#include <stdio.h>
#include <stdlib.h>
#include <mpi.h>
#include <pthread.h>
#include <assert.h>
#include <unistd.h>

//For random?
#include <time.h>

// States
#define ST_NOTHING      0
#define ST_SENTREQ      1
#define ST_WAITCONF     2
#define ST_TALK         3
#define ST_MOMENT       4
#define ST_DEAD         5

// Messages
#define MSG_REQ         0
#define MSG_ACK         1
#define MSG_CONF        2
#define MSG_DECL        3
#define MSG_FIN         4
#define MSG_TIMEOUT     5

// Constants
#define SEC2USEC(n) (n * 1000000)
#define NO_TALKING              255
#define PROB_SHIF               100
#define FILE_BUFFER_LENGTH      1024
#define EVEN_DEATH_PROB         0.5
#define TIMEOUT_INTERVAL        SEC2USEC(0.1)
#define TIMEOUT_TIME            SEC2USEC(2.0)

#define LOG printf

// Global values

// Id of this senior
int id;

// Total number of seniors
int nSeniors;

// All the seniors I am connected to
int *connections;

// Current state of this senior
int state;

//Represents if this senior may die based upon the input file
int mayDie;

// Represents if this Senior should die
int die;

// Process being talked to
int talkTo;

// Records if the seniors are done
int *notFin;

// Mutex for maintaining locks on processing recieved message
pthread_mutex_t recvProcessMutex = PTHREAD_MUTEX_INITIALIZER;

int receiveWithTimeout(int read) {
    float time = 0.0;
    int recvMsg = 0;
    int flag = 0;
    MPI_Request request;

    MPI_Irecv(&recvMsg, 1, MPI_INT, read, read, MPI_COMM_WORLD, &request);
    //LOG("%d: Waiting to receive from %d\n", id, read);

    while (1) {
        usleep(TIMEOUT_INTERVAL);
        MPI_Test(&request, &flag, MPI_STATUS_IGNORE);
        if (flag) {
            // Got valid message
            break;
        } else if (time >= TIMEOUT_TIME) {
            // Have timed-out
            MPI_Cancel(&request);

            //LOG("Believe %d is dead\n", read);
            recvMsg = MSG_FIN;

            break;
        } else {
            // Wait longer
            time += TIMEOUT_INTERVAL;
        }
    }

    return recvMsg;
}

void *receiveFromAll(void *src) {
    int read = (int) src;
    int recvMsg = 0;
    int sendMsg = 0;
    //MPI_Request request;
    //MPI_Status status;

    // Receive Message
    //LOG("%d: Receiving message from %d\n", id, read);
    recvMsg = receiveWithTimeout(read);

    // Lock for processing received message
    //LOG("%d: Waiting on lock\n", id);
    pthread_mutex_lock(&recvProcessMutex);
        //LOG("%d: lock\n", id);
        //LOG("\t%d: Got message: %d (from %d)\n", id, recvMsg, read);
        //LOG("\t%d: State: %d\n", id, state);

        if (state == ST_SENTREQ) {
            // Process message
            if (recvMsg == MSG_REQ) {
                if (die) {
                    // If we should die, then die
                    //LOG("***** %d: dieing\n", id);
                    state = ST_DEAD;
                } else {
                    //LOG("\t%d: Entering wait conf: %d\n", id, read);
                    state = ST_WAITCONF;
                    talkTo = read;
                    sendMsg = MSG_ACK;
                    MPI_Send(&sendMsg, 1, MPI_INT, read, id, MPI_COMM_WORLD);
                }
            } else if (recvMsg == MSG_ACK) {
                if (die) {
                    // If we should die, then die
                    //LOG("***** %d: dieing\n", id);
                    state = ST_DEAD;
                } else {
                    //LOG("\t%d: Entering talk: %d\n", id, read);
                    state = ST_TALK;
                    talkTo = read;
                    sendMsg = MSG_CONF;
                    MPI_Send(&sendMsg, 1, MPI_INT, read, id, MPI_COMM_WORLD);
                }
            } else if (recvMsg == MSG_FIN) {
                //LOG("\t%d: Got fin from: %d\n", id, read);
                notFin[read] = 0;
            }
        } else {
            // We have changed state - decline anything that needs a response
            if (recvMsg == MSG_REQ || recvMsg == MSG_ACK) {
                //LOG("\t%d: Sending decline to: %d\n", id, read);
                sendMsg = MSG_DECL;
                MPI_Send(&sendMsg, 1, MPI_INT, read, id, MPI_COMM_WORLD);
            } else if (recvMsg == MSG_FIN) {
                //LOG("\t%d: Got fin from: %d\n", id, read);
                notFin[read] = 0;
            }
        }

    // Unlock for processing received message
    //LOG("%d: unlock\n", id);
    pthread_mutex_unlock(&recvProcessMutex);

    // If we are in the wait_conf state then get a message
    if (talkTo == read) {
        if (state == ST_WAITCONF) {
            //LOG("%d: in Waiting conf from: %d\n", id, read);
            //MPI_Recv(&recvMsg, 1, MPI_INT, talkTo, talkTo, MPI_COMM_WORLD, &status);
            recvMsg = receiveWithTimeout(talkTo);
            //LOG("%d: WatiConf Got message: %d (from %d)\n", id, recvMsg, read);

            if (recvMsg == MSG_CONF) {
                state = ST_TALK;
            } else if (recvMsg == MSG_FIN) {
                notFin[talkTo] = 0;
                state = ST_NOTHING;
            } else {
                state = ST_NOTHING;
            }
        }
    }


    return NULL;
}

void senior(double deathProb) {
    int i;              // Counter
    int read;
    int notDoneCount;   // Counter for notDone
    int sendMsg;        // Message to send
    //MPI_Request request;
    //MPI_Status  status;
    
    //LOG("%d: started, number of seniors is %d\n", id, nSeniors);

    // Setup variables
    notFin = malloc(sizeof(int) * nSeniors);


    //Receiving messages threads variables
    int rc;
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);
    pthread_t *recvThreads = malloc(sizeof(pthread_t) * nSeniors);

    // Initialise notFin & numTimeouts
    for (i = 0; i != nSeniors; i++) {
        ////LOG("%d: setting up notFin for %d\n", id, i);
        if (connections[i] == 1) {
            notFin[i] = 1;
        } else {
            notFin[i] = 0;
        }
    }

    //Determine whether or not we will die during the simulation
    state = ST_NOTHING;
    float dieRoll;
    for(i = -1; i != id; i++) dieRoll = rand() % 100;
    //LOG("%d: dieRoll: %f\n", id, dieRoll);
    if (mayDie == 1 && dieRoll < (deathProb * 100)) {
        die = 1;
    } else {
        die = 0;
    }
    //LOG("%d: Die: %d\n", id, die);

    //Loop to send messages to define who will be talking to each other
    while (state != ST_TALK && state != ST_MOMENT && state != ST_DEAD) {
        //LOG("%d: State: %d\n", id, state);

        if (state == ST_NOTHING) {
            talkTo = NO_TALKING;

            //Check if others have finished deciding who to talk to
            notDoneCount = 0;
            for (i = 0; i != nSeniors; i++) {
                notDoneCount += notFin[i];
            }
            //LOG("%d: notDoneCount: %d\n", id, notDoneCount);
        
            //If all others are done, we must have a seniors moment, unless we are supposed to die
            //If we look at the example, it's possible for a senior to have a senior's moment even though not supposed to die
            if (notDoneCount == 0) {
                state = (die == 1) ? ST_DEAD : ST_MOMENT;
            } else {
                //Find a connected senior to send a request to
                for (i = 0; i != id; i++) {
                    if (die == 1 && (((float)rand() / (float)RAND_MAX) < EVEN_DEATH_PROB)) {
                        //LOG("%d: just died\n", id);
                        state = ST_DEAD;
                        //return;
                    }
                    if (state == ST_NOTHING && connections[i] == 1) {
                        sendMsg = MSG_REQ;

                        //Do a non-blocking send
                        MPI_Send(&sendMsg, 1, MPI_INT, i, id, MPI_COMM_WORLD);
                    }
                }
                if (state != ST_DEAD) {
                    state = ST_SENTREQ;
                }
            }
        } else if (state == ST_SENTREQ) {
            for (read = 0; read < nSeniors; read++) {
                //If we're not connected, ignore
                if (connections[read] != 0 && notFin[read] != 0) {
                    ////LOG("Spawning thread to receive from %d\n", i);

                    //Create new thread, pass in who we want to receive from
                    rc = pthread_create(&recvThreads[read], &attr, receiveFromAll, (void *)read);
                    if (rc) {
                        //LOG("##### Could not create thread. Return code from pthread_create() is: %d\n", rc);
                        exit(-1);
                    }
                }
            }

            //Wait until all threads are complete
            void *joinStatus;
            for (i = 0; i < nSeniors; i++) {
                //If we're not connected, ignore
                if (connections[i] != 0 && notFin[i] != 0) {
                    pthread_join(recvThreads[i], &joinStatus);
                }
            }
            //LOG("%d: All messages recieved\n", id);

            //We are still in SENTREQ, so we didn't enter a conversation
            //return to nothing state to send again
            if (state == ST_SENTREQ) {
                state = ST_NOTHING;
            }
        } else if (state == ST_WAITCONF) {
            assert(die != 1);
            assert(0);


        } else {
            assert(0);
        }
    }

    //LOG("%d: Terminated find person to talk to loop\n", id);

    //assert(state == ST_TALK || state == ST_MOMENT);
    //assert(state == ST_TALK || talkTo == NO_TALKING);
    //assert(state == ST_MOMENT || talkTo < nSeniors);
    //assert(state == ST_TALK || state == ST_MOMENT);

    if (state == ST_TALK) {
        assert(die != 1);

        //LOG("***** %d: Talking to: %d\n", id, talkTo);
        printf("%d exchanges life stories with %d.\n", id + 1, talkTo + 1);

        // TODO FIX!
        for (i = 0; i != nSeniors; i++) {
            if (connections[i] == 1) {
                ////LOG("%d: Sending %d\n", id, i);
                sendMsg = MSG_FIN;
                MPI_Send(&sendMsg, 1, MPI_INT, i, id, MPI_COMM_WORLD);
                ////LOG("%d: done send: %d\n", id, i);
            }
        }
    } else if (state == ST_MOMENT) {
        //LOG("***** %d: Seniors Moment\n", id);
        printf("%d has a seniors' moment.\n", id + 1);
    } else if (state == ST_DEAD) {
        //LOG("***** %d: Senior Died\n", id);
        printf("%d dies blaming the zabaglione.\n", id + 1);
    } else {
        assert(0);
    }

}

// Setup the data for the seniors
void initialise(int id, void* filename) {
    connections = malloc(sizeof(int) * nSeniors);

    // Senior 0 sends out data & other receive
    if (id == 0) {
        //LOG("Initialiser starting\n");
        //LOG("File to use: %s\n", filename);

        char line[FILE_BUFFER_LENGTH];
        FILE *f = fopen(filename, "r");

        //Get number of seniors and set up structures
        //LOG("Successfully opened file: %s\n", filename);
        fgets(line, sizeof line, f);
        assert(atoi(line) == nSeniors);
        int nSeniors = atoi(line);
        //LOG("Got nSeniors = %d from file\n", nSeniors);

        //Send connections data
        //LOG("Sending information to others\n");
        int senior = 0;
        for (senior = 0; senior != nSeniors; senior++) {
            fgets(line, sizeof line, f);
            //LOG("Got connections line %s for id %d\n", line, senior);

            int j = 0;
            for (j = 0; j != nSeniors; j++) {
                //LOG("Reading digit %d for %d got %d\n", j, senior, line[j] - '0');
                int conn = line[j] - '0';
                if (senior == 0) {
                    connections[j] = conn;
                } else {
                    MPI_Send(&conn, 1, MPI_INT, senior, 0, MPI_COMM_WORLD);
                }
            }

        }
        //LOG("Successfully sent all connections\n");

        // Send death information
        //LOG("Collecting death information\n");
        int *deaths = malloc(sizeof(int) * nSeniors);
        for (senior = 0; senior != nSeniors; senior++) deaths[senior] = 0;
        int toDie;
        while (fscanf(f, "%d", &toDie) != EOF) {
            //LOG("%d: Got die value: %d\n", id, toDie);
            deaths[toDie - 1] = 1;
        }
        for (senior = 0; senior != nSeniors; senior++) {
            if (senior == 0) {
                //LOG("%d: Saving my own death\n", id);
                mayDie = deaths[senior];
            } else {
                //LOG("%d: Sending death to %d\n", id, senior);
                MPI_Send(&deaths[senior], 1, MPI_INT, senior, 0, MPI_COMM_WORLD);
            }
        }

        // Cleanup
        free(deaths);
        fclose(f);
 
    } else {
        // Get my connections first
        int i = 0;
        int recvMsg;
        MPI_Status status;

        //LOG("%d: Receiving connections\n", id);
        for (i = 0; i != nSeniors; i++) {
            MPI_Recv(&recvMsg, 1, MPI_INT, 0, 0, MPI_COMM_WORLD, &status);
            //LOG("%d: Got conn: %d\n", id, recvMsg);
            connections[i] = recvMsg;
        }

        // Get may die information
        //LOG("%d: Waiting on death value\n", id);
        MPI_Recv(&mayDie, 1, MPI_INT, 0, 0, MPI_COMM_WORLD, &status);
        //LOG("%d: May Die: %d\n", id, mayDie);
    }

}

//Takes the input data file and starts up the other processes
int main (int argc, char *argv[]) {

    MPI_Init(&argc, &argv);
    MPI_Comm_rank(MPI_COMM_WORLD, &id);
    MPI_Comm_size(MPI_COMM_WORLD, &nSeniors);

    //LOG("Initialised senior with ID %d, number of seniors %d\n", id, nSeniors);
    if (argc != 3) {
        printf("Usage: lse <test file> <death prob>\n");
        return 0;
    }

    //Seed random
    srand(time(NULL));

    // Setup information
    initialise(id, argv[1]);

    // Execute senior
    senior(atof(argv[2]));
    //LOG("%d: Senior done\n", id);

    // Finish
    MPI_Finalize();
    return 0;
}
