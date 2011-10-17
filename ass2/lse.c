#include <stdio.h>
#include <stdlib.h>
#include <mpi.h>
#include <pthread.h>
#include <assert.h>

//For random?
#include <time.h>

// States
#define ST_NOTHING      0
#define ST_SENTREQ      1
#define ST_WAITCONF     2
#define ST_TALK         3
#define ST_MOMENT       4

// Messages
#define MSG_REQ         0
#define MSG_ACK         1
#define MSG_CONF        2
#define MSG_DECL        3
#define MSG_FIN         4
#define MSG_TIMEOUT     5

// Constants
#define NO_TALKING      255
#define FILE_BUFFER_LENGTH 1024
#define EVEN_DEATH_PROB 0.5
#define TIMEOUT_INTERVAL (0.1 * 1000000)
#define TIMEOUT_TIME (2.0 * 1000000)

int *recvMsgs;
//int sendWithTimeout(int id, int dest, int sendMsg) {
//    float time = 0.0;
//    int retVal = 0;
//    int flag = 0;
//
//    printf("%d waiting for %d to accept\n", id, dest);
//
//    while (1) {
//        usleep(TIMEOUT_INTERVAL);
//        MPI_Test(&request, &flag, MPI_STATUS_IGNORE);
//        if (flag) {
//            break;
//        } else if (time >= TIMEOUT_TIME) {
//            MPI_Cancel(&request);
//            retVal = 1;
//            break;
//        } else {
//            time += TIMEOUT_INTERVAL;
//        }
//    }
//
//    return retVal;
//}

void *receiveWithTimeout(void *src) {
    float time = 0.0;
    int recvMsg = 0;
    MPI_Request request;
    int flag = 0;

    MPI_Irecv(&recvMsgs[(int)src], 1, MPI_INT, (int)src, 1, MPI_COMM_WORLD, &request);
    printf("Waiting to receive from %d\n", src);

    while (1) {
        usleep(TIMEOUT_INTERVAL);
        MPI_Test(&request, &flag, MPI_STATUS_IGNORE);
        if (flag) {
            break;
        } else if (time >= TIMEOUT_TIME) {
            printf("Believe %d is dead\n", (int)src);
            MPI_Cancel(&request);
            recvMsgs[(int)src] = MSG_TIMEOUT;
            break;
        } else {
            time += TIMEOUT_INTERVAL;
        }
    }
}

void senior(int id, int nSeniors, double deathProb) {
    int state;         // My current state
    int talkTo;        // Process being talked to
    int *notFin = malloc(sizeof(int) * nSeniors);  // Records if the seniors are done
    int i;             // Counter
    int notDoneCount;  // Counter for notDone
    int mayDie;         //Represents if this senior may die based upon the input file
    int die;           // Represents if this Senior should die
    int sendMsg;       // Message to send
    int *connections = malloc(sizeof(int) * nSeniors); // Record of connections
    MPI_Request request;

    //Receiving messages threads variables
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);
    pthread_t *recvThreads = malloc(sizeof(pthread_t) * nSeniors);
    recvMsgs = malloc(sizeof(int) * nSeniors);       
    void *status;

    int rc;

    // Initialise, state, connections and death
    printf("Senior %d started, number of seniors is %d\n", id, nSeniors);

    //Receive connections data structure
    MPI_Recv(connections, nSeniors, MPI_INT, 0, 1, MPI_COMM_WORLD, MPI_STATUS_IGNORE);

    printf("Senior %d received connections: ", id);
    for (i = 0; i != nSeniors; i++) {
        printf("%d ", connections[i]);
    }
    printf("\n");

     //Receive die value
    MPI_Recv(&mayDie, 1, MPI_INT, 0, 1, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    printf("Senior %d has mayDie value: %d and death probability is %f\n", id, mayDie, deathProb);

    //Initialise connections. If not connected, consider the connection finished.
    for (i = 0; i != nSeniors; i++) {
        printf("Senior %d setting up notFin for %d\n", id, i);
        if (connections[i] == 1) {
            notFin[i] = 1;
        } else {
            notFin[i] = 0;
        }
    }

    //Determine whether or not we will die during the simulation
    state = ST_NOTHING;
    if (mayDie == 1 && (((float)rand() / (float)RAND_MAX) < deathProb)) {
        die = 1;
        printf("Senior %d could die\n", id);
    } else {
        die = 0;
        printf("Senior %d cannot die\n", id);
    }

    //Death does not work yet, uncomment this to disable death
    //die = 0;

    //Loop to send messages to define who will be talking to each other
    while (state != ST_TALK && state != ST_MOMENT) {
        printf("%d: State: %d\n", id, state);

        if (state == ST_NOTHING) {
            talkTo = NO_TALKING;

            //Check if others have finished deciding who to talk to
            notDoneCount = 0;
            for (i = 0; i != nSeniors; i++) {
                notDoneCount += notFin[i];
            }
            printf("%d: notDoneCount: %d\n", id, notDoneCount);
        
            //If all others are done, we must have a seniors moment, unless we are supposed to die
            //If we look at the example, it's possible for a senior to have a senior's moment even though not supposed to die
            if (notDoneCount == 0) {
                state = ST_MOMENT;
            } else {
                //Find a connected senior to send a request to
                for (i = 0; i != id; i++) {
                    if (die == 1 && (((float)rand() / (float)RAND_MAX) < EVEN_DEATH_PROB)) {
                        printf("%d just died\n", id);
                        return;
                    }
                    if (state == ST_NOTHING && connections[i] == 1) {
                        sendMsg = MSG_REQ;
                        //Do a non-blocking send
                        MPI_Isend(&sendMsg, 1, MPI_INT, i, 1, MPI_COMM_WORLD, &request);
                    }
                }
                state = ST_SENTREQ;
            }
        } else if (state == ST_SENTREQ) {
            //Spawn threads to receive from everyone
            for (i = 0; i < nSeniors; i++) {
                //If we're not connected, ignore
                if (connections[i] != 0 && notFin[i] != 0) {
                    printf("Spawning thread to receive from %d\n", i);

                    //Create new thread, pass in who we want to receive from
                    rc = pthread_create(&recvThreads[i], &attr, receiveWithTimeout, (void *)i);
                    if (rc) {
                        printf("***** Could not create thread. Return code from pthread_create() is: %d\n", rc);
                        exit(-1);
                    }
                }
            }

            //Wait until all threads are complete
            for (i = 0; i < nSeniors; i++) {
                //If we're not connected, ignore
                if (connections[i] != 0 && notFin[i] != 0) {
                    pthread_join(recvThreads[i], &status);
                    
                    printf("%d: Received message %d from %d\n", id, recvMsgs[i], i);
                }
            }

            //Go through the messages received
            //May have to shove this all into the thread
            for (i = 0; i < nSeniors; i++) {
                //If we're not connected, ignore
                if (connections[i] != 0 && notFin[i] != 0) {
                    if (recvMsgs[i] = MSG_TIMEOUT) {
                        connections[i] = 0;
                        notFin[i] = 0;
                    } else if (state == ST_SENTREQ) {
                        if (recvMsgs[i] == MSG_REQ) {
                            //We die before committing to a conversation
                            if (die == 1) {
                                return;
                            } else {
                                state = ST_WAITCONF;
                                sendMsg = MSG_ACK;
                                if (sendWithTimeout(id, i, sendMsg) == 0) {
                                    talkTo = i;
                                } else {
                                    connections[i] = 0; 
                                    notFin[i] = 0;
                                    state = ST_SENTREQ;
                                }
                            }
                        //Someone has acknowledged our request
                        } else if (recvMsgs[i] == MSG_ACK) {
                            //We die before committing to a conversation
                            if (die == 1) {
                                return;
                            } else {
                                state = ST_TALK;
                                sendMsg = MSG_CONF;
                                //Only a living person could have sent an ACK, so timeout is unnecessary
                                MPI_Send(&sendMsg, 1, MPI_INT, talkTo, 1, MPI_COMM_WORLD);
                                talkTo = i;
                            }
                        //The connected senior has already finished
                        } else if (recvMsgs[i] == MSG_FIN) {
                            notFin[i] = 0;
                        }
                    //We are no longer in SENTREQ, decline everything that needs a response
                    } else {
                        if (recvMsgs[i] == MSG_REQ || recvMsgs[i] == MSG_ACK) {
                            sendMsg = MSG_DECL;
                            if (sendWithTimeout(id, i, sendMsg) != 0) {
                                connections[i] = 0;
                                notFin[i] = 0;
                            }
                        } else if (recvMsgs[i] == MSG_FIN) {
                            notFin[i] = 0;
                        }
                    }
                }
            }

            //We are still in SENTREQ, so we didn't enter a conversation
            //return to nothing state to send again
            if (state == ST_SENTREQ) {
                state = ST_NOTHING;
            }
        } else if (state == ST_WAITCONF) {
            assert(die != 1);

            //Only a living person could have sent an ACK, so timeout is unnecessary
            MPI_Recv(&recvMsgs[i], 1, MPI_INT, talkTo, 1, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
            if (recvMsgs[i] == MSG_CONF) {
                state = ST_TALK;
            } else {
                state = ST_NOTHING;
                if (recvMsgs[i] == MSG_FIN) {
                    notFin[talkTo] = 0;
                }
            }
        } else {
            assert(0);
        }
    }

    printf("%d: Terminated find person to talk to loop\n", id);

    assert(state == ST_TALK || state == ST_MOMENT);
    assert(state == ST_TALK || talkTo == NO_TALKING);
    assert(state == ST_MOMENT || talkTo < nSeniors);
    assert(state == ST_TALK || state == ST_MOMENT);

    if (state == ST_TALK) {
        assert(die != 1);

        printf("%d: Talking to: %d\n", id, talkTo);

        for (i = 0; i != nSeniors; i++) {
            if (connections[i] == 1) {
                sendMsg = MSG_FIN;

                MPI_Isend(&sendMsg, 1, MPI_INT, i, 1, MPI_COMM_WORLD, &request);
            }
        }
    } else if (state == ST_MOMENT) {
        printf("%d: Seniors Moment\n", id);
    } else {
        assert(0);
    }
}

void *initialiser(void *filename) {
    printf("Initialiser thread started successfully\n");
    printf("File to use: %s\n", filename);

    char line[FILE_BUFFER_LENGTH];
    FILE *f = fopen(filename, "r");

    //Get number of seniors and set up structures
    printf("Successfully opened file: %s\n", filename);
    fgets(line, sizeof line, f);
    int nSeniors = atoi(line);
    int **connections = malloc(sizeof(int *) * nSeniors);
    int *deaths = malloc(sizeof(int) * nSeniors);
    printf("Got nSeniors = %d from file\n", nSeniors);

    //Send connections data
    printf("Initialiser attempting to send connections\n");
    int i = 0;
    for (i = 0; i != nSeniors; i++) {
        connections[i] = malloc(sizeof(int) * nSeniors);
        deaths[i] = 0;

        fgets(line, sizeof line, f);
        printf("Got connections line %s for id %d\n", line, i);

        int j = 0;
        for (j = 0; j != nSeniors; j++) {
            printf("Reading digit %d for %d got %d\n", j, i, line[j] - '0');
            connections[i][j] = line[j] - '0';
        }

        MPI_Send(connections[i], nSeniors, MPI_INT, i, 1, MPI_COMM_WORLD);
        printf("Initialiser successfully sent connections to %d\n", i);
    }
    printf("Initialiser successfully sent all connections\n");
    
    //Send deaths data
    int death = 0;
    while (fscanf(f, "%d", &death) != EOF) {
        printf("%d may die\n", death);
        //Buffer overflow wtf
        if (death < nSeniors) {
            deaths[death] = 1;
        }
    }
    for (i = 0; i != nSeniors; i++) {
        MPI_Send(&deaths[i], 1, MPI_INT, i, 1, MPI_COMM_WORLD);
    }
    printf("Initialiser successfully sent all deaths\n");

    fclose(f);
}

//Takes the input data file and starts up the other processes
int main (int argc, char *argv[]) {
    int id;
    int nSeniors;

    MPI_Init(&argc, &argv);
    MPI_Comm_rank(MPI_COMM_WORLD, &id);
    MPI_Comm_size(MPI_COMM_WORLD, &nSeniors);

    printf("Initialised senior with ID %d, number of seniors %d\n", id, nSeniors);

    //Seed random
    srand(time(NULL));

    if (id == 0) {
        printf("Setting up spawn for initialiser thread\n");

        pthread_attr_t attr;
        pthread_attr_init(&attr);
        pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);

        // Spawn audience threads
        pthread_t initialiserThread;
        int rc;

        printf("Attempting to spawn initialiser thread\n");

        rc = pthread_create(&initialiserThread, &attr, initialiser, (void *)argv[1]);
        if (rc) {
            printf("***** Could not create thread. Return code from pthread_create() is: %d\n", rc);
            exit(-1);
        }
    }
    senior(id, nSeniors, atof(argv[2]));

    MPI_Finalize();
}
