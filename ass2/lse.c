#include <stdio.h>
#include <stdlib.h>
#include <mpi.h>
#include <pthread.h>
#include <assert.h>

//For random?
#include <time.h>

#define N_SENIORS 3

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

// Constants
#define NO_TALKING      255

void senior(int id, int nSeniors) {
    int state;         // My current state
    int recvMsg;       // Message recieved on a channel
    int talkTo;        // Process being talked to
    int *notFin = malloc(sizeof(int) * nSeniors);  // Records if the seniors are done
    int i;             // Counter
    int notDoneCount;  // Counter for notDone
    int die;           // Represents if this Senior should die
    int sendMsg;       // Message to send
    MPI_Status stat;   //Status of received message
    int *connections = malloc(sizeof(int) * nSeniors); // Record of connections

    // Initialise, state, connections and death
    state = ST_NOTHING;
    i = 0;

    printf("Senior %d started, number of seniors is %d\n", id, nSeniors);

    //Receive connections data structure
    MPI_Recv(connections, nSeniors, MPI_INT, 0, 1, MPI_COMM_WORLD, &stat);

    printf("Senior %d received connections: %d %d %d\n", id, connections[0], connections[1], connections[2]);
    
    //Initialise connections. If not connected, consider the connection finished.
    for (i = 0; i != nSeniors; i++) {
        printf("Senior %d setting up notFin for %d\n", id, i);
        if (connections[i] == 1) {
            notFin[i] = 1;
        } else {
            notFin[i] = 0;
        }
    }

    //Determine whether or not we will die
    //return rand() % (nDancers);
    die = 0; //Ignore death for now

    //Loop to send messages to define who will be talking to each other
    while (state != ST_TALK && state != ST_MOMENT && state != ST_DEAD) {
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
            if (notDoneCount == 0) {
                if (die == 0) {state = ST_MOMENT;}
                if (die == 1) {state = ST_DEAD;}
            } else {
                //Find a connected senior to send a request to
                for (i = 0; i != id; i++) {
                    //Death
                    if (state == ST_NOTHING && connections[i] == 1) {
                        sendMsg = MSG_REQ;
                        MPI_Send(&sendMsg, 1, MPI_INT, i, 1, MPI_COMM_WORLD); //Setting tag to 1 and using Send rather than ISend
                    }
                }
                if (state != ST_DEAD) {
                    state = ST_SENTREQ;
                }
            }
        } else if (state == ST_SENTREQ) {
            //Start reading from everyone
            for (i = 0; i < nSeniors; i++) {
                //If we're not connected, ignore
                if (connections[i] != 0 && notFin[i] != 0) {
                    MPI_Recv(&recvMsg, 1, MPI_INT, i, 1, MPI_COMM_WORLD, &stat);
                    if (state == ST_SENTREQ) {
                        if (recvMsg == MSG_REQ) {
                            if (die == 1) {
                                state = ST_DEAD;
                            } else {
                                state = ST_WAITCONF;
                                sendMsg = MSG_ACK;
                                MPI_Send(&sendMsg, 1, MPI_INT, i, 1, MPI_COMM_WORLD);
                                talkTo = i;
                            }
                        //Someone has acknowledged our request
                        } else if (recvMsg == MSG_ACK) {
                            if (die == 1) {
                                state = ST_DEAD;
                            } else {
                                state = ST_TALK;
                                sendMsg = MSG_CONF;
                                MPI_Send(&sendMsg, 1, MPI_INT, i, 1, MPI_COMM_WORLD);
                                talkTo = i;
                            }
                        //The connected senior has already finished
                        } else if (recvMsg == MSG_FIN) {
                            notFin[i] = 0;
                        }
                    //We are no longer in SENTREQ, decline everything that needs a response
                    } else {
                        if (recvMsg == MSG_REQ || recvMsg == MSG_ACK) {
                            sendMsg = MSG_DECL;
                            MPI_Send(&sendMsg, 1, MPI_INT, i, 1, MPI_COMM_WORLD);
                        } else if (recvMsg == MSG_FIN) {
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
            MPI_Recv(&recvMsg, 1, MPI_INT, talkTo, 1, MPI_COMM_WORLD, &stat);
            if (recvMsg == MSG_CONF) {
                state = ST_TALK;
            } else {
                state = ST_NOTHING;
                if (recvMsg == MSG_FIN) {
                    notFin[talkTo] = 0;
                }
            }
        } else {
            assert(0);
        }
    }

    printf("%d: Terminated find person to talk to loop\n", id);

    assert(state == ST_TALK || state == ST_MOMENT || state == ST_DEAD);
    assert(state == ST_TALK || state == ST_DEAD || talkTo == NO_TALKING);
    assert(state == ST_MOMENT || state == ST_DEAD || talkTo < nSeniors);
    assert(state == ST_TALK || state == ST_MOMENT || (die == 1 && state == ST_DEAD));

    if (state == ST_TALK) {
        printf("%d: Talking to: %d\n", id, talkTo);

        for (i = 0; i != nSeniors; i++) {
            if (i != id) {
                sendMsg = MSG_FIN;
                MPI_Send(&sendMsg, 1, MPI_INT, i, 1, MPI_COMM_WORLD);
            }
        }
    } else if (state = ST_DEAD) {
        printf("%d: Dead\n", id);

        for (i = 0; i != nSeniors; i++) {
            if (i != id) {
                sendMsg = MSG_FIN;
                MPI_Send(&sendMsg, 1, MPI_INT, i, 1, MPI_COMM_WORLD);
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

    int connections0[3] = {0,1,1};
    int connections1[3] = {1,0,1};
    int connections2[3] = {1,1,0};

    printf("Initialiser attempting to send connections\n");
    MPI_Send(&connections2, 3, MPI_INT, 2, 1, MPI_COMM_WORLD);
    MPI_Send(&connections1, 3, MPI_INT, 1, 1, MPI_COMM_WORLD);
    MPI_Send(&connections0, 3, MPI_INT, 0, 1, MPI_COMM_WORLD);
    printf("Initialiser successfully sent connections\n");
}

//Takes the input data file and starts up the other processes
int main (int argc, char *argv[]) {
    int id;
    int nSeniors;

    MPI_Init(&argc, &argv);
    MPI_Comm_rank(MPI_COMM_WORLD, &id);
    MPI_Comm_size(MPI_COMM_WORLD, &nSeniors);

    printf("Initialised senior with ID %d, number of seniors %d\n", id, nSeniors);

    if (id == 0) {
        printf("Setting up spawn for initialiser thread\n");

        pthread_attr_t attr;
        pthread_attr_init(&attr);
        pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);

        // Spawn audience threads
        pthread_t initialiserThread;
        int rc;

        printf("Attempting to spawn initialiser thread\n");

        //printf("Got connections file: %s", argv[1]);
        rc = pthread_create(&initialiserThread, &attr, initialiser, (void *)argv[1]);
        if (rc) {
            printf("***** Could not create thread. Return code from pthread_create() is: %d\n", rc);
            exit(-1);
        }
    }

    senior(id, nSeniors);

    MPI_Finalize();
}
