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

    printf("Connections: %p, notFind: %p\n", connections, notFin);

    //Receive connections data structure
    MPI_Recv(&connections, nSeniors, MPI_INT, 0, 1, MPI_COMM_WORLD, &stat);

    printf("Connections: %p, notFind: %p\n", connections, notFin);

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
            for (i = 0; i != nSeniors; i++) {
                notDoneCount += notFin[i];
            }
        
            //If all others are done, we must have a seniors moment, unless we are supposed to die
            if (notDoneCount == 0) {
                if (die == 0) {state = ST_MOMENT;}
                if (die == 1) {state = ST_DEAD;}
            } else {
                //Find a connected senior to send a request to
                for (i = 0; i != id; i++) {
                    //Random numbers
                    if (state == ST_TALK && connections[i] == 1) {
                        sendMsg = MSG_REQ;
                        MPI_Send(&sendMsg, 1, MPI_INT, i, 1, MPI_COMM_WORLD); //Setting tag to 1 and using Send rather than ISend
                        state = ST_SENTREQ;
                    }
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
                            notFin[i] == 0;
                        }
                    //We are no longer in SENTREQ, decline everything that needs a response
                    } else {
                        if (recvMsg == MSG_REQ || recvMsg == MSG_ACK) {
                            sendMsg = MSG_DECL;
                            MPI_Send(&sendMsg, 1, MPI_INT, i, 1, MPI_COMM_WORLD);
                        } else if (recvMsg == MSG_FIN) {
                            notFin[i] == 0;
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

    int connections[3] = {1,1,1};

    printf("Initialiser attempting to send connections\n");
    MPI_Send(&connections, 3, MPI_INT, 2, 1, MPI_COMM_WORLD);
    MPI_Send(&connections, 3, MPI_INT, 1, 1, MPI_COMM_WORLD);
    MPI_Send(&connections, 3, MPI_INT, 0, 1, MPI_COMM_WORLD);
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

//init {
//    atomic {
//        byte i;
//        byte j;
//
//        // Set auxiliary variables
//        numConversations = 0;
//        numMoments = 0;
//        numDead = 0;
//
//        // Create connections
//        i = 0; j = 0;
//        do
//        :: i == N_SENIORS -> break;
//        :: i != N_SENIORS ->
//            j = i;
//            connections[i].b[j] = 0;
//            printf("Connections[%d][%d] = %d\n", i, j, 0);
//            j++;
//            do
//            :: j == N_SENIORS -> break;
//            :: j != N_SENIORS ->
//                if
//                :: true ->
//                    connections[i].b[j] = 0;
//                    connections[j].b[i] = 0;
//                :: true ->
//                    connections[i].b[j] = 1;
//                    connections[j].b[i] = 1;
//                fi;
//                printf("Connections[%d][%d] = %d\n", i, j, connections[i].b[j]);
//                j++;
//            od;
//            i++;
//        od;
//
//        // Spawn processes
//        i = 0;
//        do
//        :: i == N_SENIORS -> break;
//        :: i != N_SENIORS ->
//            run Senior(i);
//            i++;
//        od;
//    }
//}

//    do
//    :: state == ST_TALK || state == ST_MOMENT  || state == ST_DEAD -> break;
//    :: else ->
//        printf("%d: State: %d\n", id, state);
//
//        if
//        :: state == ST_NOTHING ->
//            // If all else are done, then have seniors moment
//            // Else send messages and continue
//            //   Only send messages to seniors we are connected to
//            //   We may die before sending a request message
//            if
//            :: notDoneCount == 0 ->
//                // If we are supposed to die then die rather than have moment
//                if
//                :: die == 0 -> state = ST_MOMENT;
//                :: die == 1 -> state = ST_DEAD;
//                fi;
//            :: else ->
//                i = 0;
//                do
//                :: i >= id -> break;
//                :: i <  id ->
//                    // We could die before sending the message
//                    if
//                    :: die == 1 -> state = ST_DEAD;
//                    :: die == 1 -> skip;
//                    :: die == 0 -> skip;
//                    fi;
//                    if
//                    :: state == ST_TALK &&
//                       connections[id].b[i] == 1 ->
//                        channels[id].c[i]!MSG_REQ;
//                        state = ST_SENTREQ;
//                    :: else -> skip;
//                    fi;
//                    i++;
//                od;
//            fi;
//
//        :: state == ST_SENTREQ ->
//            // Do a full round of reading - that is read from each connected senior
//            //  Only read from seniors we are connected to
//            read = 0;
//            do
//            :: read == N_SENIORS -> break;
//            :: read < N_SENIORS ->
//                if
//                :: connections[id].b[read] == 0 ||
//                   notFin[read] == 0
//                   -> skip;
//                :: else -> 
//                    channels[read].c[id]?recvMsg;
//                    if
//                    :: state == ST_SENTREQ ->
//                        // We are happy to stay recieve Requests/Ack's
//                        // But, we should die before sending conf/ack
//                        if
//                        :: recvMsg == MSG_REQ -> 
//                            if
//                            :: die == 1 -> state = ST_DEAD;
//                            :: else ->
//                                state = ST_WAITCONF;
//                                channels[id].c[read]!MSG_ACK;
//                                talkTo = read;
//                            fi;
//                        :: recvMsg == MSG_ACK ->
//                            if
//                            :: die == 1 -> state = ST_DEAD;
//                            :: else ->
//                                state = ST_TALK;
//                                channels[id].c[read]!MSG_CONF;
//                                talkTo = read;
//                            fi;
//                        :: recvMsg == MSG_FIN -> notFin[read] = 0;
//                        :: else -> skip;
//                        fi;
//                    :: else -> 
//                        // We have changed state
//                        //   decline anything that needs a response
//                        if
//                        :: recvMsg == MSG_REQ || recvMsg == MSG_ACK ->
//                            channels[id].c[read]!MSG_DECL;
//                        :: recvMsg == MSG_FIN -> notFin[read] = 0;
//                        :: else -> skip;
//                        fi;
//                    fi;
//                fi;
//                read++;
//            od;
//
//            // If we have not changed state then we haven't entered a communication
//            //   return to nothing state for another round of sending
//            if
//            :: state == ST_SENTREQ -> state = ST_NOTHING;
//            :: else -> skip;
//            fi;
//        :: state == ST_WAITCONF ->
//            // Wait on the senior we sent an ACK to
//            channels[talkTo].c[id]?recvMsg;
//            if
//            :: recvMsg == MSG_CONF -> state = ST_TALK;
//            :: else                ->
//                state = ST_NOTHING;
//                if
//                :: recvMsg == MSG_FIN  -> notFin[talkTo] = 0;
//                :: else                -> skip;
//                fi;
//            fi;
//        fi;
//    od;
//    printf("%d: Terminated Loop\n", id);
//
//    // assert appropriate values
//    assert(state == ST_TALK || state == ST_MOMENT || state == ST_DEAD);
//    assert(state == ST_TALK || state == ST_DEAD || talkTo == NO_TALKING);
//    assert(state == ST_MOMENT || state == ST_DEAD || talkTo < N_SENIORS);
//    assert(state == ST_TALK || state == ST_MOMENT || (die == 1 && state == ST_DEAD));
//
//    // Do finishing state tasks
//    if
//    :: state == ST_TALK ->
//        printf("%d: Talking to: %d\n", id, talkTo);
//        d_step{numConversations++};
//        i = 0;
//        do
//        :: i == N_SENIORS -> break;
//        :: i <  N_SENIORS ->
//            if
//            :: i != id -> channels[id].c[i]!MSG_FIN;
//            :: else -> skip;
//            fi;
//            i++;
//        od;
//    :: state == ST_DEAD ->
//        printf("%d: Dead\n", id);
//        d_step{numDead++};
//        i = 0;
//        do
//        :: i == N_SENIORS -> break;
//        :: i <  N_SENIORS ->
//            if
//            :: i != id -> channels[id].c[i]!MSG_FIN;
//            :: else -> skip;
//            fi;
//            i++;
//        od;
//    :: state == ST_MOMENT ->
//        d_step{numMoments++};
//        printf("%d: Seniors Moment\n", id);
//    fi;
//
//    // For termination
//terminate:
//    skip;
//}
