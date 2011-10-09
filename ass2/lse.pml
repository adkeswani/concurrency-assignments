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

// Struct to give multi-dimensional arrays
typedef arrayChannels {
    chan c[N_SENIORS] = [5] of {byte}
};
typedef arrayBytes {
    byte b[N_SENIORS]
};

// Channels
arrayChannels channels[N_SENIORS]

// Record of connections
arrayBytes connections[N_SENIORS]

// (Auxiliary) Track number of conversations (duplicated)
byte numConversations

// (Auxiliary) Track number of senior moments
byte numMoments

// (Auxiliary) Track number of dead seniors
byte numDead

proctype Senior(byte id) {
    byte state;         // My current state
    byte read;          // Index to read from
    byte recvMsg;       // Message recieved on a channel
    byte talkTo;        // Process being talked to
    byte notFin[N_SENIORS];  // Records if the seniors are done
    byte i;             // Counter
    byte notDoneCount;  // Counter for notDone
    byte die;           // Represents if this Senior should die

    // Initialise, state, connections and death
start: 
    state = ST_NOTHING;
    i = 0;
    do
    :: i == N_SENIORS -> break;
    :: i <  N_SENIORS ->
        if
        :: connections[id].b[i] == 1 -> notFin[i] = 1;
        :: else                      -> notFin[i] = 0;
        fi;
        i++;
    od;
    if
    :: true -> die = 0;
    :: true -> die = 1;
    fi;

    do
    :: state == ST_TALK || state == ST_MOMENT  || state == ST_DEAD -> break;
    :: else ->
        printf("%d: State: %d\n", id, state);

        if
        :: state == ST_NOTHING ->
            // Reset talking to
            talkTo = NO_TALKING;

            // Check all others done - not connected are already 0
            i = 0; notDoneCount = 0;
            do
            :: i == N_SENIORS -> break;
            :: i <  N_SENIORS ->
                notDoneCount = notDoneCount + notFin[i];
                i++;
            od;

            // If all else are done, then have seniors moment
            // Else send messages and continue
            //   Only send messages to seniors we are connected to
            //   We may die before sending a request message
            if
            :: notDoneCount == 0 ->
                // If we are supposed to die then die rather than have moment
                if
                :: die == 0 -> state = ST_MOMENT;
                :: die == 1 -> state = ST_DEAD;
                fi;
            :: else ->
                i = 0;
                do
                :: i >= id -> break;
                :: i <  id ->
                    // We could die before sending the message
                    if
                    :: die == 1 -> state = ST_DEAD;
                    :: die == 1 -> skip;
                    :: die == 0 -> skip;
                    fi;
                    if
                    :: state == ST_TALK &&
                       connections[id].b[i] == 1 ->
                        channels[id].c[i]!MSG_REQ;
                        state = ST_SENTREQ;
                    :: else -> skip;
                    fi;
                    i++;
                od;
            fi;

        :: state == ST_SENTREQ ->
            // Do a full round of reading - that is read from each connected senior
            //  Only read from seniors we are connected to
            read = 0;
            do
            :: read == N_SENIORS -> break;
            :: read < N_SENIORS ->
                if
                :: connections[id].b[read] == 0 ||
                   notFin[read] == 0
                   -> skip;
                :: else -> 
                    channels[read].c[id]?recvMsg;
                    if
                    :: state == ST_SENTREQ ->
                        // We are happy to stay recieve Requests/Ack's
                        // But, we should die before sending conf/ack
                        if
                        :: recvMsg == MSG_REQ -> 
                            if
                            :: die == 1 -> state = ST_DEAD;
                            :: else ->
                                state = ST_WAITCONF;
                                channels[id].c[read]!MSG_ACK;
                                talkTo = read;
                            fi;
                        :: recvMsg == MSG_ACK ->
                            if
                            :: die == 1 -> state = ST_DEAD;
                            :: else ->
                                state = ST_TALK;
                                channels[id].c[read]!MSG_CONF;
                                talkTo = read;
                            fi;
                        :: recvMsg == MSG_FIN -> notFin[read] = 0;
                        :: else -> skip;
                        fi;
                    :: else -> 
                        // We have changed state
                        //   decline anything that needs a response
                        if
                        :: recvMsg == MSG_REQ || recvMsg == MSG_ACK ->
                            channels[id].c[read]!MSG_DECL;
                        :: recvMsg == MSG_FIN -> notFin[read] = 0;
                        :: else -> skip;
                        fi;
                    fi;
                fi;
                read++;
            od;

            // If we have not changed state then we haven't entered a communication
            //   return to nothing state for another round of sending
            if
            :: state == ST_SENTREQ -> state = ST_NOTHING;
            :: else -> skip;
            fi;
        :: state == ST_WAITCONF ->
            // Wait on the senior we sent an ACK to
            channels[talkTo].c[id]?recvMsg;
            if
            :: recvMsg == MSG_CONF -> state = ST_TALK;
            :: else                ->
                state = ST_NOTHING;
                if
                :: recvMsg == MSG_FIN  -> notFin[talkTo] = 0;
                :: else                -> skip;
                fi;
            fi;
        fi;
    od;
    printf("%d: Terminated Loop\n", id);

    // assert appropriate values
    assert(state == ST_TALK || state == ST_MOMENT || state == ST_DEAD);
    assert(state == ST_TALK || state == ST_DEAD || talkTo == NO_TALKING);
    assert(state == ST_MOMENT || state == ST_DEAD || talkTo < N_SENIORS);
    assert(state == ST_TALK || state == ST_MOMENT || (die == 1 && state == ST_DEAD));

    // Do finishing state tasks
    if
    :: state == ST_TALK ->
        printf("%d: Talking to: %d\n", id, talkTo);
        d_step{numConversations++};
        i = 0;
        do
        :: i == N_SENIORS -> break;
        :: i <  N_SENIORS ->
            if
            :: i != id -> channels[id].c[i]!MSG_FIN;
            :: else -> skip;
            fi;
            i++;
        od;
    :: state == ST_DEAD ->
        printf("%d: Dead\n", id);
        d_step{numDead++};
        i = 0;
        do
        :: i == N_SENIORS -> break;
        :: i <  N_SENIORS ->
            if
            :: i != id -> channels[id].c[i]!MSG_FIN;
            :: else -> skip;
            fi;
            i++;
        od;
    :: state == ST_MOMENT ->
        d_step{numMoments++};
        printf("%d: Seniors Moment\n", id);
    fi;

    // For termination
terminate:
    skip;
}

init {
    atomic {
        byte i;
        byte j;

        // Set auxiliary variables
        numConversations = 0;
        numMoments = 0;
        numDead = 0;

        // Create connections
        i = 0; j = 0;
        do
        :: i == N_SENIORS -> break;
        :: i != N_SENIORS ->
            j = i;
            connections[i].b[j] = 0;
            printf("Connections[%d][%d] = %d\n", i, j, 0);
            j++;
            do
            :: j == N_SENIORS -> break;
            :: j != N_SENIORS ->
                if
                :: true ->
                    connections[i].b[j] = 0;
                    connections[j].b[i] = 0;
                :: true ->
                    connections[i].b[j] = 1;
                    connections[j].b[i] = 1;
                fi;
                printf("Connections[%d][%d] = %d\n", i, j, connections[i].b[j]);
                j++;
            od;
            i++;
        od;

        // Spawn processes
        i = 0;
        do
        :: i == N_SENIORS -> break;
        :: i != N_SENIORS ->
            run Senior(i);
            i++;
        od;
    }
}

// Defines for LTL's
#define pstart      Senior[0]@start
#define pfin        Senior[0]@doFinish
#define pterm       Senior[0]@terminate
#define qstart      Senior[1]@start
#define qterm       Senior[1]@terminate
#define rstart      Senior[2]@start
#define rterm       Senior[2]@terminate

// Termination
ltl term1 { [](pstart -> <>pterm) };
ltl term2 { [](qstart -> <>qterm) };
ltl term3 { [](rstart -> <>rterm) };

// Verify number of conversations is ok
ltl conv1 { []((numConversations / 2) <= (N_SENIORS / 2)) };
ltl conv2 { [](numMoments <= N_SENIORS) };
ltl conv3 { [](numDead <= N_SENIORS) };
ltl conv4 { []((numConversations / 2 + numMoments + numDead) <= N_SENIORS) };

