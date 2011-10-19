#define N_SENIORS 5

// States
#define ST_NOTHING      1
#define ST_SENTREQ      2
#define ST_WAITCONF     3
#define ST_TALK         4
#define ST_MOMENT       5
#define ST_DEAD         6

// Messages
#define MSG_REQ         0
#define MSG_ACK         1
#define MSG_CONF        2
#define MSG_DECL        3
#define MSG_FIN         4

// Nice flag for switching death
#define CAN_DIE         0

// Nice flag for switching fully connected graph
#define FULLY_CONN      0

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

// The state each process is in
byte states[N_SENIORS]

// Record of who each senior is talking to
byte talkTo[N_SENIORS]

// Keep track of processes that have/have not finished
arrayBytes notFin[N_SENIORS]

// Records if the senior should die
byte shouldDie[N_SENIORS];

// Counter for waiting for spawned threads
byte threadCounter[N_SENIORS]

// (Auxiliary) Track number of conversations (duplicated)
byte numConversations

// (Auxiliary) Track number of senior moments
byte numMoments

// (Auxiliary) Track number of dead seniors
byte numDead

proctype recvMessage(byte id; byte read) {
    byte recvMsg;       // Message recieved on a channel

    // Receive Message
    channels[read].c[id]?recvMsg;
    //printf("%d: From %d got message: %d\n", id, read, recvMsg);

    // Do next step in atomic block
    atomic {
        if
        :: states[id] == ST_SENTREQ ->
            // Process message
            if
            :: recvMsg == MSG_REQ -> 
                // If we should die, then do so before sending ack
                if
                :: shouldDie[id] == 1 -> states[id] = ST_DEAD;
                :: else ->
                    //printf("%d: waiting on conf from %d\n", id, read);
                    states[id] = ST_WAITCONF;
                    channels[id].c[read]!MSG_ACK;
                    talkTo[id] = read;
                fi;
            :: recvMsg == MSG_ACK ->
                if
                // If we should die, then do so before sending conf
                :: shouldDie[id] == 1 -> states[id] = ST_DEAD;
                :: else ->
                    states[id] = ST_TALK;
                    channels[id].c[read]!MSG_CONF;
                    talkTo[id] = read;
                fi;
            :: recvMsg == MSG_FIN -> notFin[id].b[read] = 0;
            :: else -> skip;
            fi;
        :: else ->
            // We have changed state
            //   decline anything that needs a response
            if
            :: recvMsg == MSG_REQ || recvMsg == MSG_ACK ->
                channels[id].c[read]!MSG_DECL;
            :: recvMsg == MSG_FIN -> notFin[id].b[read] = 0;
            :: else -> skip;
            fi;
        fi;
    };

    // If we are in the wait_conf state then get message
    if
    :: talkTo[id] == read ->
        if
        :: states[id] == ST_WAITCONF ->
            channels[read].c[id]?recvMsg;
            if
            :: recvMsg == MSG_CONF -> states[id] = ST_TALK;
            :: recvMsg == MSG_FIN  ->
                notFin[id].b[read] = 0;
                states[id] = ST_NOTHING;
            :: else                -> states[id] = ST_NOTHING;
            fi;
        :: else -> skip;
        fi;
    :: else -> skip;
    fi;


    // Decrement counter to say we have finished receiving
    d_step{threadCounter[id]--};
}

proctype Senior(byte id) {
    //byte state;         // My current state
    byte read;          // Index to read from
    //byte recvMsg;       // Message recieved on a channel
    //byte talkTo;        // Process being talked to
    //byte notFin[N_SENIORS];  // Records if the seniors are done
    byte i;             // Counter
    byte notDoneCount;  // Counter for notDone
    //byte die;           // Represents if this Senior should die

    // Initialise, state, connections and death
start: 
    states[id] = ST_NOTHING;
    i = 0;
    do
    :: i == N_SENIORS -> break;
    :: i <  N_SENIORS ->
        if
        :: connections[id].b[i] == 1 -> notFin[id].b[i] = 1;
        :: else                      -> notFin[id].b[i] = 0;
        fi;
        i++;
    od;
    if
    :: true         -> shouldDie[id] = 0;
    :: CAN_DIE == 1 -> shouldDie[id] = 1;
    fi;

    do
    :: states[id] == ST_TALK || states[id] == ST_MOMENT  || states[id] == ST_DEAD -> break;
    :: else ->
        printf("%d: State: %d\n", id, states[id]);

        if
        :: states[id] == ST_NOTHING ->
            // Reset talking to
            talkTo[id] = NO_TALKING;

            // Check all others done - not connected are already 0
            i = 0; notDoneCount = 0;
            do
            :: i == N_SENIORS -> break;
            :: i <  N_SENIORS ->
                notDoneCount = notDoneCount + notFin[id].b[i];
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
                :: shouldDie[id] == 0 -> states[id] = ST_MOMENT;
                :: shouldDie[id] == 1 -> states[id] = ST_DEAD;
                fi;
            :: else ->
                i = 0;
                do
                :: i >= id -> break;
                :: i <  id ->
                    // We could die before sending the message
                    if
                    :: shouldDie[id] == 1 -> states[id] = ST_DEAD;
                    :: shouldDie[id] == 1 -> skip;
                    :: shouldDie[id] == 0 -> skip;
                    fi;
                    if
                    :: states[id] == ST_NOTHING &&
                       connections[id].b[i] == 1 ->
                        //printf("%d: Sent %d request\n", id, i);
                        channels[id].c[i]!MSG_REQ;
                    :: else -> skip;
                    fi;
                    i++;
                od;
                if
                :: states[id] != ST_DEAD -> states[id] = ST_SENTREQ;
                :: else -> skip;
                fi;
            fi;

        :: states[id] == ST_SENTREQ ->
            // Do a full round of reading - that is read from each connected senior
            //  Only read from seniors we are connected to
            threadCounter[id] = 0;
            read = 0;
            do
            :: read == N_SENIORS -> break;
            :: read < N_SENIORS ->
                if
                :: connections[id].b[read] == 0 ||
                   notFin[id].b[read] == 0
                   -> skip;
                :: else -> 
                    d_step{threadCounter[id]++};
                    run recvMessage(id, read);
                fi;
                read++;
            od;
            (threadCounter[id] == 0);
            //printf("%d: Done getting requests: state: %d\n", id, states[id]);

            // If we have not changed state then we haven't entered a communication
            //   return to nothing state for another round of sending
            if
            :: states[id] == ST_SENTREQ -> states[id] = ST_NOTHING;
            :: else -> skip;
            fi;
        :: states[id] == ST_WAITCONF -> assert(false);
        fi;
    od;
    //printf("%d: Terminated Loop\n", id);

    // assert appropriate values
    assert(states[id] == ST_TALK || states[id] == ST_MOMENT || states[id] == ST_DEAD);
    assert(states[id] == ST_TALK || states[id] == ST_DEAD || talkTo[id] == NO_TALKING);
    assert(states[id] == ST_MOMENT || states[id] == ST_DEAD || talkTo[id] < N_SENIORS);
    assert(states[id] == ST_TALK || states[id] == ST_MOMENT || (shouldDie[id] == 1 && states[id] == ST_DEAD));

    // Do finishing state tasks
    if
    :: states[id] == ST_TALK ->
        printf("***** %d: Talking to: %d\n", id, talkTo[id]);
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
    :: states[id] == ST_DEAD ->
        printf("***** %d: Dead\n", id);
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
    :: states[id] == ST_MOMENT ->
        d_step{numMoments++};
        printf("***** %d: Seniors Moment\n", id);
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
                :: FULLY_CONN == 0 ->
                    connections[i].b[j] = 0;
                    connections[j].b[i] = 0;
                :: true            ->
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

