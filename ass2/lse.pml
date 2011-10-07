
#define N_SENIORS 4

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

// Struct to give multi-dimensional arrays
typedef arrayChannels {
    chan c[N_SENIORS] = [5] of {byte}
};

// Channels
arrayChannels channels[N_SENIORS]

proctype senior(byte id) {
    byte state;         // My current state
    byte reqSent;       // Person who I have sent message to
    byte read;          // Index to read from
    byte recvMsg;       // Message recieved on a channel
    byte talkTo;        // Process being talked to
    byte notFin[N_SENIORS];  // Records if the seniors are done
    byte i;             // Counter

    state = ST_NOTHING;
    reqSent = 0;
    do
    :: reqSent == N_SENIORS -> break;
    :: reqSent <  N_SENIORS ->
        if
        :: reqSent != id -> notFin[reqSent] = 1;
        :: else          -> notFin[reqSent] = 0;
        fi;
        reqSent++;
    od;

    do
    :: state == ST_TALK || state == ST_MOMENT -> break;
    :: else ->
        printf("%d: State: %d\n", id, state);

        if
        :: state == ST_NOTHING ->
            // Check all others done
            reqSent = 0;
            i = 0;
            do
            :: reqSent == N_SENIORS -> break;
            :: reqSent <  N_SENIORS ->
                i = i + notFin[reqSent];
                reqSent++;
            od;

            // If all else are done, then have seniors moment
            // Else send messages and continue
            if
            :: i == 0 -> state = ST_MOMENT;
            :: else ->
                reqSent = 0;
                do
                :: reqSent >= id -> break;
                :: reqSent <  id ->
                    channels[id].c[reqSent]!MSG_REQ;
                    reqSent++;
                od;
                state = ST_SENTREQ;
            fi;

        :: state == ST_SENTREQ ->
            read = 0;
            do
            :: read == N_SENIORS -> break;
            :: read < N_SENIORS ->
                if
                :: read == id -> skip;
                :: else -> 
                    channels[read].c[id]?recvMsg;
                    if
                    :: state == ST_SENTREQ ->
                        if
                        :: recvMsg == MSG_REQ -> 
                            state = ST_WAITCONF;
                            channels[id].c[read]!MSG_ACK;
                            talkTo = read;
                        :: recvMsg == MSG_ACK ->
                            state = ST_TALK;
                            channels[id].c[read]!MSG_CONF;
                            talkTo = read;
                        :: recvMsg == MSG_FIN -> notFin[read] = 0;
                        :: else -> skip;
                        fi;
                    :: else -> 
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
            if
            :: state == ST_SENTREQ -> state = ST_NOTHING;
            :: else -> skip;
            fi;
        :: state == ST_WAITCONF ->
            channels[talkTo].c[id]?recvMsg;
            if
            :: recvMsg == MSG_CONF -> state = ST_TALK;
            :: recvMsg == MSG_FIN  -> notFin[talkTo] = 0;
            :: else                -> state = ST_NOTHING;
            fi;
        fi;
    od;
    printf("%d: Terminated Loop\n", id);

    if
    :: state == ST_TALK ->
        printf("%d: Talking to: %d\n", id, talkTo);
        reqSent = 0;
        do
        :: reqSent == N_SENIORS -> break;
        :: reqSent <  N_SENIORS ->
            if
            :: reqSent != id -> channels[id].c[reqSent]!MSG_FIN;
            :: else -> skip;
            fi;
            reqSent++;
        od;
    :: state == ST_MOMENT -> printf("%d: Seniors Moment\n", id);
    :: else -> assert(0);
    fi;
}

init {
    atomic {
        //run senior(0);
        //run senior(1);
        //run senior(2);
        //run senior(3);
        byte i;
        i = 0;
        do
        :: i == N_SENIORS -> break;
        :: i != N_SENIORS ->
            run senior(i);
            i++;
        od;
    }
}
