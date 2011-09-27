#define N_AGED      2
#define N_PRO       3
#define N_DANCERS   5
#define N_AUDIENCE  2

#define NO_DANCER -1

// Macros
#define NEXTDANCERAGED(n)   ((n+1) % N_AGED)
#define NEXTDANCERPROORAGED(n)   ((n+1) % (N_DANCERS))

//Note: atomic has to be used here as statements inside d_steps
//are not allowed to block and they don't work when you verify

// Semaphore implementation (busy-wait)
#define sem_init(S)   S = 0
#define sem_wait(S)   atomic {S > 0; S--}
#define sem_signal(S) S++

// Lock implementation
#define mutex_init(L)   L = 1
#define mutex_lock(L)   atomic {L == 1; L = 0}
#define mutex_unlock(L) L = 1

// Dancers currently on stage
short dancerAged
short dancerProOrAged

// Records if dancers are actually dancing
byte agedDancing
byte proDancing

// Dancers previously on stage
short previousAged
short previousProOrAged

// Dacer pro done
byte dancerProDone;

// Number of audience watching
byte nAudienceWatching;

// Number of audience members requesting
int validRequest[N_DANCERS]
short toWatch[N_DANCERS]

// Mutexes for changing variables associated with what audience members wish to watch
byte watchMutexes[N_DANCERS]

// Mutex for selecting the next dancer
byte selectDancerMutex

// Semaphores of audience members waiting to watch
short toWatchSemaphores[N_DANCERS]

// Semaphore for audience members watching
int nowWatchingSemaphore

// Semaphore for dancers leaving together
int leaveTogetherSemaphore

proctype runDancer(byte idx) {
    byte id;
    byte nWatchingMe;
    bool validRequestsExist;
    byte i;

    id = idx;
    nWatchingMe = 0;
    validRequestsExist = 0;
    i = 0;

    do
    :: 1 ->
        /* Lock to prevent > 2 dancers being selected */
        mutex_lock(selectDancerMutex);
            if 
            :: dancerProDone == 0 &&
               (dancerAged == NO_DANCER || dancerProOrAged == NO_DANCER) ->
                /* Check if there are any valid requests for dancers */
                validRequestsExist = 0;

                i = 0;
                do
                :: i == N_DANCERS -> break;
                :: i != N_DANCERS ->
                    if
                    :: validRequestsExist == 1 || validRequest[id] == 1 ->
                        validRequestsExist = 1;
                    :: else -> validRequestsExist = 0;
                    fi;
                    i++;
                od;

                /* This dancer can be selected if
                       there are currently no requests or
                       if this dancer has been requested
                */
                if 
                :: validRequestsExist == 0 || validRequest[id] == 1 ->
                    if 
                    :: (id != previousAged && id != previousProOrAged) ->
                        if 
                        :: (id < N_AGED && dancerAged == NO_DANCER) ->
                            dancerAged = id;
                        :: (dancerProOrAged == NO_DANCER) ->
                            /* Handle special case where there are 2 aged dancers only.
                               Prevents both dancing at same time
                            */
                            if 
                            :: (id >= N_AGED || (N_AGED > 2)) ->
                                dancerProOrAged = id;
                            :: else -> skip;
                            fi;
                        :: else -> skip
                        fi;
                    :: else -> skip;
                    fi;

                    //Regardless of whether or not the request is fulfilled, the request is no longer valid
                    validRequest[id] = 0;
                :: else -> skip;
                fi;
            :: else -> skip;
            fi;
        mutex_unlock(selectDancerMutex);

        if
        :: dancerAged == id || dancerProOrAged == id ->
            ( dancerAged != NO_DANCER && dancerProOrAged != NO_DANCER );

            /* Signal audience members to run, lock gives eventual entry */
            mutex_lock(watchMutexes[id]);
                nWatchingMe = toWatch[id];
                do
                :: toWatch[id] == 0 -> break;
                :: toWatch[id] != 0 ->
                    sem_signal(toWatchSemaphores[id]);
                    d_step{nAudienceWatching++};
                    toWatch[id]--;
                od;
            mutex_unlock(watchMutexes[id]);

            if
            :: dancerAged      == id -> agedDancing = 1;
            :: dancerProOrAged == id -> proDancing  = 1;
            fi;

            /* Dance - ensure both dancers are dancing simultaneously */
            skip;
            ( agedDancing == 1 && proDancing == 1 );
            assert(dancerAged != NO_DANCER);
            assert(dancerProOrAged != NO_DANCER);
            assert(agedDancing == 1);
            assert(proDancing == 1);

            /* Leave stage */
            do
            :: nWatchingMe == 0 -> break;
            :: nWatchingMe != 0 ->
                sem_signal(nowWatchingSemaphore);
                nWatchingMe--;
            od;

            /* Wait for audience to leave */
            ( nAudienceWatching == 0 );
            assert(nAudienceWatching == 0);

            /* Aged dancer handles cleanup from leaving the stage */
            if
            :: id == dancerAged ->
                mutex_lock(selectDancerMutex);
                    ( dancerProDone == 1 );
                    i = 0;
                    do
                    :: i == N_DANCERS -> break;
                    :: i != N_DANCERS ->
                        validRequest[i] = 0;
                        i++;
                    od;
                    i = 0;
                    do
                    :: i == N_DANCERS -> break;
                    :: i != N_DANCERS ->
                        if
                        :: toWatch[i] > 0 -> validRequest[i] = 1;
                        :: else           -> skip;
                        fi;
                        i++;
                    od;

                    previousProOrAged = dancerProOrAged;
                    previousAged      = dancerAged;
                    dancerAged        = NO_DANCER;
                    dancerProOrAged   = NO_DANCER;
                    agedDancing       = 0;
                    proDancing        = 0;

                    sem_signal(leaveTogetherSemaphore);
                mutex_unlock(selectDancerMutex);
            :: else -> 
                dancerProDone = 1;
                sem_wait(leaveTogetherSemaphore);
                dancerProDone = 0;
            fi;
        :: else -> skip;
        fi;

    /* End of infinite loop on dancers */
    od;
}

proctype audience() {
    byte dancer;

    do
        :: 1 ->
            /* non-critical section - vegetate */
            do
            :: true -> skip;
            :: true -> break;
            od;

            /* select dancer */
            if
            :: dancer = 0
            :: dancer = 1
            :: dancer = 2
            :: dancer = 3
            fi;
            mutex_lock(watchMutexes[dancer]);
                toWatch[dancer]++;
                validRequest[dancer] = 1;
            mutex_unlock(watchMutexes[dancer]);

            /* wait on semaphore */
            requestedDancer: sem_wait(toWatchSemaphores[dancer]);

            /* Now Watching */
            assert(dancerAged == dancer || dancerProOrAged == dancer);

            /* Observe leave */
            watchingDancer: sem_wait(nowWatchingSemaphore);
            d_step{ nAudienceWatching-- };
    od
}

init {
    /* Initialise semaphores */

    /* Run everything */
    atomic {
        // Init shared variables
        dancerAged = NO_DANCER;
        dancerProOrAged = NO_DANCER;
        dancerProDone = 0;
        nAudienceWatching = 0;
        agedDancing = 0;
        proDancing = 0;

        // Init semaphores
        sem_init(nowWatchingSemaphore);
        sem_init(leaveTogetherSemaphore);

        // Init mutex
        mutex_init(selectDancerMutex);

        // Init things that can be done in a loop
        byte i;
        i = 0;
        do
            :: i != N_DANCERS ->
                toWatch[i]      = 0;
                validRequest[i] = 0;
                sem_init(toWatchSemaphores[i]);
                mutex_init(watchMutexes[i]);
                i++;
            :: i == N_DANCERS -> break;
        od;

        run audience();
        run audience();
        run runDancer(0);
        run runDancer(1);
        run runDancer(2);
        run runDancer(3);
        run runDancer(4);
    }

}

ltl r0 { [] (audience@requestedDancer -> <> audience@watchingDancer) };
ltl p0 { [] (nAudienceWatching < N_AUDIENCE ) };
