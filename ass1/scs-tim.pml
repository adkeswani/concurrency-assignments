
#define N_AGED      2
#define N_PRO       2
#define N_DANCERS   4
#define N_AUDIENCE  2

#define NO_DANCER -1

// Macros
#define NEXTDANCERAGED(n)   ((n+1) % N_AGED)
#define NEXTDANCERPROORAGED(n)   ((n+1) % (N_DANCERS))

//Note: atomic has to be used here as statements inside d_steps
//are not allowed to block and they don't work when you verify

// Current dancer on stage
short dancerAged
short dancerProOrAged

// Previous dancer on stage
short previousAged
short previousProOrAged

// Dancer CS Management
short dancerCS
short dancerProDone

// Track who has right to try and dance
short tokenAged
short tokenProOrAged

// Audience members waiting to dance
short toWatch[N_DANCERS]

// Number of audience members waiting on each type
short nWaiting
short nAgedWaiting

// Number processes watching dancers
short nWatching

// (Auxiliary) Track number of types of dancers on stage
short nDancersOnStage
short nAgedDancersOnStage

// (Auxiliary) Number of dancers in CS section
short nInDancerCS

proctype dancerThread(byte idx) {
    short isAged;
    short canDance;
    short waiting;
    short limit;
    short i;
    short id;

    id = idx;
    canDance = 0;

    if
    :: id < N_AGED -> isAged = 1;
    :: else        -> isAged = 0;
    fi;

    do
    :: 1 ->
        do
        :: canDance == 1   -> break;
        :: canDance == 0  -> 
            // Await our turn in selecting - linear waiting
            { dancerCS  == 0 &&
             (
              (dancerAged == NO_DANCER && dancerProOrAged == NO_DANCER && tokenAged == id) ||
              (dancerAged != NO_DANCER && dancerProOrAged == NO_DANCER && tokenProOrAged == id)
             )
            };
            //printf("Trying to dance: %d\n", id);
            assert(dancerCS == 0);
            assert(nInDancerCS == 0);
            d_step{ dancerCS = 1; nInDancerCS++ };
            assert(nInDancerCS == 1);
            assert(dancerCS == 1);

            // Check number of audience members waiting on dancers
            if
            :: isAged == 1 && dancerAged == NO_DANCER -> waiting = nAgedWaiting;
            :: else                                   -> waiting = nWaiting;
            fi;

            if
            :: previousAged != id &&
               previousProOrAged != id &&
               ( toWatch[id] > 0 || waiting == 0 ) &&
               ( N_AGED > 2 || isAged == 0 || dancerAged == NO_DANCER)
               ->
                // We are eligible to dance
                canDance = 1;
            :: else ->
                // Get the next potential dancer
                if
                :: dancerAged == NO_DANCER -> tokenAged = NEXTDANCERAGED(tokenAged);
                :: else ->
                    tokenProOrAged = NEXTDANCERPROORAGED(tokenProOrAged);
                    do 
                    :: tokenProOrAged != dancerAged -> break;
                    :: tokenProOrAged == dancerAged -> tokenProOrAged = NEXTDANCERPROORAGED(tokenProOrAged);
                    od;
                fi;

                assert(nInDancerCS == 1);
                d_step{ nInDancerCS--; dancerCS = 0 };
            fi;

        od;

        // Dancer CS (cont.)
        assert(dancerAged == NO_DANCER || dancerProOrAged == NO_DANCER);
        canDance = 0;
        if
        :: dancerAged == NO_DANCER ->
            dancerAged = id;
            if
            :: tokenProOrAged == id -> tokenProOrAged = NEXTDANCERPROORAGED(tokenProOrAged);
            :: else -> skip;
            fi;
        :: else -> dancerProOrAged = id;
        fi;
        // Wait for all watching dancers to continue
        ( toWatch[id] == 0 );
        assert(nDancersOnStage == 0);
        assert(nAgedDancersOnStage == 0);
        assert(dancerCS == 1);
        assert(nInDancerCS == 1);
        d_step{ nInDancerCS--; dancerCS = 0 };

        // Wait for partner
        ( dancerCS == 0 && dancerAged != NO_DANCER && dancerProOrAged != NO_DANCER );
        d_step{nDancersOnStage++;
               nAgedDancersOnStage = nAgedDancersOnStage + (isAged * 1)};

        // Dance
        ( nDancersOnStage == 2 && dancerCS == 0 );
            //printf("Now dacing: %d\n", id);
        assert(dancerCS == 0);
        assert(nDancersOnStage == 2);
        assert(nAgedDancersOnStage >= 1);
        assert(dancerAged < N_AGED);
        assert(dancerAged != previousAged);
        assert(dancerProOrAged != previousProOrAged);
        assert(tokenAged == dancerAged);
        assert(tokenProOrAged == dancerProOrAged);
            //printf("Leaving dancing: %d\n", id);

        // Leave Dancing
        if 
        :: dancerProOrAged == id ->
            // Dancer pro just leaves (waiting for dancer aged to go its work)
            dancerProDone = 1;
        :: dancerAged == id ->
            // Dancer aged fixes up all the variables after pro has left
            ( dancerProDone == 1);
            assert(dancerCS == 0);
            d_step{ dancerCS = 1; nInDancerCS++ };
                // Alter dancers on stage 
                previousAged = dancerAged;
                previousProOrAged = dancerProOrAged;
                dancerAged = NO_DANCER;
                dancerProOrAged = NO_DANCER;

                // Wait on audience to stop watching
                ( nWatching == 0 );

                // Clear other variables
                dancerProDone = 0;
                nDancersOnStage = 0;
                nAgedDancersOnStage = 0;

                // Update tokens away from current dancers
                tokenAged = NEXTDANCERAGED(tokenAged);
                tokenProOrAged = NEXTDANCERPROORAGED(tokenProOrAged);
            assert(dancerCS == 1);
            assert(nInDancerCS == 1);
            d_step{ nInDancerCS--; dancerCS = 0 };
        fi;
    od;
}

proctype audienceThread() {
    byte dancer;
    byte isAged;

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
            if
            :: dancer < N_AGED -> isAged = 1;
            :: else            -> isAged = 0;
            fi;
            d_step{toWatch[dancer]++;
                   nWaiting++;
                   nAgedWaiting = nAgedWaiting + (isAged * 1)};

            /* wait for dancer to appear on stage */
            (dancerAged == dancer || dancerProOrAged == dancer);
            d_step{toWatch[dancer]--;
                   nWaiting--;
                   nAgedWaiting = nAgedWaiting - (isAged * 1);
                   nWatching++};

            /* Observe leave */
            (dancerAged != dancer && dancerProOrAged != dancer);
            d_step{ nWatching-- };
    od
}

init {
    /* Initialise semaphores */

    /* Run everything */
    atomic {
        dancerAged = NO_DANCER;
        dancerProOrAged = NO_DANCER;
        previousAged = NO_DANCER;
        previousProOrAged = NO_DANCER;
        dancerCS = 0;
        dancerProDone = 0;
        tokenAged = 0;
        tokenProOrAged = 0;
        nWaiting = 0;
        nAgedWaiting = 0;

        // Initialise auxiliary variables
        nDancersOnStage = 0;
        nAgedDancersOnStage = 0;
        nWatching = 0;

        byte i;
        i = 0;
        do
            :: i != N_DANCERS ->
                toWatch[i] = 0;
                i++;
            :: i == N_DANCERS -> break;
        od;

        run audienceThread();
        run audienceThread();
        run dancerThread(0);
        run dancerThread(1);
        run dancerThread(2);
        run dancerThread(3);
    }
}

ltl p0 { [](nDancersOnStage >= 0 && nDancersOnStage <= 2) };
ltl p1 { [](nAgedDancersOnStage >= 0 && nAgedDancersOnStage <= 2) };
ltl p2 { [](dancerAged < N_AGED && dancerProOrAged < N_DANCERS) };
ltl p3 { [](nWaiting <= N_AUDIENCE && nWatching <= N_AUDIENCE) };
ltl p4 { [](nInDancerCS <= 1) };

