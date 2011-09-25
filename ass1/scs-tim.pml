
#define N_AGED      3
#define N_PRO       1
#define N_DANCERS   4

#define NO_DANCER -1

// Macros
#define NEXTDANCERAGED(n)   ((n+1) % N_AGED)
#define NEXTDANCERPROORAGED(n)   ((n+1) % (N_DANCERS))

//Note: atomic has to be used here as statements inside d_steps
//are not allowed to block and they don't work when you verify

// Audience members waiting to dance
short toWatch[N_DANCERS]

short nDancersOnStage
short nAgedDancersOnStage

short nWaiting
short nAgedWaiting

short dancerCS
short dancerProDone

short tokenAged
short tokenAgedOrPro

short dancerAged
short dancerProOrAged
short previousAged
short previousProOrAged

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
              (dancerAged != NO_DANCER && dancerProOrAged == NO_DANCER && tokenAgedOrPro == id)
             )
            };
            //printf("Trying to dance: %d\n", id);
            assert(dancerCS == 0);
            dancerCS = 1;
            assert(dancerCS == 1);

            // Check number of audience members waiting on dancers
            if
            :: isAged == 1 && nAgedDancersOnStage == 0 -> waiting = nAgedWaiting;
            :: else                                    -> waiting = nWaiting;
            fi;

            if
            :: previousAged != id &&
               previousProOrAged != id &&
               (toWatch[id] > 0 || waiting == 0)
               ->
                // We are eligible to dance
                canDance = 1;
            :: else ->
                // Get the next potential dancer
                if
                :: dancerAged == NO_DANCER -> tokenAged = NEXTDANCERAGED(tokenAged);
                :: else ->
                    tokenAgedOrPro = NEXTDANCERPROORAGED(tokenAgedOrPro);
                    do 
                    :: tokenAgedOrPro != dancerAged -> break;
                    :: tokenAgedOrPro == dancerAged -> tokenAgedOrPro = NEXTDANCERPROORAGED(tokenAgedOrPro);
                    od;
                fi;
                dancerCS = 0;
            fi;

        od;

        // Dancer CS (cont.)
        assert(dancerAged == NO_DANCER || dancerProOrAged == NO_DANCER);
        canDance = 0;
        if
        :: dancerAged == NO_DANCER ->
            dancerAged = id;
            if
            :: tokenAgedOrPro == id -> tokenAgedOrPro = NEXTDANCERPROORAGED(tokenAgedOrPro);
            :: else -> skip;
            fi;
        :: else -> dancerProOrAged = id;
        fi;
        if
            :: isAged -> nAgedDancersOnStage++;
            :: else -> skip;
        fi;
        nDancersOnStage++;
        assert(dancerCS == 1);
        dancerCS = 0;

        // Dance
        ( nDancersOnStage == 2 && dancerCS == 0 );
            //printf("Now dacing: %d\n", id);
        assert(dancerCS == 0);
        assert(nDancersOnStage == 2);
        assert(nAgedDancersOnStage >= 1);
        assert(tokenAged == dancerAged);
        assert(tokenAgedOrPro == dancerProOrAged);
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
            dancerCS = 1;
                dancerProDone = 0;
                previousAged = dancerAged;
                previousProOrAged = dancerProOrAged;
                dancerAged = NO_DANCER;
                dancerProOrAged = NO_DANCER;
                nDancersOnStage = 0;
                nAgedDancersOnStage = 0;
                tokenAged = NEXTDANCERAGED(tokenAged);
                tokenAgedOrPro = NEXTDANCERPROORAGED(tokenAgedOrPro);
            assert(dancerCS == 1);
            dancerCS = 0;
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
                   nAgedWaiting = nAgedWaiting - (isAged * 1)};

            /* Observe leave */
            (dancerAged != dancer && dancerProOrAged != dancer);
    od
}

init {
    /* Initialise semaphores */

    /* Run everything */
    atomic {
        nDancersOnStage = 0;
        nAgedDancersOnStage = 0;
        dancerCS = 0;
        dancerProDone = 0;
        tokenAged = 0;
        tokenAgedOrPro = 0;
        dancerAged = NO_DANCER;
        dancerProOrAged = NO_DANCER;
        previousAged = NO_DANCER;
        previousProOrAged = NO_DANCER;
        nWaiting = 0;
        nAgedWaiting = 0;

        byte i;
        i = 0;
        do
            :: i != N_DANCERS ->
                toWatch[i] = 0;
                i++;
            :: i == N_DANCERS -> break;
        od;

        run audienceThread();
        run dancerThread(0);
        run dancerThread(1);
        run dancerThread(2);
        run dancerThread(3);
    }
}

ltl p0 { [](nDancersOnStage >= 0 && nDancersOnStage <= 2) };
ltl p1 { [](nAgedDancersOnStage >= 0 && nAgedDancersOnStage <= 2) };
ltl r0 { <>(dancerAged != NO_DANCER ) };

