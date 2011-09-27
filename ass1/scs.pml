#define N_AGED      3
#define N_PRO       2
#define N_DANCERS   5

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

// Mutexs
byte watchMutex
byte nowWatchingMutex

int toWatchSemaphores[N_DANCERS]
short toWatch[N_DANCERS]
int nowWatchingSemaphore

// Number of audience members watching
byte nWatching

short previousAged = N_DANCERS;
short previousProOrAged = N_DANCERS;
short dancerAged = NO_DANCER;
short dancerProOrAged = NO_DANCER;

proctype runDancers() {
    short selectedDancerAged = NO_DANCER;
    short selectedDancerProOrAged = NO_DANCER;
    short i = 0;

    do :: 1 ->
        selectedDancerAged = NO_DANCER;
        selectedDancerProOrAged = NO_DANCER;
        
        printf("Selecting next dancers. Previous aged dancer: %d, Previous pro or aged dancer: %d\n", previousAged, previousProOrAged);

        //Find the next aged dancer that people want to watch and is not the same as either of the previous dancers
        selectedDancerAged = NEXTDANCERAGED(previousAged);

        i = 0;
        do 
            :: i != N_AGED ->
                if
                    ::(toWatch[selectedDancerAged] > 0 && 
                      selectedDancerAged != previousAged &&     
                      selectedDancerAged != previousProOrAged) -> 
                        dancerAged = selectedDancerAged;
                        break;
                    :: else -> 
                        selectedDancerAged = NEXTDANCERAGED(selectedDancerAged);
                fi;
                i++;
            :: i == N_AGED ->
                break;
        od;

        
        //If we could not find an aged dancer people want to watch, then just select the next aged dancer who isn't one of the previous dancers
        if :: (dancerAged == NO_DANCER) ->
                selectedDancerAged = NEXTDANCERAGED(previousAged);
                i = 0;
                do 
                    :: i != N_AGED ->
                        if 
                            :: selectedDancerAged != previousAged && selectedDancerAged != previousProOrAged -> 
                                dancerAged = selectedDancerAged;
                                break;
                            :: else -> 
                                selectedDancerAged = NEXTDANCERAGED(selectedDancerAged);
                        fi;
                        i++;
                    :: i == N_AGED ->
                        break;
                od;
            :: (dancerAged != NO_DANCER) -> skip;
        fi;
    
        //If we still cannot find an aged dancer, the arguments given were broken, it's impossible to proceed
        assert(dancerAged != NO_DANCER);
    
        //Find the next pro or aged dancer that people want to watch and is not the same as either of the previous dancers
        selectedDancerProOrAged = NEXTDANCERPROORAGED(previousProOrAged);
        i = 0;
        do 
            :: i != (N_DANCERS - 1) ->
                if
                    :: toWatch[selectedDancerProOrAged] > 0 && 
                       selectedDancerProOrAged != dancerAged && 
                       selectedDancerProOrAged != previousAged && 
                       selectedDancerProOrAged != previousProOrAged && 
                       (N_AGED > 2 || selectedDancerProOrAged >= 2) -> 
                        dancerProOrAged = selectedDancerProOrAged;
                        break;
                    :: else -> 
                        selectedDancerProOrAged = NEXTDANCERPROORAGED(selectedDancerProOrAged);
                fi;
                i++;
            :: i == (N_DANCERS - 1) -> 
                break;
        od;
        
        //If we could not find a pro or aged dancer people want to watch, then just select the next pro or aged dancer who isn't one of the previous dancers
        if ::(dancerProOrAged == NO_DANCER) ->
                selectedDancerProOrAged = NEXTDANCERPROORAGED(previousProOrAged);
                i = 0;
                do 
                    :: i != (N_DANCERS - 1) ->
                        if 
                            :: selectedDancerProOrAged != dancerAged && 
                               selectedDancerProOrAged != previousAged && 
                               selectedDancerProOrAged != previousProOrAged && 
                               (N_AGED > 2 || selectedDancerProOrAged >= 2) -> 
                                dancerProOrAged = selectedDancerProOrAged;
                                break;
                            :: else -> 
                                selectedDancerProOrAged = NEXTDANCERPROORAGED(selectedDancerProOrAged);
                        fi;
                        i++;
                    :: i == (N_DANCERS - 1) ->
                        break;
                od;
            :: (dancerProOrAged != NO_DANCER) -> skip;
        fi;
    
        //If we still cannot find an aged dancer, the arguments given were broken, it's impossible to proceed
        assert(dancerProOrAged != NO_DANCER);
    
        printf("Selected dancers. Aged dancer: %d, Pro or aged dancer: %d\n", dancerAged, dancerProOrAged);

        //Check that some rules are being followed
        assert(dancerAged != previousAged && dancerAged != previousProOrAged);
        assert(dancerProOrAged != previousAged && dancerProOrAged != previousProOrAged);
        assert(dancerAged != dancerProOrAged);
        assert(dancerAged < N_AGED);
        assert(dancerProOrAged < N_DANCERS);

        // Ensure that all previously watching audience members have finished watching
        nWatching == 0;
    
        // Notify Audience members to watch
        mutex_lock(watchMutex);
        mutex_lock(nowWatchingMutex);
            printf("Singalling %d aged dancers(%d) waiting\n", toWatch[dancerAged], dancerAged);
            nWatching = nWatching + toWatch[dancerAged];
            do 
                :: toWatch[dancerAged] != 0 ->
                    sem_signal(toWatchSemaphores[dancerAged]);
                    toWatch[dancerAged]--;
                :: toWatch[dancerAged] == 0 ->
                    break;
            od;
    
            printf("Singalling %d pro or aged dancer (%d) waiting\n", toWatchSemaphores[dancerProOrAged], dancerProOrAged);
            nWatching = nWatching + toWatch[dancerProOrAged];
            do 
                :: toWatch[dancerProOrAged] != 0 ->
                    sem_signal(toWatchSemaphores[dancerProOrAged]);
                    toWatch[dancerProOrAged]--;
                :: toWatch[dancerProOrAged] == 0 ->
                    break;
            od;
        mutex_unlock(watchMutex);
        mutex_unlock(nowWatchingMutex);

        printf("Now dancing on stage: Aged dancer: %d, Pro or aged dancer: %d\n", dancerAged, dancerProOrAged);

        printf("Finished dancing on stage: Aged dancer %d, Pro or aged dancer: %d\n", dancerAged, dancerProOrAged);

        //Tell audience members that they have finished watching
        i = 0;
        do
            :: i != nWatching ->
                sem_signal(nowWatchingSemaphore);
            :: i == nWatching ->
                break;
        od;
    
        previousAged = dancerAged;
        previousProOrAged = dancerProOrAged;
        dancerAged = NO_DANCER;
        dancerProOrAged = NO_DANCER;
    od;
}

proctype runDancer(byte id) {
    byte id = id;
    byte nWatching = 0;
    bool validRequestsExist = false;

    do
        :: 1 ->
            //Lock to prevent > 2 dancers being selected
            mutex_lock(selectDancerMutex);
                if 
                    :: dancerAged == NO_DANCER || dancerProOrAged == NO_DANCER ->
                        //Check if there are any valid requests for dancers
                        validRequestsExist = false;

                        byte i = 0;
                        do
                            :: i != nDancers ->
                                validRequestsExist = validRequestsExist || validRequest[id];
                                i++
                            :: i == nDancers ->
                                break
                        od

                        //This dancer can be selected if there are currently no requests or if this dancer has been requested
                        if 
                            :: (!validRequestsExist || validRequest[id]) ->
                                if 
                                    :: (id != previousAged && id != previousProOrAged) ->
                                        if 
                                            :: (id < nAgedDancers && dancerAged == NO_DANCER) ->
                                                printf("%ld became new aged dancer\n", id);
                                                dancerAged = id;
                                            :: (dancerProOrAged == NO_DANCER) ->
                                                //Handle special case where there are 2 aged dancers only. Prevents both dancing at same time
                                                if 
                                                    :: (id >= nAgedDancers || (nAgedDancers > 2)) ->
                                                        printf("%ld became new pro dancer\n", id);
                                                        dancerProOrAged = id;
                                                    :: else ->
                                                        break
                                                fi
                                            :: else ->
                                                break
                                        fi
                                    :: else ->
                                        break
                                fi;

                                //Regardless of whether or not the request is fulfilled, the request is no longer valid
                                validRequest[id] = false;
                            :: else ->
                                skip
                        fi
                    :: else ->
                        skip
                fi
            mutex_unlock(selectDancerMutex);
    
        if (dancerAged == id || dancerProOrAged == id) {
            //Wait until the other dancer has also been selected
            while (dancerAged == NO_DANCER || dancerProOrAged == NO_DANCER) { };

            printf("%ld now dancing on stage\n", id);

            // Lock prevents audience members adding themselves while others are being signalled by runDancer()
            printf("Signalling %d audience members waiting for dancer %ld\n", toWatch[id], id);
            pthread_mutex_lock(&(watchMutexes[id]));
                nWatching = toWatch[id];
                for (; toWatch[id] != 0; toWatch[id]--) {
                    sem_post(&toWatchSemaphores[id]);
                }
            pthread_mutex_unlock(&(watchMutexes[id]));

            //Dance
            usleep(SEC2USEC(10));
    
            // Leave stage
            printf("%ld finished dancing on stage\n", id);
            for (; nWatching != 0; nWatching--) {
                sem_post(&nowWatchingSemaphore);
            }
    
            //Let the aged dancer thread handle the resetting of dancers
            if (id == dancerAged) {
                //Lock prevents new dancers being selected while dancers are being reset
                pthread_mutex_lock(&selectDancerMutex);
                    //Reset nValidRequests as previously invalid requests may now be valid
                    int i;
                    for (i = 0; i != nDancers; i++) {
                        validRequest[i] = false; 
                    }
                    for (i = 0; i != nDancers; i++) {
                        if (toWatch[i] > 0) {validRequest[i] = true;}
                    }
    
                    //Reset dancers
                    previousProOrAged = dancerProOrAged; 
                    previousAged = dancerAged;
                    dancerAged = NO_DANCER;
                    dancerProOrAged = NO_DANCER;

                    //Allow the pro dancer to leave
                    sem_post(&leaveTogetherSemaphore);
                pthread_mutex_unlock(&selectDancerMutex);
            } else {
                //Semaphore prevents pro dancer continuing before aged dancer has reset dancers
                sem_wait(&leaveTogetherSemaphore);
            }
            printf("%ld has left stage\n", id);
        }
    }

    return NULL;
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
            mutex_lock(watchMutex);
                if
                    :: dancer = 0
                    :: dancer = 1
                    :: dancer = 2
                    :: dancer = 3
                    :: dancer = 4
                fi;
                toWatch[dancer]++;
            mutex_unlock(watchMutex);

            /* wait on semaphore */
            requestedDancer: sem_wait(toWatchSemaphores[dancer]);

            assert(dancerAged == dancer || dancerProOrAged == dancer);

            /* Observe leave */
            watchingDancer: sem_wait(nowWatchingSemaphore);

            mutex_lock(nowWatchingMutex);
                nWatching--;
            mutex_unlock(nowWatchingMutex);
    od
}

init {
    /* Initialise semaphores */

    /* Run everything */
    atomic {
        nWatching = 0;

        mutex_init(watchMutex);
        mutex_init(nowWatchingMutex);

        sem_init(toWatchSemaphores[0]);
        sem_init(toWatchSemaphores[1]);
        sem_init(toWatchSemaphores[2]);
        sem_init(toWatchSemaphores[3]);
        sem_init(toWatchSemaphores[4]);

        sem_init(nowWatchingSemaphore);

        byte i;
        i = 0;
        do
            :: i != N_DANCERS ->
                toWatch[i] = 0;
                i++;
            :: i == N_DANCERS -> break;
        od;

        dancerAged = NO_DANCER;
        dancerProOrAged = NO_DANCER;

        i = 0;
        do
            :: i != N_DANCERS ->
                validRequest[i] = false;
                i++;
            :: i == N_DANCERS -> break;
        od;

        sem_init(nowWatchingSemaphore);
        sem_init(leaveTogetherSemaphore);
    
        // Set up mutexes
        i = 0;
        do
            :: i != N_DANCERS ->
                mutex_init(watchMutexes[i]);
                i++;
            :: i == N_DANCERS -> break;
        od;

        run audience();
        run audience();
        run runDancer();
        run runDancer();
        run runDancer();
    }

}
