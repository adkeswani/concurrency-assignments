
//#include "non-critical.h"

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
        fi;
    
        //If we still cannot find an aged dancer, the arguments given were broken, it's impossible to proceed
        assert(dancerProOrAged != NO_DANCER);
    
        printf("Selected dancers. Aged dancer: %d, Pro or aged dancer: %d\n", dancerAged, dancerProOrAged);
    
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

proctype audience() {
    byte dancer;

    do
        :: 1 ->
            /* non-critical section - vegetate */

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
            sem_wait(toWatchSemaphores[dancer]);

            /* Observe leave */
            sem_wait(nowWatchingSemaphore);

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
            :: i == N_DANCERS ->
                break;
        od;

        run audience();
        run runDancers();
    }
}

ltl l0 {[] ((dancerAged != previousAged) && (dancerAged != previousProOrAged) && (dancerProOrAged != previousAged) && (dancerProOrAged != previousProOrAged) && (dancerAged != dancerProOrAged))}
