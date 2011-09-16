
//#include "non-critical.h"

#define N_AGED      3
#define N_PRO       2
#define N_DANCERS   5

#define NO_DANCER -1

// Macros
#define SEC2USEC(n)     (n * 1000000)
#define USEC2SEC(n)     (n / 1000000.0)
#define NEXTDANCERAGED(n)   ((n+1) % N_AGED)
#define NEXTDANCERPROORAGED(n)   ((n+1) % (N_DANCERS))



// Semaphore implementation (busy-wait)
#define sem_init(S)   S = 0
#define sem_wait(S)   d_step {S > 0; S--}
#define sem_signal(S) S++

// Semaphores
short toWatchSems[N_DANCERS]

proctype audience() {
    byte dancer;
    byte round = 0;
    do :: 1 ->
       /* non-critical section - vegetate */
       /* select dancer */
       if
           :: dancer = 0
           :: dancer = 1
           :: dancer = 2
           :: dancer = 3
           :: dancer = 4
       fi;
       /* wait on semaphore */
       sem_wait(toWatchSems[dancer]);
    od
}

proctype runDancers() {
    short selectedDancerAged = NO_DANCER;
    short selectedDancerProOrAged = NO_DANCER;
    short previousAged = NO_DANCER;
    short previousProOrAged = NO_DANCER;
    short i = 0;
    short dancerAged = NO_DANCER;
    short dancerProOrAged = NO_DANCER;

    do :: 1 ->
        selectedDancerAged = NO_DANCER;
        selectedDancerProOrAged = NO_DANCER;
        
        printf("Selecting next dancers. Previous aged dancer: %d, Previous pro or aged dancer: %d\n", previousAged, previousProOrAged);

        //Find the next aged dancer that people want to watch and is not the same as either of the previous dancers
        selectedDancerAged = NEXTDANCERAGED(previousAged);

        i = 0;
        do :: i != N_AGED ->
            if
                ::(toWatchSems[selectedDancerAged] > 0 && selectedDancerAged != previousAged && selectedDancerAged != previousProOrAged) -> dancerAged = selectedDancerAged;
                :: else -> selectedDancerAged = NEXTDANCERAGED(selectedDancerAged);
            fi;
            i++;
        od;

        
        //If we could not find an aged dancer people want to watch, then just select the next aged dancer who isn't one of the previous dancers
        if :: (dancerAged == NO_DANCER) ->
            selectedDancerAged = NEXTDANCERAGED(previousAged);
            i = 0;
            do :: i != N_AGED ->
                if 
                    :: selectedDancerAged != previousAged && selectedDancerAged != previousProOrAged -> dancerAged = selectedDancerAged;
                    :: else -> selectedDancerAged = NEXTDANCERAGED(selectedDancerAged);
                fi;
                i++;
            od;
        fi;
    
        //If we still cannot find an aged dancer, the arguments given were broken, it's impossible to proceed
        assert(dancerAged != NO_DANCER);
    
        //Find the next pro or aged dancer that people want to watch and is not the same as either of the previous dancers
        selectedDancerProOrAged = NEXTDANCERPROORAGED(previousProOrAged);
        i = 0;
        do :: i != (N_DANCERS - 1) ->
            if
                :: toWatchSems[selectedDancerProOrAged] > 0 && selectedDancerProOrAged != dancerAged && selectedDancerProOrAged != previousAged && selectedDancerProOrAged != previousProOrAged && (N_AGED > 2 || selectedDancerProOrAged >= 2) -> dancerProOrAged = selectedDancerProOrAged;
                :: else -> selectedDancerProOrAged = NEXTDANCERPROORAGED(selectedDancerProOrAged);
            fi;
            i++;
        od;
        
        //If we could not find a pro or aged dancer people want to watch, then just select the next pro or aged dancer who isn't one of the previous dancers
        if ::(dancerProOrAged == NO_DANCER) ->
            selectedDancerProOrAged = NEXTDANCERPROORAGED(previousProOrAged);
            i = 0;
            do :: i != (N_DANCERS - 1) ->
                if 
                    :: selectedDancerProOrAged != dancerAged && selectedDancerProOrAged != previousAged && selectedDancerProOrAged != previousProOrAged && (N_AGED > 2 || selectedDancerProOrAged >= 2) -> dancerProOrAged = selectedDancerProOrAged;
                    :: else -> selectedDancerProOrAged = NEXTDANCERPROORAGED(selectedDancerProOrAged);
                fi;
                i++;
            od;
        fi;
    
        //If we still cannot find an aged dancer, the arguments given were broken, it's impossible to proceed
        assert(dancerProOrAged != NO_DANCER);
    
        printf("Selected dancers. Aged dancer: %d, Pro or aged dancer: %d\n", dancerAged, dancerProOrAged);
    
        // Wait for previous audience members to leave
        //noWatching == 0;
    
        // Notify Audience members to watch
        d_step {
            printf("Singalling %d aged dancers(%d) waiting\n", toWatchSems[dancerAged], dancerAged);
            //noWatching += toWatchSems[dancerAged];
            do :: toWatchSems[dancerAged] != 0 ->
                sem_signal(toWatchSems[dancerAged]);
            od;
    
            printf("Singalling %d pro or aged dancer (%d) waiting\n", toWatchSems[dancerProOrAged], dancerProOrAged);
            //noWatching += toWatch[dancerProOrAged];
            do :: toWatchSems[dancerProOrAged] != 0 ->
                sem_signal(toWatchSems[dancerProOrAged]);
            od;

            //There is no longer a delay when dancer finishes dancing so we do not need the nowWatchingSemaphore
            printf("Finished dancing on stage: Aged dancer %d, Pro or aged dancer: %d\n", dancerAged, dancerProOrAged);
        }
    
        previousAged = dancerAged;
        previousProOrAged = dancerProOrAged;
        dancerAged = NO_DANCER;
        dancerProOrAged = NO_DANCER;
    od
}

init {
    /* Initialise semaphores */

    /* Run everything */
    atomic {
        /*byte i = 0;
        do
            :: i != N_DANCERS ->
                   sem_init(toWatchSems[i]);
                   i++
        od;*/
        sem_init(toWatchSems[0]);
        sem_init(toWatchSems[1]);
        sem_init(toWatchSems[2]);
        sem_init(toWatchSems[3]);
        sem_init(toWatchSems[4]);

        run audience();
        run runDancers();
    }
}
