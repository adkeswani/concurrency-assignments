
//#include "non-critical.h"

#define N_AGED      3
#define N_PRO       2
#define N_DANCERS   5

// Semaphore implementation (busy-wait)
#define sem_init(S)   S = 0
#define sem_wait(S)   d_step {S > 0; S--}
#define sem_signal(S) S++

// Lock implementation
#define mutex_init(L)   L = 1
#define mutex_lock(L)   d_step {L == 1; L = 0}
#define mutex_unlock(L) L = 1

// Mutexs
byte watchMutex

// Semaphores
int toWatchSems[N_DANCERS]
int nowWatchingSem

// Number of audience members watching
byte noWatching

proctype audience() {
    byte dancer;

    do
        :: 
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
           mutex_unlock(watchMutex);
           /* wait on semaphore */
           sem_wait(toWatchSems[dancer]);
           /* Observe leave */
           sem_wait(nowWatchingSem);
           d_step{noWatching--};
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
        noWatching = 100;
        mutex_init(watchMutex);
        sem_init(toWatchSems[0]);
        sem_init(toWatchSems[1]);
        sem_init(toWatchSems[2]);
        sem_init(toWatchSems[3]);
        sem_init(toWatchSems[4]);
        sem_init(nowWatchingSem);

        run audience();
    }
}
