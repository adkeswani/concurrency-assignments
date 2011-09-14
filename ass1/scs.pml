
//#include "non-critical.h"

#define N_AGED      3
#define N_PRO       2
#define N_DANCERS   5
#define N_ROUNDS    1

// Semaphore implementation (busy-wait)
#define sem_init(S)   S = 0
#define sem_wait(S)   d_step {S > 0; S--}
#define sem_signal(S) S++

// Semaphores
int toWatchSems[N_DANCERS]

proctype audience() {
    byte dancer;
    byte round = 0;
    do
        :: round != N_ROUNDS ->
           /* non-critical section - vegetate */
           /* select dancer */
           if
               :: dancer = 1
               :: dancer = 2
               :: dancer = 3
               :: dancer = 4
               :: dancer = 5
           fi;
           /* wait on semaphore */
           sem_wait(toWatchSems[dancer]);
           /* next round */
           round++
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
    }
}
