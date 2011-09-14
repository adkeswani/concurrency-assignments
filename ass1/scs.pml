
//#include "non-critical.h"

#define N_AGED      3
#define N_PRO       2
#define D_DANCERS   (N_AGED+N_PRO)

// Semaphore implementation (busy-wait)
#define sem_init(S)   (S = 0)
#define sem_wait(S)   (d_step {S > 0; s--} )
#define sem_signal(S) (S++)

// Semaphores
int S1;


proctype audience() {
    byte dancer;
    do
        :: 
           /* non-critical section - vegetate */
           if
               :: dancer = 1
               :: dancer = 2
               :: dancer = 3
               :: dancer = 4
               :: dancer = 5
           fi;
    od
}

init {
    atomic {
        run audience();
    }
}
