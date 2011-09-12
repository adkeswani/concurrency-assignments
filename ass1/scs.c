
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#include <pthread.h>

// Constants
#define NO_DANCER       -1

// Macros
#define SEC2USEC(n)     (n * 1000000)
#define USEC2SEC(n)     (n / 1000000.0)
#define NEXTDANCER(n)   ((n+1) % nDancers)

// Methods

/* Randomly select a dancer */
int randomDancer();

/* Single Audience member */
void *runAudience(void* id);

/* Method for running dancer selection/dancing/leaving */
void runDancers();

// Shared Variables

/* Number of audience members */
unsigned int nAudience = 0;

/* Number of dancers */
unsigned int nDancers = 0;

/* Counter of number of audience wanting to see a given dancer */
unsigned int *toWatch;

// Mutex
pthread_mutex_t watchMutex = PTHREAD_MUTEX_INITIALIZER;

/* Dancer A currently on stage */
int dancerA;

int main(int argc, char** argv) {

    // Set global constants
    nAudience = 2;
    nDancers = 5;
    dancerA = NO_DANCER;
    toWatch = malloc(nDancers * sizeof(int));
    for(int i = 0; i < nDancers; i++) toWatch[i] = 0;
    printf("Number of dancers: %d\n", nDancers);
    printf("Number of audience members: %d\n", nAudience);

    // Init Random number generator
    srand(time(NULL));

    // Spawn audience threads
    pthread_t threads[nAudience];
    int rc;
    long t;
    for(t=0; t < nAudience; t++) {
        printf("Creating thread %ld\n", t);
        rc = pthread_create(&threads[t], NULL, runAudience, (void *)t);
        if (rc) {
            printf("ERROR; return code from pthread_create() is %d\n", rc);
            exit(-1);
        }
    }

    // Start dancer method in this thread
    runDancers();

    pthread_exit(NULL);
}

int randomDancer() {
    return rand() % nDancers;
}

void runDancers() {
    printf("Starting Dancers\n");

    int selectedDancerA = NO_DANCER;
    int previousA = NO_DANCER;

    while(1) {
        selectedDancerA = NO_DANCER;
        dancerA = NO_DANCER;

        // TODO Select dancer from those wishing to be seen
        selectedDancerA = NEXTDANCER(previousA);
        for(int i = 0; i < nDancers; i++, selectedDancerA = NEXTDANCER(selectedDancerA)) { // Need this loop format as prev could be NO_DANCER
            if (toWatch[i] > 0 && selectedDancerA != previousA) {
                dancerA = i;
            }
        }
        
        // If no waiting, select random dancer
        if (dancerA == NO_DANCER) {
            selectedDancerA = NEXTDANCER(previousA);
            while (selectedDancerA == previousA) {
                selectedDancerA = NEXTDANCER(selectedDancerA);
            }
        }
        dancerA = selectedDancerA;
        
        // Dance
        printf("Now dancing on stage: %d\n", dancerA);
        usleep(SEC2USEC(5));

        // TODO Leave stage
        pthread_mutex_lock(&watchMutex);
        toWatch[dancerA] = 0;
        pthread_mutex_unlock(&watchMutex);
        previousA = dancerA;
        dancerA = NO_DANCER;
    }
}

void *runAudience(void* idPtr) {
    long id = (long) idPtr;
    //printf("My Audience member Id: %ld\n", id);

    int sleepDuration = 1000;
    int dancer = -1;

    while(1) {
        // Vegetate
        sleepDuration = rand() % SEC2USEC(10);
        printf("Audience %ld: Sleeping for %.2lf seconds\n", id, USEC2SEC(sleepDuration));
        usleep(sleepDuration);
        //usleep(SEC2USEC(20));

        // Select Dancer
        dancer = randomDancer();
        pthread_mutex_lock(&watchMutex);
        printf("Audience %ld: Selected to watch dancer: %d\n", id, dancer);
        toWatch[dancer]++;
        pthread_mutex_unlock(&watchMutex);

        // TODO Watch

        // TODO Observe leave
    }

    return NULL;
}

