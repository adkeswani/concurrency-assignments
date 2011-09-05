
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#include <pthread.h>

#define SEC2USEC(n)     (n * 1000000)
#define USEC2SEC(n)     (n / 1000000.0)

#define NO_DANCER       -1

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

/* Dancer A currently on stage */
int dancerA;

int main(int argc, char** argv) {

    // Set global constants
    nAudience = 2;
    nDancers = 5;
    dancerA = NO_DANCER;
    printf("Number of dancers: %d\n", nDancers);
    printf("Number of audience members: %d\n", nAudience);

    // Init Random number generator
    srand(time(NULL));

    // Spawn audience threads
    pthread_t threads[nAudience];
    int rc;
    long t;
    for(t=0; t < nAudience; t++){
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

        // TODO Select dancer from those wishing to be seen
        
        // If no waiting, select random dancer
        if (selectedDancerA == NO_DANCER) {
            selectedDancerA = randomDancer();
            while (selectedDancerA == previousA) {
                selectedDancerA = randomDancer();
            }
        }
        dancerA = selectedDancerA;
        
        // Dance
        printf("Now dancing on stage: %d\n", dancerA);
        usleep(SEC2USEC(10));

        // TODO Leave stage
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

        // Select Dancer
        dancer = randomDancer();
        printf("Audience %ld: Selected to watch dancer: %d\n", id, dancer);

        // TODO Watch

        // TODO Observe leave
    }

    return NULL;
}

