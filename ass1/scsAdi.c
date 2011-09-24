
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <assert.h>

#include <pthread.h>
#include <semaphore.h>

// Constants
#define NO_DANCER       -1
#define N_PRO_DANCERS_ARG  1
#define N_AGED_DANCERS_ARG 2
#define N_AUDIENCE_ARG 3
#define N_ROUNDS_ARG 4

// Macros
#define SEC2USEC(n)     (n * 1000000)
#define USEC2SEC(n)     (n / 1000000.0)
#define NEXTDANCERAGED(n)   ((n+1) % nAgedDancers)
#define NEXTDANCERPROORAGED(n)   ((n+1) % (nDancers))

// Methods

// Randomly select a dancer
int randomDancer();

// Single Audience member
void *runAudience(void *id);

// Method for running dancer selection/dancing/leaving
//void runDancers();
void *runDancer(void *idPtr);

// Shared Variables

//Number of pro dancers
unsigned int nProDancers = 0;

//Number of aged dancers
unsigned int nAgedDancers = 0;

// Number of audience members
unsigned int nAudience = 0;

// Number of rounds
unsigned int nRounds = 0;

// Number of dancers
unsigned int nDancers = 0;

// Dancers currently on stage
long dancerAged, dancerProOrAged;

// Dancers previously on stage
long previousAged, previousProOrAged;

// Number of audience members requesting
unsigned int nValidRequests;

// Count of waiting audience members
unsigned int *toWatch;

// Mutex for changing variables associated with what audience members wish to watch
pthread_mutex_t watchMutex = PTHREAD_MUTEX_INITIALIZER;

// Mutex for changing the nWatching value
pthread_mutex_t nowWatchingMutex = PTHREAD_MUTEX_INITIALIZER;

pthread_mutex_t dancerTestAndSetMutex = PTHREAD_MUTEX_INITIALIZER;

// Array of semaphores for watching a given dancer
sem_t *toWatchSemaphores;

// Semaphore for audience members now watching the dancers
sem_t nowWatchingSemaphore;

sem_t randomSemaphore;

int main(int argc, char** argv) {
    int i;

    if (argc != 5) {
        printf("Usage: ./scs numProDancers numAgedDancers numAudienceMembers numRounds\n");
        return 0;
    }

    // Set global constants
    nProDancers = atoi(argv[N_PRO_DANCERS_ARG]);
    nAgedDancers = atoi(argv[N_AGED_DANCERS_ARG]);
    nAudience = atoi(argv[N_AUDIENCE_ARG]);
    nRounds = atoi(argv[N_ROUNDS_ARG]);
    nDancers = nProDancers + nAgedDancers;
    printf("Number of pro dancers: %d\n", nProDancers);
    printf("Number of aged dancers: %d\n", nAgedDancers);
    printf("Number of audience members: %d\n", nAudience);
    printf("Number of rounds: %d\n", nRounds);

    // Sanity checks
    assert(nAgedDancers >= 2);
    assert(nDancers >= 4);

    // Set global constants
    dancerAged = NO_DANCER;
    dancerProOrAged = NO_DANCER;

    // Init random number generator
    srand(time(NULL));

    // Setup toWatch
    toWatch = malloc(nDancers * sizeof(unsigned int));
    for(i = 0; i != (nDancers); i++) {
        toWatch[i] = 0;
    }

    // Set up semaphores
    toWatchSemaphores = malloc(nDancers * sizeof(sem_t));
    for(i = 0; i != (nDancers); i++) {
        printf("Initialising semaphore %d\n", i);
        if(sem_init(&toWatchSemaphores[i], 0, 0)) {
            printf("***** Could not initialise semaphore: %d\n", i);
            exit(-1);
        }
    }
    sem_init(&nowWatchingSemaphore, 0, 0);
    sem_init(&randomSemaphore, 0, 0);

    //Spawn threads
    //Set up thread attributes so they are all detached
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);

    // Spawn audience threads
    pthread_t audienceThreads[nAudience];
    int rc;
    long t;
    for(t = 0; t != nAudience; t++) {
        printf("Creating audience thread %ld\n", t);
        rc = pthread_create(&audienceThreads[t], &attr, runAudience, (void *)t);
        if (rc) {
            printf("***** Could not create thread. Return code from pthread_create() is: %d\n", rc);
            exit(-1);
        }
    }

    // Spawn dancer threads
    pthread_t dancerThreads[nDancers];
    for (t = 0; t != nDancers; t++) {
        printf("Creating dancer thread %ld\n", t);
        rc = pthread_create(&dancerThreads[t], &attr, runDancer, (void *)t);
        if (rc) {
            printf("***** Could not create thread. Return code from pthread_create() is: %d\n", rc);
            exit(-1);
        }
    }

    pthread_attr_destroy(&attr);
    pthread_exit(NULL);
}

int randomDancer() {
    return rand() % (nDancers);
}

void dancerTestAndSet(long *dancer, int id) {
    pthread_mutex_lock(&dancerTestAndSetMutex);
        if (*dancer == NO_DANCER) {
            *dancer = id;
        }
    pthread_mutex_unlock(&dancerTestAndSetMutex);
}

void *runDancer(void *idPtr) {
    long id = (long)idPtr;
    unsigned int nWatching = 0;

    while (1) {
        pthread_mutex_lock(&dancerTestAndSetMutex);
            if (dancerAged == NO_DANCER || dancerProOrAged == NO_DANCER) {
                if (nValidRequests == 0 && id != previousAged && id != previousProOrAged) {
                    if (id < nAgedDancers && dancerAged == NO_DANCER) {
                        dancerAged = id;
                    } else if (dancerProOrAged == NO_DANCER) {
                        if (id >= nAgedDancers || (nAgedDancers >= 2)) {
                            dancerProOrAged = id;
                        } 
                    }
                } else if (toWatch[id] > 0) {
                    if (id != previousAged && id != previousProOrAged) {
                        if (id < nAgedDancers && dancerAged == NO_DANCER) {
                            dancerAged = id;
                        } else if (dancerProOrAged == NO_DANCER) {
                            if (id >= nAgedDancers || (nAgedDancers >= 2)) {
                                dancerProOrAged = id;
                            }
                        }
                    }
                    nValidRequests--;
                }
            }
        pthread_mutex_unlock(&dancerTestAndSetMutex);

        if (dancerAged == id || dancerProOrAged == id) {
            while (dancerAged == NO_DANCER || dancerProOrAged == NO_DANCER) { };

            printf("%ld now dancing on stage\n", id);

            printf("Signalling %d audience members waiting for dancer %ld\n", toWatch[id], id);
            pthread_mutex_lock(&watchMutex);
                nWatching = toWatch[id];
                for (; toWatch[id] != 0; toWatch[id]--) {
                    sem_post(&toWatchSemaphores[id]);
                }
            pthread_mutex_unlock(&watchMutex);

            usleep(SEC2USEC(10));
    
            // Leave stage
            printf("%ld finished dancing on stage\n", id);
            for (; nWatching != 0; nWatching--) {
                sem_post(&nowWatchingSemaphore);
            }
    
            if (id == dancerAged) {
                pthread_mutex_lock(&dancerTestAndSetMutex);
                    //Reset nValidRequests
                    nValidRequests = 0;
                    int i;
                    for (i = 0; i != nDancers; i++) {
                        nValidRequests += toWatch[i];
                    }
    
                    //Reset dancers
                    previousProOrAged = dancerProOrAged; 
                    previousAged = dancerAged;
                    dancerAged = NO_DANCER;
                    dancerProOrAged = NO_DANCER;

                    sem_post(&randomSemaphore);
    
                    printf("%ld has left stage\n", id);
                pthread_mutex_unlock(&dancerTestAndSetMutex);
            } else {
                sem_wait(&randomSemaphore);
                printf("%ld has left stage\n", id);
            }
        }
    }

    return NULL;
}
    
void *runAudience(void* idPtr) {
    long id = (long) idPtr;
    int sleepDuration = 1000;
    int roundsCompleted = 0;
    long dancer = NO_DANCER;

    for (roundsCompleted = 0; roundsCompleted != nRounds || nRounds == 0; roundsCompleted++) {
        // Vegetate
        printf("Audience %ld: Beginning vegetation \n", id);
        sleepDuration = rand() % SEC2USEC(10);
        printf("Audience %ld: Sleeping for %.2lf seconds\n", id, USEC2SEC(sleepDuration));
        usleep(sleepDuration);
        //usleep(SEC2USEC(20));

        // Select Dancer
        // Take mutex so that we can't add ourselves when audience members are being signalled by runDancers()
        pthread_mutex_lock(&watchMutex);
            dancer = randomDancer();
            toWatch[dancer]++;
            nValidRequests++;
            printf("Audience %ld: Selected to watch dancer: %ld\n", id, dancer);
        pthread_mutex_unlock(&watchMutex);

        // Watch - Wait on semaphore
        sem_wait(&toWatchSemaphores[dancer]);
        printf("Audience %ld: Now Watching dancer: %ld\n", id, dancer);

        // Observe leave
        sem_wait(&nowWatchingSemaphore);
    }
    printf("Audience %ld: Finished %d rounds, dying now.\n", id, nRounds);
    
    return NULL;
}

//void runDancers() {
//    printf("Starting Dancers\n");
//    printf("All dancers <= %d are aged, all dancers > %d are pro\n", nAgedDancers - 1, nAgedDancers - 1);
//
//    int selectedDancerAged = NO_DANCER;
//    int selectedDancerProOrAged = NO_DANCER;
//    int previousAged = NO_DANCER;
//    int previousProOrAged = NO_DANCER;
//    int i;
//
//    while(1) {
//        selectedDancerAged = NO_DANCER;
//        selectedDancerProOrAged = NO_DANCER;
//        
//        printf("Selecting next dancers. Previous aged dancer: %d, Previous pro or aged dancer: %d\n", previousAged, previousProOrAged);
//        //Find the next aged dancer that people want to watch and is not the same as either of the previous dancers
//        selectedDancerAged = NEXTDANCERAGED(previousAged);
//        for (i = 0; i < nAgedDancers - 1; i++) {
//            if (toWatch[selectedDancerAged] > 0 && selectedDancerAged != previousAged && selectedDancerAged != previousProOrAged) {
//                dancerAged = selectedDancerAged;
//                break;
//            } else {
//                selectedDancerAged = NEXTDANCERAGED(selectedDancerAged);
//            }
//        }
//        
//        //If we could not find an aged dancer people want to watch, then just select the next aged dancer who isn't one of the previous dancers
//        if (dancerAged == NO_DANCER) {
//            selectedDancerAged = NEXTDANCERAGED(previousAged);
//            for (i = 0; i < nAgedDancers - 1; i++) {
//                if (selectedDancerAged != previousAged && selectedDancerAged != previousProOrAged) {
//                    dancerAged = selectedDancerAged;
//                    break;
//                } else {
//                    selectedDancerAged = NEXTDANCERAGED(selectedDancerAged);
//                }
//            }
//        }
//
//        //If we still cannot find an aged dancer, the arguments given were broken, it's impossible to proceed
//        assert(dancerAged != NO_DANCER);
//
//        //Find the next pro or aged dancer that people want to watch and is not the same as either of the previous dancers
//        selectedDancerProOrAged = NEXTDANCERPROORAGED(previousProOrAged);
//        for (i = 0; i < (nDancers - 1); i++) {
//            if (toWatch[selectedDancerProOrAged] > 0 &&
//                selectedDancerProOrAged != dancerAged &&
//                selectedDancerProOrAged != previousAged &&
//                selectedDancerProOrAged != previousProOrAged &&
//                (nAgedDancers > 2 || selectedDancerProOrAged >= 2)) {
//                dancerProOrAged = selectedDancerProOrAged;
//                break;
//            } else {
//                selectedDancerProOrAged = NEXTDANCERPROORAGED(selectedDancerProOrAged);
//            }
//        }
//        
//        //If we could not find a pro or aged dancer people want to watch, then just select the next pro or aged dancer who isn't one of the previous dancers
//        if (dancerProOrAged == NO_DANCER) {
//            selectedDancerProOrAged = NEXTDANCERPROORAGED(previousProOrAged);
//            for (i = 0; i < (nDancers - 1); i++) {
//                if (selectedDancerProOrAged != dancerAged &&
//                    selectedDancerProOrAged != previousAged &&
//                    selectedDancerProOrAged != previousProOrAged &&
//                    (nAgedDancers > 2 || selectedDancerProOrAged >= 2)) {
//                    dancerProOrAged = selectedDancerProOrAged;
//                    break;
//                } else {
//                    selectedDancerProOrAged = NEXTDANCERPROORAGED(selectedDancerProOrAged);
//                }
//            }
//        }
//
//        //If we still cannot find an aged dancer, the arguments given were broken, it's impossible to proceed
//        assert(dancerProOrAged != NO_DANCER);
//
//        printf("Selected dancers. Aged dancer: %d, Pro or aged dancer: %d\n", dancerAged, dancerProOrAged);
//
//        // Wait for previous audience members to leave
//        while (nWatching != 0) {};
//
//        // Notify Audience members to watch
//        pthread_mutex_lock(&watchMutex);
//        pthread_mutex_lock(&nowWatchingMutex);
//            printf("Singalling %d aged dancers(%d) waiting\n", toWatch[dancerAged], dancerAged);
//            nWatching += toWatch[dancerAged];
//            for (; toWatch[dancerAged] > 0; toWatch[dancerAged]--) {
//                sem_post(&toWatchSemaphores[dancerAged]);
//            }
//
//            printf("Singalling %d pro or aged dancer (%d) waiting\n", toWatch[dancerProOrAged], dancerProOrAged);
//            nWatching += toWatch[dancerProOrAged];
//            for (; toWatch[dancerProOrAged] > 0; toWatch[dancerProOrAged]--) {
//                sem_post(&toWatchSemaphores[dancerProOrAged]);
//            }
//        pthread_mutex_unlock(&nowWatchingMutex);
//        pthread_mutex_unlock(&watchMutex);
//
//        // Dance
//        printf("Now dancing on stage: Aged dancer: %d, Pro or aged dancer: %d\n", dancerAged, dancerProOrAged);
//        usleep(SEC2USEC(10));
//
//        // Leave stage
//        printf("Finished dancing on stage: Aged dancer %d, Pro or aged dancer: %d\n", dancerAged, dancerProOrAged);
//        for (i = 0; i < nWatching; i++) {
//            sem_post(&nowWatchingSemaphore);
//        }
//
//        previousAged = dancerAged;
//        previousProOrAged = dancerProOrAged;
//        dancerAged = NO_DANCER;
//        dancerProOrAged = NO_DANCER;
//    }
//}


