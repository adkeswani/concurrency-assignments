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

typedef enum {false, true} bool;

// Methods

// Randomly select a dancer
long randomDancer();

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
bool *validRequest;

// Count of waiting audience members
unsigned int *toWatch;

// Mutexes for changing variables associated with what audience members wish to watch
pthread_mutex_t *watchMutexes;

// Mutex for selecting the next dancer
pthread_mutex_t selectDancerMutex = PTHREAD_MUTEX_INITIALIZER;

// Array of semaphores for watching a given dancer
sem_t *toWatchSemaphores;

// Semaphore for audience members now watching the dancers
sem_t nowWatchingSemaphore;

sem_t leaveTogetherSemaphore;

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
    for(i = 0; i != nDancers; i++) {
        toWatch[i] = 0;
    }

    validRequest = malloc(nDancers * sizeof(bool));
    for(i = 0; i != nDancers; i++) {
        validRequest[i] = false;
    }

    // Set up semaphores
    toWatchSemaphores = malloc(nDancers * sizeof(sem_t));
    for(i = 0; i != nDancers; i++) {
        printf("Initialising semaphore %d\n", i);
        if(sem_init(&toWatchSemaphores[i], 0, 0)) {
            printf("***** Could not initialise semaphore: %d\n", i);
            exit(-1);
        }
    }
    sem_init(&nowWatchingSemaphore, 0, 0);
    sem_init(&leaveTogetherSemaphore, 0, 0);

    // Set up mutexes
    watchMutexes = malloc(nDancers * sizeof(pthread_mutex_t));
    for (i = 0; i != nDancers; i++) {
        pthread_mutex_init(&watchMutexes[i], NULL);
    }

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

long randomDancer() {
    return rand() % (nDancers);
}

void *runDancer(void *idPtr) {
    long id = (long)idPtr;
    unsigned int nWatching = 0;
    bool validRequestsExist = false;

    while (1) {
        //Lock to prevent > 2 dancers being selected
        pthread_mutex_lock(&selectDancerMutex);
            if (dancerAged == NO_DANCER || dancerProOrAged == NO_DANCER) {
                //Check if there are any valid requests for dancers
                validRequestsExist = false;
                int i;
                for (i = 0; i != nDancers; i++) {
                    validRequestsExist = validRequestsExist || validRequest[id];
                }

                //This dancer can be selected if there are currently no requests or if this dancer has been requested
                if (!validRequestsExist || validRequest[id]) {
                    if (id != previousAged && id != previousProOrAged) {
                        if (id < nAgedDancers && dancerAged == NO_DANCER) {
                            printf("%ld became new aged dancer\n", id);
                            dancerAged = id;
                        } else if (dancerProOrAged == NO_DANCER) {
                            //Handle special case where there are 2 aged dancers only. Prevents both dancing at same time
                            if (id >= nAgedDancers || (nAgedDancers > 2)) {
                                printf("%ld became new pro dancer\n", id);
                                dancerProOrAged = id;
                            } 
                        }
                    }
                    //Regardless of whether or not the request is fulfilled, the request is no longer valid
                    validRequest[id] = false;
                }
            }
        pthread_mutex_unlock(&selectDancerMutex);

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
        // Lock prevents audience members adding themselves while others are being signalled by runDancer()
        dancer = randomDancer();
        pthread_mutex_lock(&(watchMutexes[dancer]));
            toWatch[dancer]++;
            validRequest[dancer] = true;
            printf("Audience %ld: Selected to watch dancer: %ld\n", id, dancer);
        pthread_mutex_unlock(&(watchMutexes[dancer]));

        // Watch
        // Wait on semaphore until dancer starts dancing
        sem_wait(&toWatchSemaphores[dancer]);
        printf("Audience %ld: Now Watching dancer: %ld\n", id, dancer);

        // Observe leave
        // Wait on semaphore until dancer finishes dancing
        sem_wait(&nowWatchingSemaphore);
    }
    printf("Audience %ld: Finished %d rounds, dying now.\n", id, nRounds);
    
    return NULL;
}

