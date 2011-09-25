
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <assert.h>

#include <pthread.h>

// Constants
#define NO_DANCER       -1
#define N_PRO_DANCERS_ARG  1
#define N_AGED_DANCERS_ARG 2
#define N_AUDIENCE_ARG 3
#define N_ROUNDS_ARG 4

// Macros
#define SEC2USEC(n)     (n * 1000000)
#define USEC2SEC(n)     (n / 1000000.0)
#define NEXTDANCER(n,mod)   ((n+1) % mod)
#define ISAGEDDANCER(n) (n < nAgedDancers)

// Simulates the await statement using a while loop and macro
#define AWAIT(n)    while(!(n));
#define AWAIT2(n,ss)    while(!(n)) {ss}

// Methods

// Randomly select a dancer
int randomDancer();

// Single Audience member
void *runAudience(void* id);

// Method for running dancer selection/dancing/leaving
void *runDancers(void* id);

// Determines if the dancer can continue selection based on those waiting
int continueToWatch(int aged);

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
int dancerAged, dancerProOrAged;

// Dancers currently on stage
int previousDancerAged, previousDancerProOrAged;

// Number of dancers currently on stage
int nDancersOnStage, nAgedDancersOnStage;

// Denotes if dacning is taking place
int currentlyDancing;

// Records critical section for dancer selections
int dancerCS;

// Tokens for linear waiting in dancers
int tokenAged, tokenAgedOrPro;

// Count of waiting audience members waiting to see specific dancers
unsigned int *toWatch;

// Mutex for changing variables associated with what audience members wish to watch
pthread_mutex_t toWatchMutex = PTHREAD_MUTEX_INITIALIZER;

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
    nDancersOnStage = 0;
    nAgedDancersOnStage = 0;
    currentlyDancing = 0;
    dancerAged = NO_DANCER;
    dancerProOrAged = NO_DANCER;
    previousDancerAged = NO_DANCER;
    previousDancerProOrAged = NO_DANCER;
    tokenAged = 0;
    tokenAgedOrPro = 0;
    dancerCS = 0;
    nDancers = nProDancers + nAgedDancers;
    printf("Number of pro dancers: %d\n", nProDancers);
    printf("Number of aged dancers: %d\n", nAgedDancers);
    printf("Number of audience members: %d\n", nAudience);
    printf("Number of rounds: %d\n", nRounds);

    // Sanity checks
    assert(nAgedDancers >= 2);
    assert(nDancers >= 4);

    // Init Random number generator
    srand(time(NULL));

    // Setup toWatch
    toWatch = malloc(nDancers * sizeof(unsigned int));
    for(i = 0; i != (nDancers); i++) {
        toWatch[i] = 0;
    }

    // Spawn audience threads
    pthread_t audience[nAudience];
    int rc;
    long t;
    for(t = 0; t != nAudience; t++) {
        printf("Creating audience thread %ld\n", t);
        rc = pthread_create(&audience[t], NULL, runAudience, (void *)t);
        if (rc) {
            printf("ERROR; return code from pthread_create() is %d\n", rc);
            exit(-1);
        }
    }

    // Spawn dancer threads
    pthread_t dancers[nDancers];
    for(t = 0; t != nDancers; t++) {
        printf("Creating Dancer thread %ld\n", t);
        rc = pthread_create(&dancers[t], NULL, runDancers, (void *)t);
        if (rc) {
            printf("ERROR; return code from pthread_create() is %d\n", rc);
            exit(-1);
        }
    }

    pthread_exit(NULL);
}

int randomDancer() {
    return rand() % (nDancers);
}

int continueToWatch(int aged) {
    int waiting = 0;

    // Set iteration limit based on aged/non-aged dancers
    int limit = nDancers;
    if (aged && nAgedDancersOnStage == 0) {
        limit = nAgedDancers;
    }

    int i = 0;
    for (i = 0; i != limit; i++) {
        if (i != previousDancerAged && i != previousDancerProOrAged) {
            waiting += toWatch[i];
        }
    }

    return waiting == 0;
}

void *runDancers(void* idPtr) {
    // Out dancer id - used to denote which dancer we are and if we are aged or not
    int id = (long) idPtr;

    // Is this dancer aged
    int isAged = ISAGEDDANCER(id);

    // Are we permitted to start dancing
    int canDance = 0;

    printf("Starting Dancer thread: %d (Aged: %d)\n", id, isAged);

    while(1) {
        while (!canDance) {
            // Wait for it to be our turn in selecting (gives linear waiting)
            AWAIT(!currentlyDancing && !dancerCS &&
                  (
                    (dancerAged == NO_DANCER && tokenAged      == id) ||
                    (dancerAged != NO_DANCER && tokenAgedOrPro == id)
                  )
                  //printf("Dancer:%d tokenAged: %d, tokenPro: %d currDan: %d, dancerCS: %d dancerAged: %d\n", 
                  //       id, tokenAged, tokenAgedOrPro, currentlyDancing, dancerCS, dancerAged);
                  );

            printf("Dancer %d trying to dance\n", id);

            // Not a current dancer
            // Not previous dancer
            // Not previous dancer
            // Check against waiting audience
            if (
                  dancerAged != id &&
                  dancerProOrAged != id &&
                  previousDancerAged != id &&
                  previousDancerProOrAged != id &&
                  ( toWatch[id] > 0 || continueToWatch(isAged) )
                ) {
                canDance = 1;
            } else {
                if (dancerAged == NO_DANCER) {
                    tokenAged = NEXTDANCER(tokenAged, nAgedDancers);
                } else {
                    tokenAgedOrPro = NEXTDANCER(tokenAgedOrPro, nDancers);
                    while (tokenAgedOrPro == dancerAged) tokenAgedOrPro = NEXTDANCER(tokenAgedOrPro, nDancers);
                }
            }
        }

        // We are now dancer on stage (Dancer CS)
        dancerCS = 1;
            //printf("Dancer: %d CS\n", id);
            assert(dancerAged == NO_DANCER || dancerProOrAged == NO_DANCER);
            if (dancerAged == NO_DANCER) {
                dancerAged = id;
                if (tokenAgedOrPro == id) tokenAgedOrPro = NEXTDANCER(tokenAgedOrPro, nDancers);
                printf("Dancer %d now aged dancer\n", id);
            } else {
                dancerProOrAged = id;
                printf("Dancer %d now pro dancer\n", id);
            }
            if (isAged) nAgedDancersOnStage++;
            nDancersOnStage++;

            // Finished setup (Finihsed Dancer CS)
            canDance = 0;
            if (nDancersOnStage == 2) currentlyDancing = 1;
            //printf("Dancer %d: aged: %d pro: %d nAged: %d, nDancers: %d currDancing: %d\n",
            //       id, dancerAged, dancerProOrAged, nAgedDancersOnStage, nDancersOnStage, currentlyDancing);
        dancerCS = 0;

        // Dance!
        AWAIT(currentlyDancing && !dancerCS);
        printf("*** Now dancing on stage: Aged dancer: %d(%d), Pro or aged dancer: %d(%d), Num Dancers: %d \n",
               dancerAged, ISAGEDDANCER(dancerAged), dancerProOrAged, ISAGEDDANCER(dancerProOrAged), nDancersOnStage);
        usleep(SEC2USEC(5));
        printf("*** Dancer %d finished\n", id);

        // Leave dancing (just let one dancer do the cleanup)
        if (dancerProOrAged == id) {
            previousDancerProOrAged = dancerProOrAged;
            dancerProOrAged = NO_DANCER;
            tokenAgedOrPro = NEXTDANCER(tokenAgedOrPro, nDancers);
        if (dancerAged == id) {
            AWAIT( dancerProOrAged == NO_DANCER);

            previousDancerAged = dancerAged;
            dancerAged = NO_DANCER;
            tokenAged = NEXTDANCER(tokenAged, nAgedDancers);

            nDancersOnStage = 0;
            nAgedDancersOnStage = 0;
            currentlyDancing = 0;
        }
    }

    return NULL;
}

void *runAudience(void* idPtr) {
    int id = (long) idPtr;
    int sleepDuration = 1000;
    int roundsCompleted = 0;
    int dancer = NO_DANCER;

    for (roundsCompleted = 0; roundsCompleted != nRounds || nRounds == 0; roundsCompleted++) {
        // Vegetate
        printf("Audience %d: Beginning vegetation \n", id);
        sleepDuration = rand() % SEC2USEC(10);
        printf("Audience %d: Sleeping for %.2lf seconds\n", id, USEC2SEC(sleepDuration));
        usleep(sleepDuration);
        //usleep(SEC2USEC(20));
          
        // Select Dancer (Do this with atomic in promela)
        pthread_mutex_lock(&toWatchMutex);
            dancer = randomDancer();
            toWatch[dancer]++;
            printf("### Audience %d: Selected to watch dancer: %d\n", id, dancer);
        pthread_mutex_unlock(&toWatchMutex);

        // Wait for dancer to appear on stage (Do this with atomic in promela)
        AWAIT(dancerAged == dancer || dancerProOrAged == dancer);
        pthread_mutex_lock(&toWatchMutex);
            toWatch[dancer]--;
        pthread_mutex_unlock(&toWatchMutex);
        printf("Audience %d: Watching Dancer %d\n", id, dancer);

        // Observe leave
        AWAIT(dancerAged != dancer && dancerProOrAged != dancer);
        printf("Audience %d: Watched Dancer %d leave stage\n", id, dancer);
    }

    printf("Audience %d: Finished %d rounds, dying now.\n", id, nRounds);
    
    return NULL;
}

