
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
int previousAged, previousProOrAged;

// Records critical section for dancer selections
int dancerCS;
int dancerProDone;

// Tokens for linear waiting in dancers
int tokenAged, tokenProOrAged;

// Count of waiting audience members waiting to see specific dancers
unsigned int *toWatch;

// Auxiliary counting to help track values in toWatch
int nWaiting, nAgedWaiting;

// Track number of audience members watching
int nWatching;

// Track number of dancers on stage
int nDancersOnStage, nAgedDancersOnStage;

// Mutex for changing variables associated with what audience members wish to watch
pthread_mutex_t toWatchMutex = PTHREAD_MUTEX_INITIALIZER;

// Dancer mutex for awaits
pthread_mutex_t dancerMutex = PTHREAD_MUTEX_INITIALIZER;

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

    // Initialise variables
    dancerAged = NO_DANCER;
    dancerProOrAged = NO_DANCER;
    previousAged = NO_DANCER;
    previousProOrAged = NO_DANCER;
    dancerCS = 0;
    dancerProDone = 0;
    tokenAged = 0;
    tokenProOrAged = 0;
    nWaiting = 0;
    nAgedWaiting = 0;
    nWatching = 0;
    nDancersOnStage = 0;
    nAgedDancersOnStage = 0;

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

void *runDancers(void* idPtr) {
    // Out dancer id - used to denote which dancer we are and if we are aged or not
    int id = (long) idPtr;

    // Is this dancer aged
    int isAged = ISAGEDDANCER(id);

    // Are we permitted to start dancing
    int canDance = 0;

    // Track number of waiting dancers
    int waiting;

    int awaitDone;

    printf("Starting Dancer thread: %d (Aged: %d)\n", id, isAged);

    while(1) {
        while (!canDance) {
            awaitDone = 0;
            while (!awaitDone) {
                pthread_mutex_lock(&dancerMutex);
                awaitDone = 
                (!dancerCS &&
                  (
                    (dancerAged == NO_DANCER && dancerProOrAged == NO_DANCER && tokenAged      == id) ||
                    (dancerAged != NO_DANCER && dancerProOrAged == NO_DANCER && tokenProOrAged == id)
                  )
                );
                pthread_mutex_unlock(&dancerMutex);
            }
            pthread_mutex_lock(&dancerMutex);
            printf("Dancer %d trying to dance\n", id);
            dancerCS = 1;

            // Check number of audience members waiting on dancers
            if (isAged && dancerAged == NO_DANCER) {
                waiting = nAgedWaiting;
            } else {
                waiting = nWaiting;
            }

            // Not previous dancer
            // Not previous dancer
            // Check against waiting audience
            if ( previousAged != id &&
                 previousProOrAged != id &&
                 ( toWatch[id] > 0 || waiting == 0 ) &&
                 ( nAgedDancers > 2 || isAged == 0 || dancerAged == NO_DANCER )
                ) {
                canDance = 1;
            } else {
                if (dancerAged == NO_DANCER) {
                    tokenAged = NEXTDANCER(tokenAged, nAgedDancers);
                } else {
                    tokenProOrAged = NEXTDANCER(tokenProOrAged, nDancers);
                    while (tokenProOrAged == dancerAged) tokenProOrAged = NEXTDANCER(tokenProOrAged, nDancers);
                }

                printf("Cannot Dance: %d. New token: Aged: %d Pro: %d\n",
                       id, tokenAged, tokenProOrAged);
                dancerCS = 0;
                pthread_mutex_unlock(&dancerMutex);
            }
        }

        // We are now dancer on stage (Dancer CS)
        //printf("Dancer: %d CS\n", id);
        assert(dancerAged == NO_DANCER || dancerProOrAged == NO_DANCER);
        canDance = 0;
        if (dancerAged == NO_DANCER) {
            dancerAged = id;
            if (tokenProOrAged == id) tokenProOrAged = NEXTDANCER(tokenProOrAged, nDancers);
            printf("Dancer %d now aged dancer\n", id);
        } else {
            dancerProOrAged = id;
            printf("Dancer %d now pro dancer\n", id);
        }
        // Wait for all dancers to continue
        AWAIT( toWatch[id] == 0 );
        assert(nDancersOnStage == 0);
        assert(nAgedDancersOnStage == 0);
            //printf("Dancer %d: aged: %d pro: %d nAged: %d, nDancers: %d currDancing: %d\n",
            //       id, dancerAged, dancerProOrAged, nAgedDancersOnStage, nDancersOnStage, currentlyDancing);
        dancerCS = 0;
        pthread_mutex_unlock(&dancerMutex);

        // Wait for partner
        AWAIT( !dancerCS && dancerAged != NO_DANCER && dancerProOrAged != NO_DANCER );
        nDancersOnStage++;
        if (isAged) nAgedDancersOnStage++;

        // Dance!
        AWAIT( nDancersOnStage == 2 && !dancerCS );
        printf("*** Now dancing on stage: Aged dancer: %d(%d), "
               "Pro or aged dancer: %d(%d), Num Dancers: %d, "
               "TokenAged: %d TokenPro: %d\n",
               dancerAged, ISAGEDDANCER(dancerAged), dancerProOrAged,
               ISAGEDDANCER(dancerProOrAged), nDancersOnStage,
               tokenAged, tokenProOrAged);
        assert(dancerCS == 0);
        assert(nDancersOnStage == 2);
        assert(nAgedDancersOnStage >= 1);
        assert(dancerAged < nAgedDancers);
        assert(dancerAged != previousAged);
        assert(dancerProOrAged != previousProOrAged);
        assert(tokenAged == dancerAged);
        assert(tokenProOrAged == dancerProOrAged);
        usleep(SEC2USEC(1));
        printf("*** Dancer %d finished\n", id);

        // Leave dancing (just let one dancer do the cleanup)
        if (dancerProOrAged == id) {
            dancerProDone = 1;
        } else if (dancerAged == id) {
            // Wait for pro dancer
            pthread_mutex_lock(&dancerMutex);
            AWAIT( dancerProDone == 1 );
            dancerCS = 1;
                
                // Alter dancers on stage
                previousAged = dancerAged;
                previousProOrAged = dancerProOrAged;
                dancerAged = NO_DANCER;
                dancerProOrAged = NO_DANCER;

                // Wait on audience to stop watching
                AWAIT( nWatching == 0 );

                // Clear other variables
                dancerProDone = 0;
                nDancersOnStage = 0;
                nAgedDancersOnStage = 0;

                // Update tokens away from current dancers
                tokenAged = NEXTDANCER(tokenAged, nAgedDancers);
                tokenProOrAged = NEXTDANCER(tokenProOrAged, nDancers);
                printf("Aged %d finished\n", id);

            dancerCS = 0;
            pthread_mutex_unlock(&dancerMutex);
        }
    }

    return NULL;
}

void *runAudience(void* idPtr) {
    int id = (long) idPtr;
    int sleepDuration = 1000;
    int roundsCompleted = 0;
    int dancer = NO_DANCER;
    int isAged = 0;

    for (roundsCompleted = 0; roundsCompleted != nRounds || nRounds == 0; roundsCompleted++) {
        // Vegetate
        printf("Audience %d: Beginning vegetation \n", id);
        sleepDuration = rand() % SEC2USEC(10);
        printf("Audience %d: Sleeping for %.2lf seconds\n", id, USEC2SEC(sleepDuration));
        usleep(sleepDuration);
        //usleep(SEC2USEC(20));
          
        // Select Dancer (Do this with d_step in promela)
        dancer = randomDancer();
        isAged = ISAGEDDANCER(dancer);
        pthread_mutex_lock(&toWatchMutex);
            toWatch[dancer]++;
            nWaiting++;
            if (isAged) nAgedWaiting++;
            printf("### Audience %d: Selected to watch dancer: %d (Aged: %d)\n", id, dancer, isAged);
        pthread_mutex_unlock(&toWatchMutex);

        // Wait for dancer to appear on stage (Do this with d_step in promela)
        AWAIT(dancerAged == dancer || dancerProOrAged == dancer);
        pthread_mutex_lock(&toWatchMutex);
            toWatch[dancer]--;
            nWaiting--;
            if (isAged) nAgedWaiting--;
            nWatching++;
        pthread_mutex_unlock(&toWatchMutex);
        printf("Audience %d: Watching Dancer %d\n", id, dancer);

        // Observe leave (Do this with d_step in promela)
        AWAIT(dancerAged != dancer && dancerProOrAged != dancer);
        pthread_mutex_lock(&toWatchMutex);
            nWatching--;
        pthread_mutex_unlock(&toWatchMutex);
        printf("Audience %d: Watched Dancer %d leave stage\n", id, dancer);
    }

    printf("Audience %d: Finished %d rounds, dying now.\n", id, nRounds);
    
    return NULL;
}

