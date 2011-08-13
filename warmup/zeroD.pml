#include "fdef.h"

bool found = false;
byte turn = 1;

proctype P() {
    byte i = 0;
    
    do
        :: (found) -> break
        :: else ->
            pTurnA: (turn == 1);
            pTurnB: turn = 2;

            i = i + 1;

            if
                :: (f(i) == 0) -> found = true
                :: else -> skip
            fi
    od
}

proctype Q() {
    byte j = 1;
    
    do
        :: (found) -> break
        :: else ->
            qTurnA: (turn == 2);
            qTurnB: turn = 1;
    
            j = j - 1;
    
            if
                :: (f(j) == 0) -> found = true
                :: else -> skip
            fi
    od
}

init {
    atomic {
        run P();
        run Q()
    }
}

ltl p0 { [] ( ( <> found ) && ( found -> [] found ) && ( P@pTurnA -> <> P@pTurnB ) && ( Q@qTurnA -> <> Q@qTurnB ) ) }
