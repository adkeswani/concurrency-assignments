#include "fdef.h"

bool found = false;
byte turn = 1;

proctype P() {
    byte i = 0;
    
    do
        :: (found) -> break
        :: else ->
pTurnChange: 
            d_step { (turn == 1); turn = 2 }
pAfterTurnChange:
            i = i + 1;
            if
                :: (f(i) == 0) -> found = true
                :: else -> skip
            fi
    od;

    turn = 2;
}

proctype Q() {
    byte j = 1;
    
    do
        :: (found) -> break
        :: else ->
qTurnChange:
            d_step { (turn == 2); turn = 1 }
qAfterTurnChange:
            j = j - 1;
            if
                :: (f(j) == 0) -> found = true
                :: else -> skip
            fi
    od;

    turn = 1;
}

init {
    atomic {
        run P();
        run Q()
    }
}

ltl p0 { [] ( ( <> found ) && ( found -> [] found ) && ( P@pTurnChange -> <> P@pAfterTurnChange ) && ( Q@qTurnChange -> <> Q@qAfterTurnChange ) ) }
