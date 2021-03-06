#include "fdef.h"

bool found = false;

proctype P() {
    byte i = 0;

    do
        :: (found) -> break
        :: else ->
            i = i + 1;
            if
                :: f(i) == 0 -> found = true
            fi
    od
}

proctype Q() {
    byte j = 1;

    do
        :: (found) -> break
        :: else ->
            j = j - 1;
            if
                :: f(j) == 0 -> found = true
            fi
    od
}

init {
    atomic {
        run P();
        run Q()
    }   
}

ltl p0 { [] ( ( <> found ) && ( found -> [] found ) ) }
