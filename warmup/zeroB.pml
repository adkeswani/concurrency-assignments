#include "fdef.h"

bool found = false;

proctype P() {
    byte i = 0;

    do
        :: (found) -> break
        :: else ->
            i = i + 1;
            found = (f(i) == 0)
    od
}

proctype Q() {
    byte j = 1;

    do
        :: (found) -> break
        :: else ->
            j = j - 1;
            found = (f(j) == 0)
    od
}

init {
    atomic {
        run P();
        run Q()
    }   
}
