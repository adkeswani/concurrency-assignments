#include "fdef.h"

bool foun = false

proctype P() {
    byte i = 0;
    fount = false;

    do
        :: (found) -> break
        :: else ->
            i = i + 1;
            found = (f(i) == 0)
    od
}

proctype Q() {
    byte j = 1;
    fount = false;

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
