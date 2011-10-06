
#define N_SENIORS 3

proctype senior(byte id) {
    printf("My id: %d\n", id);
}

init {
    atomic {
        run senior(0);
        run senior(1);
        run senior(2);
    }
}
