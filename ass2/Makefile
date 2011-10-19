PROGRAM=lse

default: all

all: $(PROGRAM)

# Source files
SRCS=lseTim.c
OBJS=$(SRCS:.c=.o)

# Compilation variables
CC=mpicc
BUILDFLAGS=-g3 -Wall -Werror
CFLAGS+=$(BUILDFLAGS)
LDFLAGS+=-lpthread 

# Program build
$(PROGRAM): $(SRCS)
	@echo
	@echo Building $(PROGRAM)
	$(CC) $(BUILDFLAGS) $(LDFLAGS) -o $@ $^

# Clean
clean:
	rm -rf $(OBJS) $(PROGRAM)

