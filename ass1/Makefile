PROGRAM=scs

default: all

all: $(PROGRAM)

# Source files
SRCS=scs.c
OBJS=$(SRCS:.c=.o)

# Compilation variables
CC=gcc
BUILDFLAGS=-g3 -Wall -Werror
CFLAGS+=$(BUILDFLAGS)
LDFLAGS+=-lpthread -lrt

# Program build
$(PROGRAM): $(OBJS)
	@echo
	@echo Building $(PROGRAM)
	$(CC) $(BUILDFLAGS) $(LDFLAGS) -o $@ $^

# Clean
clean:
	rm -rf $(OBJS) $(PROGRAM)

