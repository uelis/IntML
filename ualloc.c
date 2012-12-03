#include <stdlib.h>
#include <stdbool.h>
#include <malloc.h>

#define BLOCKSIZE 27
#define NBLOCKS 1000

void *mem;
void* freestack[NBLOCKS];
int stacktop;
int nnn;

void *uinit(int size) {
    mem = malloc(NBLOCKS * BLOCKSIZE);
}

void *ualloc(int size) {
  mem += BLOCKSIZE;
  return mem;
}

void ufree(void *mem) {
  mem -= BLOCKSIZE;
}
