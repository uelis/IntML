#include <stdlib.h>
#include <stdbool.h>
#include <malloc.h>

#define BLOCKSIZE 200
#define NBLOCKS 10000000

void *mem;
void* freestack[NBLOCKS];
int stacktop;

void *ualloc(int size) {
  static bool init = false;
  if (!init) {
    mem = malloc(NBLOCKS * BLOCKSIZE);
    stacktop = 0;
    for (int i = 0; i < NBLOCKS; i++) {
      freestack[i] = mem + i * BLOCKSIZE;
      stacktop = i;
    }
    init = true;
  }
  if (stacktop == 0) {
    printf("oom\n");
    exit(1);
  }
//  printf("st: %i\n", stacktop);
  return freestack[stacktop--];
}

void ufree(void *mem) {
  freestack[++stacktop] = mem;
}

