#include "rt.h"

#define HEAP_ADDR (void *)0x04000000

void func(unsigned int *count) { (*count)++; }

Result main() {
  void *heap = HEAP_ADDR;
  // unsigned int *count = (unsigned int *)heap;
  void (*f)() = (void (*)())(heap);

  (*f)();

  return success(0, 0, 0, 0, 0, 0, 0, 0);
}
