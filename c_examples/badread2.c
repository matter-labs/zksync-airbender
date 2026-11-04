#include "rt.h"

#define RAM_SIZE (1 << 30)
#define HEAP_ADDR (void *)(RAM_SIZE)

void func(unsigned int *count) { (*count)++; }

Result main() {
  void *heap = HEAP_ADDR;
  unsigned int *values = (unsigned int *)heap;

  return success(values[0], values[10], values[20], values[30], values[40],
                 values[50], values[60], values[70]);
}
