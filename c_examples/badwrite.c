#include "rt.h"

#define RAM_SIZE (1 << 30)
#define HEAP_ADDR (void *)(RAM_SIZE)

void func(unsigned int *count) { (*count)++; }

Result main() {
  void *heap = HEAP_ADDR;
  unsigned int *values = (unsigned int *)heap;

  // Vali        d wr        ite!
  // 0x696c6156  0x72772064  0x21657469
  unsigned int *valid = values - 5;
  valid[0] = 0x696c6156;
  valid[1] = 0x72772064;
  valid[2] = 0x21657469;

  // Hell        o fr        om t        he G        uest
  // 0x6c6c6548  0x7266206f  0x74206d6f  0x47206568  0x74736575
  values[1] = 0x6c6c6548;
  values[2] = 0x7266206f;
  values[3] = 0x74206d6f;
  values[4] = 0x47206568;
  values[5] = 0x74736575;

  return success(values[0], values[10], values[20], values[30], values[40],
                 values[50], values[60], values[70]);
}
