// Runtime file that defines the _start function.

#include "rt.h"

void _start_c() {
  Result result = main();
  unsigned int *ptr = result.data;
  asm("lw x10, 0(%0)\n\t"
      "lw x11, 4(%0)\n\t"
      "lw x12, 8(%0)\n\t"
      "lw x13, 12(%0)\n\t"
      "lw x14, 16(%0)\n\t"
      "lw x15, 20(%0)\n\t"
      "lw x16, 24(%0)\n\t"
      "lw x17, 28(%0)\n\t"
      "lw x18, 32(%0)\n\t"
      "lw x19, 36(%0)\n\t"
      "lw x20, 40(%0)\n\t"
      "lw x21, 44(%0)\n\t"
      "lw x22, 48(%0)\n\t"
      "lw x23, 52(%0)\n\t"
      "lw x24, 56(%0)\n\t"
      "lw x25, 60(%0)\n\t"
      :
      : "r"(ptr)
      : "x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17", "x18", "x19",
        "x20", "x21", "x22", "x23", "x24", "x25");

  for (;;) {
  }
  __builtin_unreachable();
}

void write_csr_word(unsigned int word) {
  // csrrw x0, 0x7c0, {rd}
  asm("csrrw x0, 0x7c0, %0" : : "r"(word) : "x0");
}

void *memset(void *b, int c, unsigned int len) {
  for (int i = 0; i < len; i++) {
    *(((unsigned char *)b) + i) = (unsigned char)c;
  }
  return b;
}

Result success(unsigned int d0, unsigned int d1, unsigned int d2,
               unsigned int d3, unsigned int d4, unsigned int d5,
               unsigned int d6, unsigned int d7) {
  return (Result){.data = {d0, d1, d2, d3, d4, d5, d6, d7}};
}

unsigned strlen(const char *s) {
  unsigned i = 0;
  for (; s[i] != '\0'; i++) {
  }

  return i;
}
