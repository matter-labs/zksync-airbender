#include "uart.h"
#include "rt.h"

void uart_print_msg(const char *msg) {
  write_csr_word(0xffffffff);
  unsigned len = strlen(msg);
  unsigned words = len / 4;
  if (len % 4 != 0) {
    words++;
  }
  write_csr_word(len);
  for (unsigned word = 0; word < words; word++) {
    unsigned *ptr = (unsigned *)msg;
    if (word * 4 < len) {
      write_csr_word(ptr[word]);
    }
  }
}
