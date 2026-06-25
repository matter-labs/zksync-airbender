#ifndef _RT_H
#define _RT_H

typedef struct Result {
  unsigned int data[16];
} Result;

Result main();

Result success(unsigned int, unsigned int, unsigned int, unsigned int,
               unsigned int, unsigned int, unsigned int, unsigned int);

void write_csr_word(unsigned int word);

unsigned strlen(const char *);

#endif
