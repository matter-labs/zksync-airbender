#ifndef _COMPLIANCE_MODEL_H
#define _COMPLIANCE_MODEL_H

#define RVMODEL_DATA_SECTION
// .pushsection.tohost, "aw", @progbits;                                        \
  // .align 8;                                                                    \
  // .global tohost;                                                              \
  // tohost:                                                                      \
  // .dword 0;                                                                    \
  // .align 8;                                                                    \
  // .global fromhost;                                                            \
  // fromhost:                                                                    \
  // .dword 0;                                                                    \
  // .popsection;

#ifdef RVTEST_SELFCHECK
#define RVMODEL_BOOT \
    la t1, signature_base_rom; \
    la t2, signature_end_rom; \
    la t3, signature_base; \
  1: \
    lw t4, 0(t1); \
    sw t4, 0(t3); \
    addi t1, t1, 4; \
    addi t3, t3, 4; \
    bltu t1, t2, 1b
#else
#define RVMODEL_BOOT
#endif



#define RVMODEL_ACCESS_FAULT_ADDRESS 0x00000000

// Lowercase 'a' in all output registers is a passing test.
#define RVMODEL_HALT_PASS                                                      \
  li x10, 97;                                                                  \
  li x11, 97;                                                                  \
  li x12, 97;                                                                  \
  li x13, 97;                                                                  \
  li x14, 97;                                                                  \
  li x15, 97;                                                                  \
  li x16, 97;                                                                  \
  li x17, 97;                                                                  \
  li x18, 0;                                                                   \
  li x19, 0;                                                                   \
  li x20, 0;                                                                   \
  li x21, 0;                                                                   \
  li x22, 0;                                                                   \
  li x23, 0;                                                                   \
  li x24, 0;                                                                   \
  li x25, 0;                                                                   \
  loop1:                                                                       \
  j loop1;

// Uppercase 'A' in all output registers is a failing test.
#define RVMODEL_HALT_FAIL                                                      \
  li x10, 65;                                                                  \
  li x11, 65;                                                                  \
  li x12, 65;                                                                  \
  li x13, 65;                                                                  \
  li x14, 65;                                                                  \
  li x15, 65;                                                                  \
  li x16, 65;                                                                  \
  li x17, 65;                                                                  \
  li x18, 0;                                                                   \
  li x19, 0;                                                                   \
  li x20, 0;                                                                   \
  li x21, 0;                                                                   \
  li x22, 0;                                                                   \
  li x23, 0;                                                                   \
  li x24, 0;                                                                   \
  li x25, 0;                                                                   \
  loop2:                                                                       \
  j loop2;

#define RVMODEL_IO_INIT(_R1, _R2, _R3)

#define RVMODEL_IO_WRITE_STR(_R1, _R2, _R3, _STR_PTR)

#define RVMODEL_MTIME_ADDRESS
// 0x0200BFF8

#define RVMODEL_MTIMECMP_ADDRESS
// 0x02004000

#define RVMODEL_SET_MEXT_INT(_R1, _R2)

#define RVMODEL_CLR_MEXT_INT(_R1, _R2)

#define RVMODEL_SET_MSW_INT(_R1, _R2)

#define RVMODEL_CLR_MSW_INT(_R1, _R2)

#define RVMODEL_SET_SEXT_INT(_R1, _R2)

#define RVMODEL_CLR_SEXT_INT(_R1, _R2)

#define RVMODEL_SET_SSW_INT(_R1, _R2)

#define RVMODEL_CLR_SSW_INT(_R1, _R2)

#endif // _COMPLIANCE_MODEL_H
