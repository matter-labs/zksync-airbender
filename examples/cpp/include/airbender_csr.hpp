#pragma once

#include <stdint.h>

namespace airbender {

constexpr uint32_t CSR_NON_DETERMINISM = 0x7C0;
constexpr uint32_t CSR_BLAKE2S = 0x7C7;
constexpr uint32_t CSR_BIGINT = 0x7CA;
constexpr uint32_t CSR_KECCAK_SPECIAL5 = 0x7CB;

#if defined(__riscv) && __riscv_xlen == 32

inline void csr_write_word(uint32_t value) {
    asm volatile("csrrw x0, 0x7C0, %0" :: "r"(value) : "memory");
}

inline uint32_t csr_read_word() {
    uint32_t out = 0;
    asm volatile("csrrw %0, 0x7C0, x0" : "=r"(out) :: "memory");
    return out;
}

inline void blake_trigger_reduced_rounds(uint32_t* state, const uint32_t* input, uint32_t mask) {
    register uintptr_t x10 asm("x10") = reinterpret_cast<uintptr_t>(state);
    register uintptr_t x11 asm("x11") = reinterpret_cast<uintptr_t>(input);
    register uint32_t x12 asm("x12") = mask;
    asm volatile(
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        : "+r"(x12)
        : "r"(x10), "r"(x11)
        : "memory"
    );
    (void)x12;
}

inline void blake_trigger_full_rounds(uint32_t* state, const uint32_t* input, uint32_t mask) {
    register uintptr_t x10 asm("x10") = reinterpret_cast<uintptr_t>(state);
    register uintptr_t x11 asm("x11") = reinterpret_cast<uintptr_t>(input);
    register uint32_t x12 asm("x12") = mask;
    asm volatile(
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        "csrrw x0, 0x7C7, x0\n"
        : "+r"(x12)
        : "r"(x10), "r"(x11)
        : "memory"
    );
    (void)x12;
}

inline uint32_t bigint_trigger(uint32_t* mut_ptr, const uint32_t* immut_ptr, uint32_t mask) {
    register uintptr_t x10 asm("x10") = reinterpret_cast<uintptr_t>(mut_ptr);
    register uintptr_t x11 asm("x11") = reinterpret_cast<uintptr_t>(immut_ptr);
    register uint32_t x12 asm("x12") = mask;
    asm volatile(
        "csrrw x0, 0x7CA, x0"
        : "+r"(x12)
        : "r"(x10), "r"(x11)
        : "memory"
    );
    return x12;
}

// Keccak delegation is disabled for now -- clang refuses to produce correct assembly
// for it. A better way would probably be to export it from Rust as a C function and link to it.
//
// inline uint32_t keccak_f1600_delegate(const uint32_t* state_ptr) {
//    TODO
// }

[[noreturn]] inline void finish_error() {
    asm volatile("csrrw x0, cycle, x0" ::: "memory");
    // Loop at the end. For some reason, C++ tries to optimize away the loop
    // in the release build, so we have to explicitly provide it as an assembly block.
    asm volatile(
        "1: j 1b\n"
    );
    while (true) {
    }
}

[[gnu::noinline]] [[noreturn]] inline void finish_success_extended(const uint32_t data[16]) {
    const uint32_t* ptr = data;
    asm volatile(
        "lw x10, 0(%0)\n"
        "lw x11, 4(%0)\n"
        "lw x12, 8(%0)\n"
        "lw x13, 12(%0)\n"
        "lw x14, 16(%0)\n"
        "lw x15, 20(%0)\n"
        "lw x16, 24(%0)\n"
        "lw x17, 28(%0)\n"
        "lw x18, 32(%0)\n"
        "lw x19, 36(%0)\n"
        "lw x20, 40(%0)\n"
        "lw x21, 44(%0)\n"
        "lw x22, 48(%0)\n"
        "lw x23, 52(%0)\n"
        "lw x24, 56(%0)\n"
        "lw x25, 60(%0)\n"
        :: "r"(ptr),
             "m"(*(const uint32_t (*)[16])ptr)
        : "x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17",
          "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "memory"
    );
    // Loop at the end. For some reason, C++ tries to optimize away the loop
    // in the release build, so we have to explicitly provide it as an assembly block.
    asm volatile(
        "1: j 1b\n"
    );
    while (true) {}
}

[[noreturn]] inline void finish_success(const uint32_t data[8]) {
    uint32_t extended[16] = {};
    for (int i = 0; i < 8; ++i) {
        extended[i] = data[i];
    }
    finish_success_extended(extended);
}

#else

inline void csr_write_word(uint32_t) {}
inline uint32_t csr_read_word() { return 0; }
inline void blake_trigger_reduced_rounds(uint32_t*, const uint32_t*, uint32_t) {}
inline void blake_trigger_full_rounds(uint32_t*, const uint32_t*, uint32_t) {}
inline uint32_t bigint_trigger(uint32_t*, const uint32_t*, uint32_t mask) { return mask; }
inline uint32_t keccak_f1600_delegate(const uint32_t*) { return 0; }
[[noreturn]] inline void finish_error() { while (true) {} }
[[noreturn]] inline void finish_success(const uint32_t[8]) { while (true) {} }
[[noreturn]] inline void finish_success_extended(const uint32_t[16]) { while (true) {} }

#endif

} // namespace airbender
