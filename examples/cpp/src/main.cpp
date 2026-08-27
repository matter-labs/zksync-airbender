#include <stdint.h>

#include "app.hpp"

extern "C" {
// Boundaries of the heap
extern uint32_t _sheap;
extern uint32_t _eheap;

// Boundaries of the stack
extern uint32_t _sstack;
extern uint32_t _estack;

// Boundaries of the .data section (and it's part in ROM)
extern uint32_t _sidata;
extern uint32_t _sdata;
extern uint32_t _edata;

// Boundaries of the .bss section
extern uint32_t _sbss;
extern uint32_t _ebss;

// Boundaries of the .rodata section
extern uint32_t _sirodata;
extern uint32_t _srodata;
extern uint32_t _erodata;

#if defined(AIRBENDER_USE_NEWLIB)
void __libc_init_array();
#endif
}

extern "C" void eh_personality() {}

struct MachineTrapFrame {
    uint32_t registers[32];
};

extern "C" [[noreturn]] void _start_rust() __attribute__((section(".init.rust")));
extern "C" uint32_t _machine_start_trap_rust(MachineTrapFrame*) __attribute__((section(".trap.rust")));

namespace {

// =============================================================================
// ROM -> RAM relocation helpers
// =============================================================================
//
// The linker keeps initial bytes for .rodata/.data in ROM and maps their final
// addresses into RAM. We copy these ranges first so global/static state is
// valid before C++ runtime initialization.

static void copy_section(const uint8_t* src, uint8_t* dst, const uint8_t* end) {
    while (dst < end) {
        *dst++ = *src++;
    }
}

static void zero_section(uint8_t* start, const uint8_t* end) {
    while (start < end) {
        *start++ = 0;
    }
}

static void init_memory() {
    // Copy .rodata section from ROM to RAM
    const uint8_t* sirodata = reinterpret_cast<const uint8_t*>(&_sirodata);
    uint8_t* srodata = reinterpret_cast<uint8_t*>(&_srodata);
    const uint8_t* erodata = reinterpret_cast<const uint8_t*>(&_erodata);
    if (srodata < erodata) {
        copy_section(sirodata, srodata, erodata);
    }

    // Copy .data section from ROM to RAM
    uint8_t* sdata = reinterpret_cast<uint8_t*>(&_sdata);
    const uint8_t* edata = reinterpret_cast<const uint8_t*>(&_edata);
    if (sdata < edata) {
        copy_section(reinterpret_cast<const uint8_t*>(&_sidata), sdata, edata);
    }

    // Zero .bss so C/C++ static storage starts from a deterministic state.
    uint8_t* sbss = reinterpret_cast<uint8_t*>(&_sbss);
    const uint8_t* ebss = reinterpret_cast<const uint8_t*>(&_ebss);
    if (sbss < ebss) {
        zero_section(sbss, ebss);
    }
}

} // namespace

extern "C" [[noreturn]] void _start_rust() {
    // Bring RAM-backed sections to their runtime state before any library code
    // observes globals.
    init_memory();
#if defined(AIRBENDER_USE_NEWLIB)
    // Initialize constructors and libc internals before app code uses the
    // standard library (stdio wrappers, exit handlers, etc.).
    __libc_init_array();
#endif
    app_entrypoint();
}

extern "C" uint32_t _machine_start_trap_rust(MachineTrapFrame*) {
    while (true) {
    }
}
