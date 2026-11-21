#![cfg_attr(not(test), no_std)]

#[cfg(feature = "checked_word_memory")]
mod checked_word;
mod memcpy;
mod memmove;
mod memset;
pub mod zk_masking;

// The checked runtime replaces riscv_common's own exports; without them the guest would link
// compiler_builtins' byte-wise fallbacks, and the precompile path is not word-checked.
#[cfg(all(
    target_arch = "riscv32",
    feature = "checked_word_memory",
    any(
        feature = "no_memcpy_override",
        feature = "no_memmove_override",
        feature = "no_memset_override",
        feature = "memcpy_via_precompile"
    )
))]
compile_error!(
    "checked_word_memory needs riscv_common's memcpy/memmove/memset exports and excludes memcpy_via_precompile"
);

// The checked word-memory build is exercised by the verifier guests.
#[cfg(all(test, not(feature = "checked_word_memory")))]
mod tests;

#[cfg(all(target_arch = "riscv32", feature = "boot_sequence"))]
pub mod boot_sequence;

/// Execution ROM of this guest; the circuit being verified can use a different ROM.
#[cfg(target_arch = "riscv32")]
pub const GUEST_ROM_GEOMETRY: common_constants::RomGeometry =
    if cfg!(feature = "ram_16mb_no_heap_wrap") {
        common_constants::L1_WRAP_ROM
    } else {
        common_constants::REGULAR_ROM
    };

/// Exit sequence produced by `zksync_os_finish_success_extended`
pub const EXIT_SEQUENCE: &[u32] = &[
    0x000d2503, //	lw	a0, 0x0(s10)
    0x004d2583, //	lw	a1, 0x4(s10)
    0x008d2603, //	lw	a2, 0x8(s10)
    0x00cd2683, //	lw	a3, 0xc(s10)
    0x010d2703, //	lw	a4, 0x10(s10)
    0x014d2783, //	lw	a5, 0x14(s10)
    0x018d2803, //	lw	a6, 0x18(s10)
    0x01cd2883, //	lw	a7, 0x1c(s10)
    0x020d2903, //	lw	s2, 0x20(s10)
    0x024d2983, //	lw	s3, 0x24(s10)
    0x028d2a03, //	lw	s4, 0x28(s10)
    0x02cd2a83, //	lw	s5, 0x2c(s10)
    0x030d2b03, //	lw	s6, 0x30(s10)
    0x034d2b83, //	lw	s7, 0x34(s10)
    0x038d2c03, //	lw	s8, 0x38(s10)
    0x03cd2c83, //	lw	s9, 0x3c(s10)
    0x0000006f, //	loop
];

/// Tail of `finish_execution_recursion_extended`: all the registers outside of x10-x28 are
/// zeroed, then the loop that an execution ends on.
pub const RECURSION_EXIT_TAIL_SEQUENCE: &[u32] = &[
    0x00000093, //	li	ra, 0
    0x00000113, //	li	sp, 0
    0x00000193, //	li	gp, 0
    0x00000213, //	li	tp, 0
    0x00000293, //	li	t0, 0
    0x00000313, //	li	t1, 0
    0x00000393, //	li	t2, 0
    0x00000413, //	li	s0, 0
    0x00000493, //	li	s1, 0
    0x00000e93, //	li	t4, 0
    0x00000f13, //	li	t5, 0
    0x00000f93, //	li	t6, 0
    0x0000006f, //	loop
];

#[cfg(target_arch = "riscv32")]
#[inline(always)]
/// Writes a given word into CRS register.
pub fn csr_write_word(word: usize) {
    unsafe {
        core::arch::asm!(
            "csrrw x0, 0x7c0, {rd}",
            rd = in(reg) word,
            options(nomem, nostack, preserves_flags)
        )
    }
}

#[cfg(target_arch = "riscv32")]
#[inline(always)]
/// Reads a word from CRS register.
pub fn csr_read_word() -> u32 {
    let mut output;
    unsafe {
        core::arch::asm!(
            "csrrw {rd}, 0x7c0, x0",
            rd = out(reg) output,
            options(nomem, nostack, preserves_flags)
        );
    }

    output
}

/// Reverses the byte order of a word (`u32::swap_bytes`) in a single cycle.
///
/// Emits Zbb `rev8`. airbender supports `rev8` but not the rest of Zbb, so guests can't
/// build with `+zbb`; `.option arch` enables the mnemonic locally instead.
#[cfg(target_arch = "riscv32")]
#[inline(always)]
pub fn byte_swap(value: u32) -> u32 {
    let mut output;
    unsafe {
        core::arch::asm!(
            ".option push",
            ".option arch, +zbb",
            "rev8 {rd}, {rs1}",
            ".option pop",
            rs1 = in(reg) value,
            rd = lateout(reg) output,
            options(pure, nomem, nostack, preserves_flags)
        );
    }

    output
}

/// Reverses the byte order of a word (`u32::swap_bytes`). Host fallback for the
/// airbender `rev8` implementation.
#[cfg(not(target_arch = "riscv32"))]
#[inline(always)]
pub fn byte_swap(value: u32) -> u32 {
    value.swap_bytes()
}

#[cfg(target_arch = "riscv32")]
#[no_mangle]
pub fn rust_abort() -> ! {
    zksync_os_finish_error()
}

/// Set data as a output of the current execution. Unsatisfiable in circuits
#[cfg(target_arch = "riscv32")]
#[inline(never)]
pub fn zksync_os_finish_error() -> ! {
    unsafe {
        core::arch::asm!(
            "csrrw x0, cycle, x0",
            options(nomem, nostack, preserves_flags)
        );
        core::hint::unreachable_unchecked();
    }
}

/// Set data as a output of the current execution.
/// Allows program to pass up to 8 integers as output values.
///
/// By convention, the data that is stored in registers 10-17 after
/// execution has finished is considered 'output' of the computation.
/// Registers 18-25 will be set to 0 as our convention for recursive chain start
#[cfg(target_arch = "riscv32")]
#[inline(never)]
pub fn zksync_os_finish_success(data: &[u32; 8]) -> ! {
    let mut result = [0u32; 16];
    result[..8].copy_from_slice(data);
    zksync_os_finish_success_extended(&result)
}

/// Set data as a output of the current execution.
/// By convention, the data that is stored in registers 10-25 after
/// execution has finished is considered 'output' of the computation.
#[cfg(target_arch = "riscv32")]
#[inline(never)]
pub fn zksync_os_finish_success_extended(data: &[u32; 16]) -> ! {
    let data_ptr = core::hint::black_box(data.as_ptr().cast::<u32>());
    unsafe {
        core::arch::asm!(
            "lw x10, 0(x26)",
            "lw x11, 4(x26)",
            "lw x12, 8(x26)",
            "lw x13, 12(x26)",
            "lw x14, 16(x26)",
            "lw x15, 20(x26)",
            "lw x16, 24(x26)",
            "lw x17, 28(x26)",
            "lw x18, 32(x26)",
            "lw x19, 36(x26)",
            "lw x20, 40(x26)",
            "lw x21, 44(x26)",
            "lw x22, 48(x26)",
            "lw x23, 52(x26)",
            "lw x24, 56(x26)",
            "lw x25, 60(x26)",
            in("x26") data_ptr,
            out("x10") _,
            out("x11") _,
            out("x12") _,
            out("x13") _,
            out("x14") _,
            out("x15") _,
            out("x16") _,
            out("x17") _,
            out("x18") _,
            out("x19") _,
            out("x20") _,
            out("x21") _,
            out("x22") _,
            out("x23") _,
            out("x24") _,
            out("x25") _,
            options(nostack, preserves_flags)
        )
    }
    loop {
        continue;
    }
}

/// Exit point of a recursion step, with zero-knowledge masking of the trace.
///
/// Puts `data` into registers 10-25 and `rec_counters` into registers 26-28, then runs the
/// masking sequence of [`zk_masking`]: one oracle query, whose response it consumes as operands
/// and as stores of random words to oracle-chosen addresses, so nothing may read memory after
/// this point. Then it zeroes every other register, so that no masking value survives into the
/// final register state, and ends on an explicit infinite loop, see
/// [`RECURSION_EXIT_TAIL_SEQUENCE`].
#[cfg(target_arch = "riscv32")]
#[inline(never)]
pub fn finish_execution_recursion_extended(data: &[u32; 16], rec_counters: &[u32; 3]) -> ! {
    unsafe {
        core::arch::asm!(
            "lw x10, 0(t0)",
            "lw x11, 4(t0)",
            "lw x12, 8(t0)",
            "lw x13, 12(t0)",
            "lw x14, 16(t0)",
            "lw x15, 20(t0)",
            "lw x16, 24(t0)",
            "lw x17, 28(t0)",
            "lw x18, 32(t0)",
            "lw x19, 36(t0)",
            "lw x20, 40(t0)",
            "lw x21, 44(t0)",
            "lw x22, 48(t0)",
            "lw x23, 52(t0)",
            "lw x24, 56(t0)",
            "lw x25, 60(t0)",
            "lw x26, 0(t1)",
            "lw x27, 4(t1)",
            "lw x28, 8(t1)",
            zk_masking::masking_sequence_asm!(),
            "li x1, 0",
            "li x2, 0",
            "li x3, 0",
            "li x4, 0",
            "li x5, 0",
            "li x6, 0",
            "li x7, 0",
            "li x8, 0",
            "li x9, 0",
            "li x29, 0",
            "li x30, 0",
            "li x31, 0",
            "5:",
            "j 5b",
            in("t0") data.as_ptr(),
            in("t1") rec_counters.as_ptr(),
            masking_query_id = const zk_masking::MASKING_QUERY_ID,
            masking_oracle_words = const zk_masking::ORACLE_WORDS,
            masking_iterations = const zk_masking::ITERATIONS,
            options(noreturn)
        )
    }
}

#[cfg(all(target_arch = "riscv32", not(feature = "custom_panic")))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    rust_abort();
}

#[derive(Clone, Copy, Debug, Default)]
pub struct NullAllocator;

unsafe impl core::alloc::GlobalAlloc for NullAllocator {
    unsafe fn alloc(&self, _layout: core::alloc::Layout) -> *mut u8 {
        core::hint::unreachable_unchecked()
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: core::alloc::Layout) {
        core::hint::unreachable_unchecked()
    }

    unsafe fn realloc(
        &self,
        _ptr: *mut u8,
        _layout: core::alloc::Layout,
        _new_size: usize,
    ) -> *mut u8 {
        core::hint::unreachable_unchecked()
    }
}

#[cfg(all(target_arch = "riscv32", not(feature = "custom_allocator")))]
#[global_allocator]
static GLOBAL_ALLOCATOR_PLACEHOLDER: NullAllocator = NullAllocator;

#[cfg(all(target_arch = "riscv32", feature = "uart"))]
#[derive(Default)]
#[repr(C, align(4))]
pub struct QuasiUART {
    buffer: [u8; 4],
    len: usize,
}

#[cfg(all(target_arch = "riscv32", feature = "uart"))]
impl QuasiUART {
    const HELLO_MARKER: u32 = u32::MAX;

    #[inline(never)]
    pub const fn new() -> Self {
        Self {
            buffer: [0u8; 4],
            len: 0,
        }
    }

    pub fn write_entry_sequence(&mut self, message_len: usize) {
        csr_write_word(Self::HELLO_MARKER as usize);
        // now write length is words for query
        csr_write_word(message_len.next_multiple_of(4) / 4 + 1);
        csr_write_word(message_len);
    }

    pub fn write_word(&self, word: u32) {
        csr_write_word(word as usize);
    }

    pub fn read_word(&self) -> usize {
        csr_read_word() as usize
    }

    fn write_byte(&mut self, byte: u8) {
        self.buffer[self.len] = byte;
        self.len += 1;
        if self.len == 4 {
            self.len = 0;
            let word = u32::from_le_bytes(self.buffer);
            self.write_word(word);
        }
    }

    fn flush(&mut self) {
        if self.len == 0 {
            // cleanup and return
            for dst in self.buffer.iter_mut() {
                *dst = 0;
            }
            return;
        }
        for i in self.len..4 {
            self.buffer[i] = 0u8;
        }
        self.len = 0;
        csr_write_word(u32::from_le_bytes(self.buffer) as usize);
    }

    #[inline(never)]
    pub fn write_debug<T: core::fmt::Debug>(value: &T) {
        use core::fmt::Write;
        let mut writer = Self::new();
        let mut string = heapless::String::<64>::new(); // 64 byte string buffer
        let Ok(_) = write!(string, "{:?}", value) else {
            let _ = writer.write_str("too long debug");
            return;
        };
        let _ = writer.write_str(&string);
    }
}

#[cfg(all(target_arch = "riscv32", feature = "uart"))]
impl core::fmt::Write for QuasiUART {
    fn write_str(&mut self, s: &str) -> Result<(), core::fmt::Error> {
        self.write_entry_sequence(s.len());
        for c in s.bytes() {
            self.write_byte(c);
        }
        self.flush();

        Ok(())
    }
}
