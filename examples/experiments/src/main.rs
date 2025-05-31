#![no_std]
#![feature(const_mut_refs)]
#![feature(strict_provenance)]
#![feature(exposed_provenance)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]
#![no_builtins]

extern "C" {
    // Boundaries of the heap
    static mut _sheap: usize;
    static mut _eheap: usize;

    // Boundaries of the stack
    static mut _sstack: usize;
    static mut _estack: usize;
}

core::arch::global_asm!(include_str!("../../scripts/asm/asm_reduced.S"));

#[no_mangle]
extern "C" fn eh_personality() {}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    rust_abort();
}

#[derive(Clone, Copy, Debug, Default)]
pub struct NullAllocator;

unsafe impl core::alloc::GlobalAlloc for NullAllocator {
    unsafe fn alloc(&self, _layout: core::alloc::Layout) -> *mut u8 {
        // panic!("use of global null allocator");
        core::hint::unreachable_unchecked()
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: core::alloc::Layout) {
        // panic!("use of global null allocator");
        core::hint::unreachable_unchecked()
    }

    unsafe fn realloc(
        &self,
        _ptr: *mut u8,
        _layout: core::alloc::Layout,
        _new_size: usize,
    ) -> *mut u8 {
        // panic!("use of global null allocator");
        core::hint::unreachable_unchecked()
    }
}

#[global_allocator]
static GLOBAL_ALLOCATOR_PLACEHOLDER: NullAllocator = NullAllocator;

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

#[export_name = "_setup_interrupts"]
pub unsafe fn custom_setup_interrupts() {
    extern "C" {
        fn _machine_start_trap();
    }

    // xtvec::write(_machine_start_trap as *const () as usize, xTrapMode::Direct);
}

#[repr(C)]
#[derive(Debug)]
pub struct MachineTrapFrame {
    pub registers: [u32; 32],
}

/// Exception (trap) handler in rust.
/// Called from the asm/asm.S
#[link_section = ".trap.rust"]
#[export_name = "_machine_start_trap_rust"]
pub extern "C" fn machine_start_trap_rust(_trap_frame: *mut MachineTrapFrame) -> usize {
    {
        unsafe { core::hint::unreachable_unchecked() }
    }
}

/// Set data as a output of the current execution.
/// By convention, the data that is stored in registers 10-17 after
/// execution has finished is considered 'output' of the computation.
/// Registers 18-25 will be set to 0 as our convention for recursive chain start
#[inline(never)]
pub fn zksync_os_finish_success(data: &[u32; 8]) -> ! {
    let mut result = [0u32; 16];
    result[..8].copy_from_slice(data);
    zksync_os_finish_success_extended(&result)
}

/// Set data as a output of the current execution.
/// By convention, the data that is stored in registers 10-25 after
/// execution has finished is considered 'output' of the computation.
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

/// Set data as a output of the current execution. Unsatisfiable in circuits
#[inline(never)]
pub fn zksync_os_finish_error() -> ! {
    unsafe {
        core::hint::unreachable_unchecked();
    }
}

#[no_mangle]
pub fn rust_abort() -> ! {
    zksync_os_finish_error()
}

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

#[inline(always)]
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

unsafe fn workload() -> ! {
    let a: [u32; 16] = core::array::from_fn(|_| csr_read_word());
    let b: [u32; 16] = core::array::from_fn(|_| csr_read_word());
    assert_eq!(a, b);

    zksync_os_finish_success_extended(&a);
}

#[inline(never)]
fn main() -> ! {
    unsafe { workload() }
}
