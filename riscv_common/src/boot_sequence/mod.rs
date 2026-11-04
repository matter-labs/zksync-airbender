core::arch::global_asm!(include_str!("../asm/start.s"));

// #[cfg(not(feature = "no_memcpy_override"))]
// core::arch::global_asm!(include_str!("../asm/memcpy.s"));

#[cfg(not(feature = "no_memcpy_override"))]
mod memcpy;

#[cfg(not(feature = "no_memset_override"))]
core::arch::global_asm!(include_str!("../asm/memset.s"));

pub use ::common_constants;

#[export_name = "_setup_interrupts"]
pub unsafe fn custom_setup_interrupts() {
    extern "C" {
        fn _machine_start_trap();
    }
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

extern "C" {
    // Boundary of ROM region
    pub static mut _rom_size: usize;

    // Boundaries of the heap
    pub static mut _sheap: usize;
    pub static mut _eheap: usize;

    // Boundaries of the stack
    pub static mut _sstack: usize;
    pub static mut _estack: usize;

    // Boundaries of the .data section (and it's part in ROM)
    pub static mut _sidata: usize;
    pub static mut _sdata: usize;
    pub static mut _edata: usize;

    // Boundaries of the .rodata section
    pub static mut _sirodata: usize;
    pub static mut _srodata: usize;
    pub static mut _erodata: usize;
}

pub fn heap_start() -> *mut usize {
    use core::ptr::addr_of_mut;
    addr_of_mut!(_sheap)
}

pub fn heap_end() -> *mut usize {
    use core::ptr::addr_of_mut;
    addr_of_mut!(_eheap)
}

pub fn init() {
    use core::ptr::addr_of_mut;

    use common_constants::rom::ROM_BYTE_SIZE;
    assert!(addr_of_mut!(_rom_size).addr() <= ROM_BYTE_SIZE);
    assert_eq!(addr_of_mut!(_estack).addr(), ROM_BYTE_SIZE);

    unsafe {
        // copy .rodata
        let load_address = addr_of_mut!(_sirodata);
        let rodata_start = addr_of_mut!(_srodata);
        let rodata_end = addr_of_mut!(_erodata);
        load_to_ram(
            load_address as *const u8,
            rodata_start as *mut u8,
            rodata_end as *mut u8,
        );

        // copy .data
        let load_address = addr_of_mut!(_sidata);
        let data_start = addr_of_mut!(_sdata);
        let data_end = addr_of_mut!(_edata);
        load_to_ram(
            load_address as *const u8,
            data_start as *mut u8,
            data_end as *mut u8,
        );
    }
}

unsafe fn load_to_ram(src: *const u8, dst_start: *mut u8, dst_end: *mut u8) {
    #[cfg(debug_assertions)]
    {
        use common_constants::rom::ROM_BYTE_SIZE;

        debug_assert!(src.addr() < ROM_BYTE_SIZE);
        debug_assert!(dst_start.addr() >= ROM_BYTE_SIZE);
        debug_assert!(dst_end.addr() >= dst_start.addr());
    }

    let offset = dst_end.offset_from_unsigned(dst_start);

    core::ptr::copy_nonoverlapping(src, dst_start, offset);
}
