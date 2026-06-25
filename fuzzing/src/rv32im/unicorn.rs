use std::cell::RefCell;
use std::num::TryFromIntError;
use std::rc::Rc;

use riscv_transpiler::ir::preprocess_bytecode;
use unicorn_engine::uc_error;
use unicorn_engine::Arch;
use unicorn_engine::Mode;
use unicorn_engine::Prot;
use unicorn_engine::RegisterRISCV;
use unicorn_engine::Unicorn;

use crate::rv32im::common::constants::TOTAL_MEM_SIZE;
use crate::rv32im::types::DecoderConfig;
use crate::rv32im::GuestResult;
use crate::rv32im::DEFAULT_CYCLES;
use crate::rv32im::ENTRYPOINT;

// Taken from `examples/scripts/lds/memory.x`.
const ROM: u64 = 4 * 1024 * 1024;
const RAM: u64 = TOTAL_MEM_SIZE as u64 - ROM;
const ALIGN: u64 = 4096; // 4kb aligment.

fn configure_vm<'vm>(
    data: &[u8],
    text_sect_len: Option<u64>,
) -> Result<Unicorn<'vm, ()>, uc_error> {
    let text_sect_len = text_sect_len.map(|l| {
        dbg!(l);
        dbg!(((l / ALIGN) + if l % ALIGN == 0 { 0 } else { 1 }) * ALIGN)
    });
    if let Some(tcl) = text_sect_len {
        assert_eq!(tcl % ALIGN, 0, "{tcl} is not aligned to 4kb");
        assert!(data.len() >= tcl as usize);
    }
    let mut vm = Unicorn::new(Arch::RISCV, Mode::RISCV32)?;
    log::debug!("Created vm: {vm:?}");
    for (base, size, perms) in [
        // ROM section
        (
            ENTRYPOINT as u64,
            text_sect_len.unwrap_or(ROM),
            Prot::READ | Prot::EXEC,
        ),
        // RAM section, right after the ROM
        (text_sect_len.unwrap_or(ROM), RAM, Prot::READ | Prot::WRITE),
    ] {
        log::debug!("Creating memory map at address 0x{base} with {size} bytes");
        vm.mem_map(base, size, perms)?;
    }
    vm.mem_write(ENTRYPOINT as u64, data)?;
    log::debug!("Wrote program to entrypoint");
    Ok(vm)
}

#[derive(Debug)]
pub enum Error {
    Unicorn(uc_error),
    U32(TryFromIntError),
    UnexpectedRegisterListSize(usize),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Unicorn(e) => write!(f, "unicorn error: {e}"),
            Error::U32(e) => write!(f, "u64 to u32 conversion error: {e}"),
            Error::UnexpectedRegisterListSize(s) => write!(f, "expected 8 registers, but got {s}"),
        }
    }
}

impl From<uc_error> for Error {
    fn from(value: uc_error) -> Self {
        Self::Unicorn(value)
    }
}

impl From<TryFromIntError> for Error {
    fn from(value: TryFromIntError) -> Self {
        Self::U32(value)
    }
}

/// Runs the given binary in an unicorn VM and returns the result following the same ABI.
pub fn run_on_unicorn(
    data: &[u8],
    text_sect_len: Option<u64>,
) -> Result<Option<GuestResult>, Error> {
    // Set to true if unicorn encounters instructions that are not support by the target, like 2
    // byte instructions or RV32A instructions.
    // If after execution this flag is true we report that the oracle failed, regardless of what
    // actually happened.
    let unsupported_instructions = Rc::new(RefCell::new(false));
    // Clone so we have a different variable go into the closure.
    let ui = unsupported_instructions.clone();
    let prev_pc = Rc::new(RefCell::new(None));
    let mut abi_stop = false;
    let mut vm = configure_vm(data, text_sect_len)?;
    let mut hooks = vec![];
    let hook_id = vm.add_code_hook(ENTRYPOINT as u64, RAM, |vm, addr, size| {
        log::debug!("CODE HOOK!! (0x{addr:08x}) ({size})");
        {
            let prev = prev_pc.borrow();
            if *prev == Some(addr) {
                abi_stop = true;
                vm.emu_stop().unwrap();
            }
        }
        let _ = prev_pc.borrow_mut().insert(addr);
        if size == 2 {
            *ui.borrow_mut() = true;
            return;
        }
        let mut instr = [0, 0, 0, 0];
        match vm.mem_read(addr, &mut instr) {
            Ok(_) => {}
            Err(err) => {
                log::error!("Error in hook at 0x{addr:016x}: {err}");
                return;
            }
        };
        let instr = u32::from_le_bytes(instr);
        let decoded = preprocess_bytecode::<DecoderConfig>(&[instr]);
        log::debug!("    instr = 0x{instr:08x} = {:?}", decoded[0]);
    })?;
    hooks.push(hook_id);
    log::debug!("Unicorn VM configured");
    let hook_id = vm.add_insn_invalid_hook(|_vm| {
        log::warn!("Invalid instruction!");
        false
    })?;
    hooks.push(hook_id);

    if let Err(err) = vm.emu_start(ENTRYPOINT as u64, data.len() as u64, 0, DEFAULT_CYCLES) {
        log::warn!("Unicorn failed while executing: {err}");
        let pc = vm.pc_read()?;
        log::debug!("  PC = 0x{pc:08x}");
        let mut instr = [0, 0, 0, 0];
        vm.mem_read(pc, &mut instr)?;
        let instr = u32::from_le_bytes(instr);
        let decoded = preprocess_bytecode::<DecoderConfig>(&[instr]);
        log::debug!("    instr = 0x{instr:08x} = {:?}", decoded[0]);

        // If unicorn fails during execution we consider it a 'success' that returns no output.
        for hook_id in hooks {
            vm.remove_hook(hook_id)?;
        }

        return Ok(None);
    }
    log::debug!("Execution completed");
    for hook_id in hooks {
        vm.remove_hook(hook_id)?;
    }
    let output = [
        RegisterRISCV::A0,
        RegisterRISCV::A1,
        RegisterRISCV::A2,
        RegisterRISCV::A3,
        RegisterRISCV::A4,
        RegisterRISCV::A5,
        RegisterRISCV::A6,
        RegisterRISCV::A7,
    ]
    .into_iter()
    .map(|reg| -> Result<u32, Error> { Ok(vm.reg_read(reg)?.try_into()?) })
    .collect::<Result<Vec<u32>, _>>()?
    .try_into()
    .map_err(|v: Vec<u32>| Error::UnexpectedRegisterListSize(v.len()))
    .map(Some);
    if *unsupported_instructions.borrow() {
        log::warn!("Unicorn encountered instructions that are not supported by the target");
        return Ok(None);
    }
    drop(vm);
    if !abi_stop {
        log::warn!("Unicorn did not finish according to the ABI!");
        return Ok(None);
    }
    output
}
