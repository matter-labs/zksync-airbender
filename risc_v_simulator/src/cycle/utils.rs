use super::*;
use crate::abstractions::memory::MemorySource;
use std::hint::unreachable_unchecked;

#[must_use]
#[inline(always)]
pub(crate) fn opcode_read<M: MemorySource>(pc: u32, memory_source: &mut M) -> u32 {
    let value = memory_source.get_opcode_noexcept(pc as u64);

    value
}

#[must_use]
#[inline(always)]
pub fn mem_read<M: MemorySource, C: MachineConfig>(
    memory_source: &mut M,
    phys_address: u64,
    num_bytes: u32,
) -> (u32, u32) {
    let unalignment = (phys_address & 3) as u8;
    let aligned_address = phys_address & !3;
    let aligned_value = memory_source.get_noexcept(aligned_address);
    if C::SUPPORT_LOAD_LESS_THAN_WORD {
        let value = match (unalignment, num_bytes) {
            (0, 4) | (0, 2) | (2, 2) | (0, 1) | (1, 1) | (2, 1) | (3, 1) => {
                let unalignment_bits = unalignment * 8;
                let value = aligned_value >> unalignment_bits;
                value
            }
            _ => {
                panic!(
                    "Unsupported access for {} bytes at address 0x{:08x}",
                    num_bytes, phys_address
                );
            }
        };

        let mask = match num_bytes {
            1 => 0x000000ff,
            2 => 0x0000ffff,
            4 => 0xffffffff,
            _ => unsafe { unreachable_unchecked() },
        };
        let value = value & mask;

        (aligned_value, value)
    } else {
        let value = match (unalignment, num_bytes) {
            (0, 4) => aligned_value,
            _ => {
                panic!(
                    "Unsupported access for {} bytes at address 0x{:08x}",
                    num_bytes, phys_address
                );
            }
        };

        (aligned_value, value)
    }
}

#[inline(always)]
pub fn mem_write<M: MemorySource, C: MachineConfig>(
    memory_source: &mut M,
    phys_address: u64,
    value: u32,
    num_bytes: u32,
) -> (u32, u32) {
    let unalignment = (phys_address & 3) as u8;
    let aligned_address = phys_address & !3;
    let old_aligned_value = memory_source.get_noexcept(aligned_address);
    if C::SUPPORT_LOAD_LESS_THAN_WORD {
        match (unalignment, num_bytes) {
            a @ (0, 4)
            | a @ (0, 2)
            | a @ (2, 2)
            | a @ (0, 1)
            | a @ (1, 1)
            | a @ (2, 1)
            | a @ (3, 1) => {
                let (unalignment, num_bytes) = a;

                let value_mask = match num_bytes {
                    1 => 0x000000ffu32,
                    2 => 0x0000ffffu32,
                    4 => 0xffffffffu32,
                    _ => unsafe { unreachable_unchecked() },
                };

                let mask_old = match (unalignment, num_bytes) {
                    (0, 1) => 0xffffff00u32,
                    (0, 2) => 0xffff0000u32,
                    (0, 4) => 0x00000000u32,
                    (1, 1) => 0xffff00ffu32,
                    (1, 2) => 0xffff00ffu32,
                    (2, 1) => 0xff00ffffu32,
                    (2, 2) => 0x0000ffffu32,
                    (3, 1) => 0x00ffffffu32,
                    _ => unsafe { unreachable_unchecked() },
                };

                let new_value =
                    ((value & value_mask) << (unalignment * 8)) | (old_aligned_value & mask_old);

                memory_source.set_noexcept(aligned_address, new_value);

                (old_aligned_value, new_value)
            }
            _ => {
                panic!(
                    "Unsupported access for {} bytes at address 0x{:08x}",
                    num_bytes, phys_address
                );
            }
        }
    } else {
        match (unalignment, num_bytes) {
            _a @ (0, 4) => {
                let new_value = value;

                memory_source.set_noexcept(aligned_address, new_value);

                (old_aligned_value, new_value)
            }
            _ => {
                panic!(
                    "Unsupported access for {} bytes at address 0x{:08x}",
                    num_bytes, phys_address
                );
            }
        }
    }
}
