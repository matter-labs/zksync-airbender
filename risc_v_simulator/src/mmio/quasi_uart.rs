use log::info;
use std::{collections::VecDeque, ffi::CString};

use super::*;

#[derive(Clone, Debug, Default)]
pub struct QuasiUART {
    pub oracle: VecDeque<u32>,
    pub buffer: Vec<u8>,
}

pub const QUASI_UART_ADDRESS: u32 = 0x0000_0004;

impl MMIOSource for QuasiUART {
    fn address_range(&self) -> std::ops::Range<u64> {
        (QUASI_UART_ADDRESS as u64)..((QUASI_UART_ADDRESS + 1) as u64)
    }

    fn read(&mut self, address: u64, _trap: &mut TrapReason) -> u32 {
        debug_assert!(self.address_range().contains(&address));

        self.oracle.pop_front().unwrap_or(0u32)
    }

    fn write(&mut self, address: u64, value: u32, _trap: &mut TrapReason) {
        debug_assert!(self.address_range().contains(&address));
        // let tmp = value.to_le_bytes();
        // if let Ok(substring) = core::str::from_utf8(&tmp) {
        //     dbg!(substring);
        // } else {

        // }
        self.buffer.extend(value.to_le_bytes());
        let len = self.buffer.len();
        for idx in (len - 4)..len {
            if self.buffer[idx] == 0 {
                // c-style string can be made
                let mut buffer = std::mem::replace(&mut self.buffer, vec![]);
                buffer.truncate(idx + 1);
                let c_string = CString::from_vec_with_nul(buffer).unwrap();
                info!("UART: `{}`", c_string.to_string_lossy());
                break;
            }
        }
    }
}
