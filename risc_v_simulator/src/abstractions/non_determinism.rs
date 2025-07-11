// there is no interpretation of methods here, it's just read/write and that's all
pub trait NonDeterminismCSRSource<M: MemorySource + ?Sized> {
    const SHOULD_MOCK_READS_BEFORE_WRITES: bool = true;
    const SHOULD_IGNORE_WRITES_AFTER_READS: bool = true;

    fn read(&mut self) -> u32;

    // we in general can allow CSR source to peek into memory (readonly)
    // to perform adhoc computations to prepare result. This will allow to save on
    // passing large structures
    fn write_with_memory_access(&mut self, memory: &M, value: u32);
}

pub struct ZeroedSource;

impl<M: MemorySource> NonDeterminismCSRSource<M> for ZeroedSource {
    fn read(&mut self) -> u32 {
        0u32
    }
    fn write_with_memory_access(&mut self, _memory: &M, _value: u32) {}
}

use super::memory::MemorySource;
use std::collections::VecDeque;

#[derive(Clone, Debug)]
pub struct QuasiUARTSource {
    pub oracle: VecDeque<u32>,
    write_state: QuasiUARTSourceState,
}

impl Default for QuasiUARTSource {
    fn default() -> Self {
        Self {
            oracle: VecDeque::new(),
            write_state: QuasiUARTSourceState::Ready,
        }
    }
}

impl QuasiUARTSource {
    pub fn new_with_reads(reads: Vec<u32>) -> Self {
        Self {
            oracle: VecDeque::from(reads),
            write_state: QuasiUARTSourceState::Ready,
        }
    }
}

#[derive(Clone, Debug)]
pub enum QuasiUARTSourceState {
    Ready,
    Buffering {
        remaining_words: Option<usize>,
        remaining_len_in_bytes: Option<usize>,
        buffer: Vec<u8>,
    },
}

impl QuasiUARTSourceState {
    const HELLO_VALUE: u32 = u32::MAX;

    pub fn process_write(&mut self, value: u32) {
        match self {
            QuasiUARTSourceState::Ready => {
                if value == Self::HELLO_VALUE {
                    *self = QuasiUARTSourceState::Buffering {
                        remaining_words: None,
                        remaining_len_in_bytes: None,
                        buffer: Vec::new(),
                    };
                }
            }
            QuasiUARTSourceState::Buffering {
                remaining_words,
                remaining_len_in_bytes,
                buffer,
            } => {
                if remaining_words.is_none() {
                    *remaining_words = Some(value as usize);
                    buffer.clear();
                    return;
                }
                if remaining_len_in_bytes.is_none() {
                    assert!(remaining_words.is_some());
                    *remaining_words.as_mut().unwrap() -= 1;
                    *remaining_len_in_bytes = Some(value as usize);
                    buffer.reserve(value as usize);

                    return;
                }
                // It is also possible that someone wrote 0 bytes.
                // In this case we just ignore the write.
                if remaining_words.unwrap() > 0 {
                    *remaining_words.as_mut().unwrap() -= 1;
                    if remaining_len_in_bytes.unwrap() >= 4 {
                        buffer.extend(value.to_le_bytes());
                        *remaining_len_in_bytes.as_mut().unwrap() -= 4;
                    } else {
                        let remaining_len = remaining_len_in_bytes.unwrap();
                        let bytes = value.to_le_bytes();
                        buffer.extend_from_slice(&bytes[..remaining_len]);
                        *remaining_len_in_bytes.as_mut().unwrap() = 0;
                    }
                }
                if remaining_words.unwrap() == 0 {
                    let buffer = std::mem::replace(buffer, Vec::new());
                    println!("UART: `{}`", String::from_utf8_lossy(&buffer));
                    *self = QuasiUARTSourceState::Ready;
                }
            }
        }
    }
}

impl<M: MemorySource> NonDeterminismCSRSource<M> for QuasiUARTSource {
    fn read(&mut self) -> u32 {
        self.oracle.pop_front().unwrap_or_default()
    }

    fn write_with_memory_access(&mut self, _memory: &M, value: u32) {
        self.write_state.process_write(value);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_quasi_uart_source_state_ready_to_buffering() {
        let mut state = QuasiUARTSourceState::Ready;
        state.process_write(QuasiUARTSourceState::HELLO_VALUE);

        if let QuasiUARTSourceState::Buffering {
            remaining_words,
            remaining_len_in_bytes,
            buffer,
        } = state
        {
            assert!(remaining_words.is_none());
            assert!(remaining_len_in_bytes.is_none());
            assert!(buffer.is_empty());
        } else {
            panic!("State did not transition to Buffering");
        }
    }

    #[test]
    fn test_quasi_uart_source_state_buffering_with_remaining_words() {
        let mut state = QuasiUARTSourceState::Buffering {
            remaining_words: None,
            remaining_len_in_bytes: None,
            buffer: Vec::new(),
        };

        state.process_write(3); // Set remaining_words to 3
        if let QuasiUARTSourceState::Buffering {
            remaining_words,
            remaining_len_in_bytes,
            buffer,
        } = state
        {
            assert_eq!(remaining_words, Some(3));
            assert!(remaining_len_in_bytes.is_none());
            assert!(buffer.is_empty());
        } else {
            panic!("State did not remain in Buffering");
        }
    }

    #[test]
    fn test_quasi_uart_source_state_buffering_with_remaining_len_in_bytes() {
        let mut state = QuasiUARTSourceState::Buffering {
            remaining_words: Some(2),
            remaining_len_in_bytes: None,
            buffer: Vec::new(),
        };

        state.process_write(8); // Set remaining_len_in_bytes to 8
        if let QuasiUARTSourceState::Buffering {
            remaining_words,
            remaining_len_in_bytes,
            buffer,
        } = state
        {
            assert_eq!(remaining_words, Some(1));
            assert_eq!(remaining_len_in_bytes, Some(8));
            assert!(buffer.capacity() >= 8);
        } else {
            panic!("State did not remain in Buffering");
        }
    }

    #[test]
    fn test_quasi_uart_source_state_buffering_with_data_write() {
        let mut state = QuasiUARTSourceState::Buffering {
            remaining_words: Some(2),
            remaining_len_in_bytes: Some(6),
            buffer: Vec::new(),
        };

        state.process_write(0x12345678); // Write 4 bytes
        if let QuasiUARTSourceState::Buffering {
            remaining_words,
            remaining_len_in_bytes,
            buffer,
        } = state.clone()
        {
            assert_eq!(remaining_words, Some(1));
            assert_eq!(remaining_len_in_bytes, Some(2));
            assert_eq!(buffer, vec![0x78, 0x56, 0x34, 0x12]);
        } else {
            panic!("State did not remain in Buffering");
        }
        state.process_write(0xffff0000); // Write remaining 2 bytes
        if let QuasiUARTSourceState::Ready = state {
            // Check that the state transitioned to Ready
        } else {
            panic!("State did not transition to Ready");
        }
    }

    #[test]
    fn test_quasi_uart_source_state_buffering_to_ready() {
        let mut state = QuasiUARTSourceState::Buffering {
            remaining_words: Some(1),
            remaining_len_in_bytes: Some(4),
            buffer: Vec::new(),
        };

        state.process_write(0x12345678); // Write the last word
        if let QuasiUARTSourceState::Ready = state {
            // Check that the state transitioned to Ready
        } else {
            panic!("State did not transition to Ready");
        }
    }

    #[test]
    fn test_write_empty() {
        let mut state = QuasiUARTSourceState::Ready;

        state.process_write(0x1); // 1 word
        state.process_write(0x0); // 0 bytes

        if let QuasiUARTSourceState::Ready = state {
            // Check that the state transitioned to Ready
        } else {
            panic!("State did not transition to Ready");
        }
    }
}
