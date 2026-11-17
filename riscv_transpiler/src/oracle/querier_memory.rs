//! The oracle's read access to the memory of the querier: the input word of a memory-based
//! query is often an address in it (see the [module documentation](super)).

use crate::vm::RamPeek;
use core::mem::size_of;

/// An error of reading the querier's memory: a malformed address of a request or an operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct QuerierMemoryError(pub &'static str);

impl core::fmt::Display for QuerierMemoryError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.0)
    }
}

impl core::error::Error for QuerierMemoryError {}

/// Read access of the oracle to the memory of the querier.
pub trait QuerierMemory {
    /// Size in bytes of a word, and of an address, of the querier: 4 on the proving target, and
    /// `size_of::<usize>()` for a querier in the same process.
    fn word_size(&self) -> usize;

    /// Reads the `u32` at `address`, which must be 4-byte aligned.
    fn read_u32(&self, address: usize) -> Result<u32, QuerierMemoryError>;
}

impl<M: QuerierMemory + ?Sized> QuerierMemory for &M {
    fn word_size(&self) -> usize {
        (**self).word_size()
    }

    fn read_u32(&self, address: usize) -> Result<u32, QuerierMemoryError> {
        (**self).read_u32(address)
    }
}

/// `address + offset`, or an error if it overflows.
pub fn offset_address(address: usize, offset: usize) -> Result<usize, QuerierMemoryError> {
    address
        .checked_add(offset)
        .ok_or(QuerierMemoryError("querier address overflows"))
}

/// Reads a querier word ([`QuerierMemory::word_size`] bytes, low half first).
pub fn read_querier_word<M: QuerierMemory + ?Sized>(
    memory: &M,
    address: usize,
) -> Result<usize, QuerierMemoryError> {
    let low = memory.read_u32(address)?;
    match memory.word_size() {
        4 => Ok(low as usize),
        8 => {
            let high = memory.read_u32(offset_address(address, 4)?)?;
            usize::try_from(u64::from(low) | (u64::from(high) << 32))
                .map_err(|_| QuerierMemoryError("querier word does not fit into usize"))
        }
        _ => Err(QuerierMemoryError("unsupported querier word size")),
    }
}

/// Reads `dst.len()` consecutive `u32` words at `address` of the querier into `dst`.
pub fn read_querier_u32_words_into<M: QuerierMemory + ?Sized>(
    memory: &M,
    address: usize,
    dst: &mut [u32],
) -> Result<(), QuerierMemoryError> {
    for (i, word) in dst.iter_mut().enumerate() {
        let offset = i
            .checked_mul(size_of::<u32>())
            .ok_or(QuerierMemoryError("querier address overflows"))?;
        *word = memory.read_u32(offset_address(address, offset)?)?;
    }
    Ok(())
}

/// The memory of a querier in this process, whose addresses are exposed pointers.
#[derive(Debug)]
pub struct NativeQuerierMemory(());

impl NativeQuerierMemory {
    /// # Safety
    ///
    /// Only for reading the inputs of queries sent by this process (see
    /// [`QueryDispatcher::send_query`](super::QueryDispatcher::send_query)), while they are being
    /// sent: their addresses refer to live values then.
    pub const unsafe fn new() -> Self {
        Self(())
    }
}

impl QuerierMemory for NativeQuerierMemory {
    fn word_size(&self) -> usize {
        size_of::<usize>()
    }

    fn read_u32(&self, address: usize) -> Result<u32, QuerierMemoryError> {
        if address == 0 || !address.is_multiple_of(size_of::<u32>()) {
            return Err(QuerierMemoryError("invalid querier address"));
        }
        // SAFETY: guaranteed by the creator of the view
        Ok(unsafe { core::ptr::with_exposed_provenance::<u32>(address).read() })
    }
}

/// The memory of the RISC-V guest, for the processors of memory-based queries (see
/// [`OracleQueryProcessor::process_memory_query`](super::OracleQueryProcessor::process_memory_query)).
pub struct GuestMemory<'a, R: RamPeek + ?Sized>(pub &'a R);

impl<R: RamPeek + ?Sized> QuerierMemory for GuestMemory<'_, R> {
    fn word_size(&self) -> usize {
        size_of::<u32>()
    }

    fn read_u32(&self, address: usize) -> Result<u32, QuerierMemoryError> {
        let address = u32::try_from(address)
            .map_err(|_| QuerierMemoryError("guest address does not fit into u32"))?;
        if !address.is_multiple_of(4) {
            return Err(QuerierMemoryError("unaligned guest address"));
        }
        Ok(self.0.peek_word(address))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_querier_memory_reads_this_process() {
        let words = [0x0102_0304u32, 0xa0b0_c0d0, 7];
        // SAFETY: reads `words`, which is alive
        let memory = unsafe { NativeQuerierMemory::new() };
        let address = words.as_ptr().expose_provenance();
        let mut read = [0u32; 3];
        assert_eq!(
            read_querier_u32_words_into(&memory, address, &mut read),
            Ok(())
        );
        assert_eq!(read, words);
        // a querier word is two `u32`s, low first
        assert_eq!(
            read_querier_word(&memory, address),
            Ok(0xa0b0_c0d0_0102_0304)
        );
        for address in [0, address + 2] {
            assert_eq!(
                memory.read_u32(address),
                Err(QuerierMemoryError("invalid querier address"))
            );
        }
    }

    /// A querier memory of zeroes, with any word size, which it does not dereference
    struct Zeroes(usize);

    impl QuerierMemory for Zeroes {
        fn word_size(&self) -> usize {
            self.0
        }

        fn read_u32(&self, _address: usize) -> Result<u32, QuerierMemoryError> {
            Ok(0)
        }
    }

    #[test]
    fn querier_words_do_not_wrap_around() {
        assert_eq!(
            read_querier_u32_words_into(&Zeroes(4), usize::MAX - 3, &mut [0; 2]),
            Err(QuerierMemoryError("querier address overflows"))
        );
        assert_eq!(
            read_querier_word(&Zeroes(8), usize::MAX - 3),
            Err(QuerierMemoryError("querier address overflows"))
        );
        assert_eq!(
            read_querier_word(&Zeroes(2), 0x1000),
            Err(QuerierMemoryError("unsupported querier word size"))
        );
        assert_eq!(read_querier_word(&Zeroes(4), 0x1000), Ok(0));
    }
}
