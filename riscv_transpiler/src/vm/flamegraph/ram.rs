use crate::vm::{RamPeek, RamWithRomRegion};

/// Minimal RAM contract needed by the flamegraph unwinder.
///
/// `RamPeek` is intentionally low-level and uses debug assertions for bounds,
/// so flamegraph collection adds an explicit checked read API to keep profiling
/// robust even when frame-pointer metadata is malformed.
pub trait FlamegraphReadableRam: RamPeek {
    fn total_words_for_flamegraph(&self) -> usize;

    #[inline(always)]
    fn try_peek_word_for_flamegraph(&self, address: u32) -> Option<u32> {
        if address % 4 != 0 {
            return None;
        }

        let word_idx = (address / 4) as usize;
        if word_idx >= self.total_words_for_flamegraph() {
            return None;
        }

        Some(self.peek_word(address))
    }
}

impl<const N: usize> FlamegraphReadableRam for [u32; N] {
    #[inline(always)]
    fn total_words_for_flamegraph(&self) -> usize {
        N
    }
}

impl FlamegraphReadableRam for [u32] {
    #[inline(always)]
    fn total_words_for_flamegraph(&self) -> usize {
        self.len()
    }
}

impl<const ROM_BOUND_SECOND_WORD_BITS: usize> FlamegraphReadableRam
    for RamWithRomRegion<ROM_BOUND_SECOND_WORD_BITS>
{
    #[inline(always)]
    fn total_words_for_flamegraph(&self) -> usize {
        self.backing.len()
    }
}
