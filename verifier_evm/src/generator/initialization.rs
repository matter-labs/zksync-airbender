//! Validation of the prover-selected initialization/teardown address windows.

use super::PREIMAGE_TOP_BITS_BYTE_OFFSET;

pub(super) fn validation_yul(trace_len: usize, word_bits: u32, num_sets: usize) -> String {
    assert!(
        trace_len.is_power_of_two(),
        "invalid initialization trace length"
    );
    let window_bits = trace_len.trailing_zeros().checked_add(word_bits).unwrap();
    assert!(
        window_bits <= 32,
        "initialization window exceeds u32 addresses"
    );
    let top_index_limit = 1u64 << (32 - window_bits);
    assert!(num_sets > 0 && num_sets as u64 <= top_index_limit);
    let top_bits_end = PREIMAGE_TOP_BITS_BYTE_OFFSET + num_sets * 4;

    // A window has trace_len words of 2^word_bits bytes. Its top index must
    // place the entire window in the u32 byte-address space. Equal-size aligned
    // windows are disjoint exactly when their indices differ; ordering and
    // contiguity are unnecessary. This is validation, not transcript binding.
    indoc::formatdoc!(
        "
        function gkr_validate_inits_teardowns_windows(preimage_ptr) {{
            if lt(calldatasize(), add(preimage_ptr, {top_bits_end})) {{ revert(0, 0) }}
            for {{ let i := 0 }} lt(i, {num_sets}) {{ i := add(i, 1) }} {{
                let offset := add(preimage_ptr, {PREIMAGE_TOP_BITS_BYTE_OFFSET})
                let index := gkr_inits_teardowns_topbits(add(offset, mul(i, 4)))
                if iszero(lt(index, {top_index_limit})) {{ revert(0, 0) }}
                for {{ let j := 0 }} lt(j, i) {{ j := add(j, 1) }} {{
                    if eq(index, gkr_inits_teardowns_topbits(add(offset, mul(j, 4)))) {{ revert(0, 0) }}
                }}
            }}
        }}
        "
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn limit_follows_byte_address_geometry() {
        let production = validation_yul(1 << 22, 2, 2);
        assert!(production.contains("lt(index, 256)"));
        assert!(production.contains("add(preimage_ptr, 404)"));
        let larger_words = validation_yul(1 << 22, 3, 2);
        assert!(larger_words.contains("lt(index, 128)"));
        let larger_trace = validation_yul(1 << 24, 2, 2);
        assert!(larger_trace.contains("lt(index, 64)"));
        let more_sets = validation_yul(1 << 22, 2, 3);
        assert!(more_sets.contains("lt(i, 3)"));
        assert!(more_sets.contains("add(preimage_ptr, 408)"));
    }

    #[test]
    #[should_panic(expected = "invalid initialization trace length")]
    fn rejects_non_power_of_two_windows() {
        validation_yul(3, 2, 2);
    }

    #[test]
    #[should_panic(expected = "initialization window exceeds u32 addresses")]
    fn rejects_oversized_windows() {
        validation_yul(1 << 31, 2, 1);
    }
}
