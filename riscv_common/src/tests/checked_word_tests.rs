//! `checked_word_memory`. All pointers are into allocated word-backed buffers; zero length on
//! pointers outside RAM is covered by the reduced-VM oracle in `full_statement_verifier`.

use crate::memcpy::memcpy_impl;
use crate::memmove::memmove_impl;
use crate::memset::memset_impl;

fn pattern(words: usize, seed: u32) -> Vec<u32> {
    (0..words as u32)
        .map(|i| i.wrapping_mul(0x9e37_79b9) ^ seed.wrapping_mul(0x85eb_ca6b))
        .collect()
}

fn base(buffer: &mut [u32]) -> *mut u8 {
    buffer.as_mut_ptr().cast()
}

#[test]
fn memcpy_copies_words() {
    // 1..=65 words cross the 64-byte loop and every smaller block.
    for words in 1..=65 {
        let source = pattern(67, 1);
        let mut destination = pattern(67, 2);
        let mut expected = destination.clone();
        expected[1..1 + words].copy_from_slice(&source[1..1 + words]);
        let dest = unsafe { base(&mut destination).add(4) };
        assert_eq!(
            unsafe { memcpy_impl(dest, source.as_ptr().add(1).cast(), 4 * words) },
            dest
        );
        assert_eq!(destination, expected, "{words} words");
    }
    // Equal operands and adjacent ranges.
    let mut buffer = pattern(32, 3);
    let before = buffer.clone();
    let p = base(&mut buffer);
    unsafe { memcpy_impl(p, p, 64) };
    assert_eq!(buffer, before);
    unsafe { memcpy_impl(p.add(64), p, 64) };
    assert_eq!(buffer[16..], before[..16]);
}

#[test]
fn memset_fills_the_low_byte() {
    for (value, fill) in [(0x1ab_u32, 0xabab_abab_u32), (u32::MAX, u32::MAX), (0, 0)] {
        for words in 1..=65 {
            let mut buffer = pattern(67, 5);
            let mut expected = buffer.clone();
            expected[1..1 + words].fill(fill);
            let dest = unsafe { base(&mut buffer).add(4) };
            assert_eq!(unsafe { memset_impl(dest, value, 4 * words) }, dest);
            assert_eq!(buffer, expected, "value {value:#x}, {words} words");
        }
    }
}

#[test]
fn memmove_handles_overlap_in_both_directions() {
    // Distance 0 is the equal-pointer case; distance == words is adjacent.
    for distance in [0, 1, 2, 3, 16, 64] {
        for words in [1, 2, 3, 15, 16, 17, 32, 65] {
            for forward in [true, false] {
                let mut buffer = pattern(words + distance + 4, 6);
                let mut expected = buffer.clone();
                let (src, dst) = if forward {
                    (2 + distance, 2)
                } else {
                    (2, 2 + distance)
                };
                expected.copy_within(src..src + words, dst);
                let p = base(&mut buffer);
                let ret = unsafe { memmove_impl(p.add(4 * dst), p.add(4 * src), 4 * words) };
                assert_eq!(ret, unsafe { p.add(4 * dst) });
                assert_eq!(
                    buffer, expected,
                    "{words} words, distance {distance}, forward {forward}"
                );
            }
        }
    }
}

#[test]
fn zero_length_touches_nothing() {
    let mut buffer = pattern(8, 8);
    let before = buffer.clone();
    let p = base(&mut buffer);
    for (d, s) in [(1, 2), (3, 0), (0, 1), (2, 2)] {
        unsafe {
            assert_eq!(memcpy_impl(p.add(d), p.add(16 + s), 0), p.add(d));
            assert_eq!(memmove_impl(p.add(d), p.add(16 + s), 0), p.add(d));
            assert_eq!(memset_impl(p.add(d), 0xff, 0), p.add(d));
        }
    }
    assert_eq!(buffer, before);
}

#[test]
fn every_misaligned_argument_traps() {
    type Call = unsafe fn(*mut u8, usize, usize, usize) -> *mut u8;
    let memcpy: Call = |p, d, s, n| unsafe { memcpy_impl(p.add(d), p.add(128 + s), n) };
    let memmove: Call = |p, d, s, n| unsafe { memmove_impl(p.add(d), p.add(128 + s), n) };
    let memset: Call = |p, d, _, n| unsafe { memset_impl(p.add(d), 0x5a, n) };
    for (name, call, has_src) in [
        ("memcpy", memcpy, true),
        ("memmove", memmove, true),
        ("memset", memset, false),
    ] {
        for residue in 1..4 {
            let mut cases = vec![("dst", residue, 0, 64), ("len", 0, 0, 60 + residue)];
            if has_src {
                cases.push(("src", 0, residue, 64));
            }
            for (argument, d, s, n) in cases {
                let mut buffer = pattern(64, 9);
                let p = base(&mut buffer);
                let refusal = std::panic::catch_unwind(|| unsafe { call(p, d, s, n) })
                    .expect_err(&format!("{name} {argument} residue {residue} returned"));
                assert_eq!(
                    refusal.downcast_ref::<&str>(),
                    Some(&"checked_word_memory: invalid arguments"),
                    "{name} {argument} residue {residue}"
                );
            }
        }
    }
}
