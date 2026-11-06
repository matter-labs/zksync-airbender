use crate::memcpy::memcpy_impl;
use crate::memmove::memmove_impl;
use crate::memset::memset_impl;

// A tail-only length, one bulk block, and a bulk block plus every tail block.
const WORD_COUNTS: [usize; 3] = [1, 16, 31];

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
    for words in WORD_COUNTS {
        let source = pattern(words + 2, 1);
        let mut destination = pattern(words + 2, 2);
        let mut expected = destination.clone();
        expected[1..1 + words].copy_from_slice(&source[1..1 + words]);
        let dest = unsafe { base(&mut destination).add(4) };
        assert_eq!(
            unsafe { memcpy_impl(dest, source.as_ptr().add(1).cast(), 4 * words) },
            dest
        );
        assert_eq!(destination, expected, "{words} words");
    }
}

#[test]
fn memset_fills_the_low_byte() {
    for words in WORD_COUNTS {
        let mut buffer = pattern(words + 2, 5);
        let mut expected = buffer.clone();
        expected[1..1 + words].fill(0xabab_abab);
        let dest = unsafe { base(&mut buffer).add(4) };
        assert_eq!(unsafe { memset_impl(dest, 0x1ab, 4 * words) }, dest);
        assert_eq!(buffer, expected, "{words} words");
    }
}

#[test]
fn memmove_handles_overlap_in_both_directions() {
    for words in WORD_COUNTS {
        for forward in [true, false] {
            let mut buffer = pattern(words + 5, 6);
            let mut expected = buffer.clone();
            let (src, dst) = if forward { (3, 2) } else { (2, 3) };
            expected.copy_within(src..src + words, dst);
            let p = base(&mut buffer);
            let ret = unsafe { memmove_impl(p.add(4 * dst), p.add(4 * src), 4 * words) };
            assert_eq!(ret, unsafe { p.add(4 * dst) });
            assert_eq!(buffer, expected, "{words} words, forward {forward}");
        }
    }
}

#[test]
fn zero_length_touches_nothing() {
    use core::ptr::{null_mut, without_provenance_mut};
    // Null and unallocated misaligned pointers: any access would fault.
    for (d, s) in [
        (null_mut(), without_provenance_mut(3)),
        (without_provenance_mut(usize::MAX - 2), null_mut()),
    ] {
        unsafe {
            assert_eq!(memcpy_impl(d, s, 0), d);
            assert_eq!(memmove_impl(d, s, 0), d);
            assert_eq!(memset_impl(d, 0xff, 0), d);
        }
    }
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
        for residue in [1, 2] {
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
