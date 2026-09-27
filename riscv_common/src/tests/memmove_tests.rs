use core::mem::MaybeUninit;

/// Overlap distances for the larger sizes of the reduced Miri grids: both directions, every
/// mismatch mod 4, and a one-word overlap for the aligned blocks.
#[cfg(miri)]
const MIRI_DELTAS: [isize; 11] = [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5];

fn seed(n: usize, alignment: usize, delta: isize) -> u64 {
    0x9e37_79b9_7f4a_7c15u64
        ^ (n as u64).wrapping_mul(0xbf58_476d_1ce4_e5b9)
        ^ (alignment as u64).wrapping_mul(0x94d0_49bb_1331_11eb)
        ^ (delta as i64 as u64).rotate_left(29)
}

fn next_byte(state: &mut u64) -> u8 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    (*state >> 32) as u8
}

fn sentinel_case(n: usize, alignment: usize, delta: isize) {
    let mut backing = vec![0u32; (3 * n + 204 + 3) / 4];
    let bytes = unsafe {
        core::slice::from_raw_parts_mut(backing.as_mut_ptr().cast::<u8>(), backing.len() * 4)
    };
    let src_offset = ((n + 83) & !3) + alignment;
    let dest_offset = src_offset.checked_add_signed(delta).unwrap();
    assert!(src_offset + n <= bytes.len());
    assert!(dest_offset + n <= bytes.len());

    let mut state = seed(n, alignment, delta);
    for byte in bytes.iter_mut() {
        *byte = next_byte(&mut state);
    }
    let snapshot = bytes.to_vec();
    let mut expected = snapshot.clone();
    expected[dest_offset..dest_offset + n].copy_from_slice(&snapshot[src_offset..src_offset + n]);

    let base = bytes.as_mut_ptr();
    let src = unsafe { base.add(src_offset) as *const u8 };
    let dest = unsafe { base.add(dest_offset) };
    assert_eq!(src.addr() % 4, alignment);
    let returned = unsafe { crate::memmove::memmove_impl(dest, src, n) };
    assert_eq!(
        returned, dest,
        "n={n}, alignment={alignment}, delta={delta}"
    );
    assert_eq!(
        &*bytes,
        expected.as_slice(),
        "n={n}, alignment={alignment}, delta={delta}"
    );
}

fn read_bounds_case(n: usize, alignment: usize, delta: isize) {
    // Only source bytes are initialized; Miri rejects an out-of-range integer load.
    let mut backing = vec![MaybeUninit::<u32>::uninit(); (3 * n + 204 + 3) / 4];
    let base = backing.as_mut_ptr().cast::<u8>();
    let src_offset = ((n + 83) & !3) + alignment;
    let dest_offset = src_offset.checked_add_signed(delta).unwrap();
    assert!(src_offset + n <= backing.len() * 4);
    assert!(dest_offset + n <= backing.len() * 4);

    let src = unsafe { base.add(src_offset) };
    let dest = unsafe { base.add(dest_offset) };
    assert_eq!(src.addr() % 4, alignment);
    let mut state = seed(n, alignment, delta);
    let expected: Vec<u8> = (0..n).map(|_| next_byte(&mut state)).collect();
    for (i, &byte) in expected.iter().enumerate() {
        unsafe { src.add(i).write(byte) };
    }

    let returned = unsafe { crate::memmove::memmove_impl(dest, src, n) };
    assert_eq!(
        returned, dest,
        "n={n}, alignment={alignment}, delta={delta}"
    );
    for (i, &byte) in expected.iter().enumerate() {
        assert_eq!(
            unsafe { dest.add(i).read() },
            byte,
            "n={n}, alignment={alignment}, delta={delta}, byte={i}"
        );
    }
}

#[test]
fn test_memmove_sentinels() {
    #[cfg(not(miri))]
    {
        for n in 0..=260 {
            for alignment in 0..4 {
                for delta in -(n as isize + 5)..=(n as isize + 5) {
                    sentinel_case(n, alignment, delta);
                }
            }
        }
        for n in [511, 512, 513, 1023, 1024, 1027, 4099] {
            for alignment in 0..4 {
                for delta in -70..=70 {
                    sentinel_case(n, alignment, delta);
                }
                for k in -5..=5 {
                    sentinel_case(n, alignment, n as isize + k);
                    sentinel_case(n, alignment, -(n as isize + k));
                }
            }
        }
    }
    #[cfg(miri)]
    {
        for n in 0..=12 {
            for alignment in 0..4 {
                for delta in -(n as isize + 2)..=(n as isize + 2) {
                    sentinel_case(n, alignment, delta);
                }
            }
        }
        for n in (13..=20).chain([63, 64, 65, 128]) {
            for alignment in 0..4 {
                for delta in MIRI_DELTAS
                    .into_iter()
                    .chain([-(n as isize + 2), n as isize + 2])
                {
                    sentinel_case(n, alignment, delta);
                }
            }
        }
    }
}

#[test]
fn test_memmove_read_bounds() {
    #[cfg(not(miri))]
    {
        for n in (0..=40).chain([63, 64, 65, 67, 100, 144]) {
            for alignment in 0..4 {
                for delta in -(n as isize + 4)..=(n as isize + 4) {
                    read_bounds_case(n, alignment, delta);
                }
            }
        }
    }
    #[cfg(miri)]
    {
        for n in 0..=12 {
            for alignment in 0..4 {
                for delta in -(n as isize + 4)..=(n as isize + 4) {
                    read_bounds_case(n, alignment, delta);
                }
            }
        }
        for n in (13..=20).chain([63, 64, 65, 67, 128]) {
            for alignment in 0..4 {
                for delta in MIRI_DELTAS
                    .into_iter()
                    .chain([-(n as isize + 4), n as isize + 4])
                {
                    read_bounds_case(n, alignment, delta);
                }
            }
        }
    }
}
