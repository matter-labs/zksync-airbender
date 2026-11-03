use core::mem::MaybeUninit;

fn next_byte(state: &mut u64) -> u8 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    (*state >> 32) as u8
}

fn pattern(n: usize, dst_alignment: usize, src_alignment: usize) -> Vec<u8> {
    let mut state = 0x9e37_79b9_7f4a_7c15u64
        ^ (n as u64).wrapping_mul(0xbf58_476d_1ce4_e5b9)
        ^ ((dst_alignment * 4 + src_alignment) as u64).wrapping_mul(0x94d0_49bb_1331_11eb);
    (0..n).map(|_| next_byte(&mut state)).collect()
}

fn sentinel_case(n: usize, dst_alignment: usize, src_alignment: usize) {
    // u32 backing makes the requested byte offsets actual mod-4 alignments.
    let mut source = vec![0u32; (n + 32).div_ceil(4)];
    let mut destination = vec![0xa5a5_a5a5u32; (n + 32).div_ceil(4)];
    let src = source.as_mut_ptr().cast::<u8>();
    let dst = destination.as_mut_ptr().cast::<u8>();
    let src_offset = 8 + src_alignment;
    let dst_offset = 12 + dst_alignment;
    let expected = pattern(n, dst_alignment, src_alignment);
    assert!(src_offset + n <= source.len() * 4);
    assert!(dst_offset + n + 8 <= destination.len() * 4);
    for (i, &byte) in expected.iter().enumerate() {
        unsafe { src.add(src_offset + i).write(byte) };
    }

    let src = unsafe { src.add(src_offset) };
    let dst = unsafe { dst.add(dst_offset) };
    assert_eq!(src.addr() % 4, src_alignment);
    assert_eq!(dst.addr() % 4, dst_alignment);
    let returned = unsafe { crate::memcpy::memcpy_impl(dst, src, n) };
    assert_eq!(
        returned, dst,
        "n={n}, dst={dst_alignment}, src={src_alignment}"
    );
    let bytes = unsafe {
        core::slice::from_raw_parts(destination.as_ptr().cast::<u8>(), destination.len() * 4)
    };
    assert_eq!(
        &bytes[dst_offset..dst_offset + n],
        expected.as_slice(),
        "n={n}, dst={dst_alignment}, src={src_alignment}"
    );
    assert!(
        bytes[..dst_offset].iter().all(|&byte| byte == 0xa5),
        "before destination: n={n}, dst={dst_alignment}, src={src_alignment}"
    );
    assert!(
        bytes[dst_offset + n..].iter().all(|&byte| byte == 0xa5),
        "after destination: n={n}, dst={dst_alignment}, src={src_alignment}"
    );
}

fn read_bounds_case(n: usize, dst_alignment: usize, src_alignment: usize) {
    // Only [src, src+n) is initialized; Miri catches wider source loads.
    let mut source = vec![MaybeUninit::<u32>::uninit(); (n + 32).div_ceil(4)];
    let mut destination = vec![MaybeUninit::<u32>::uninit(); (n + 32).div_ceil(4)];
    let src = unsafe { source.as_mut_ptr().cast::<u8>().add(8 + src_alignment) };
    let dst = unsafe {
        destination
            .as_mut_ptr()
            .cast::<u8>()
            .add(12 + dst_alignment)
    };
    let expected = pattern(n, dst_alignment, src_alignment);
    assert!(8 + src_alignment + n <= source.len() * 4);
    assert!(12 + dst_alignment + n <= destination.len() * 4);
    assert_eq!(src.addr() % 4, src_alignment);
    assert_eq!(dst.addr() % 4, dst_alignment);
    for (i, &byte) in expected.iter().enumerate() {
        unsafe { src.add(i).write(byte) };
    }

    let returned = unsafe { crate::memcpy::memcpy_impl(dst, src, n) };
    assert_eq!(
        returned, dst,
        "n={n}, dst={dst_alignment}, src={src_alignment}"
    );
    for (i, &byte) in expected.iter().enumerate() {
        assert_eq!(
            unsafe { dst.add(i).read() },
            byte,
            "n={n}, dst={dst_alignment}, src={src_alignment}, byte={i}"
        );
    }
}

#[test]
fn test_memcpy_bounds_sentinels() {
    #[cfg(miri)]
    let sizes = (0..=72).chain([100, 128, 144]);
    #[cfg(not(miri))]
    let sizes = (0..=300).chain([511, 512, 513, 1023, 1024, 1027, 4099]);
    for n in sizes {
        for dst_alignment in 0..4 {
            for src_alignment in 0..4 {
                sentinel_case(n, dst_alignment, src_alignment);
            }
        }
    }
}

#[test]
fn test_memcpy_bounds_reads() {
    #[cfg(miri)]
    let sizes = (0..=72).chain([100, 128, 144]);
    #[cfg(not(miri))]
    let sizes = (0..=72).chain([100, 144, 255]);
    for n in sizes {
        for dst_alignment in 0..4 {
            for src_alignment in 0..4 {
                read_bounds_case(n, dst_alignment, src_alignment);
            }
        }
    }
}
