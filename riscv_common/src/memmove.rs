/// Uses the forward-order contract of `memcpy_impl` when `dest` is below `src`
/// or the ranges are disjoint. Otherwise copies backward. With mismatched word
/// alignments, the backward path composes each destination word from an aligned
/// source word below it and the already loaded bytes above it; neither load
/// reaches outside the source range.
#[allow(dead_code)]
// seq! expands reverse offsets to literals, including intentional zero/equal operands.
#[allow(clippy::eq_op, clippy::identity_op)]
#[inline(always)]
pub(crate) unsafe fn memmove_impl(dest: *mut u8, src: *const u8, n: usize) -> *mut u8 {
    #[cfg(not(target_endian = "little"))]
    {
        compile_error!("unsupported arch - only LE is supported");
    }

    if dest.addr().wrapping_sub(src.addr()) >= n {
        return crate::memcpy::memcpy_impl(dest, src, n);
    }

    let return_value = dest;
    let mut d = dest.add(n);
    let mut s = src.add(n);
    let mut n = n;

    // Align the destination end. The source end follows if their alignments match.
    while n > 0 && !d.addr().is_multiple_of(4) {
        d = d.sub(1);
        s = s.sub(1);
        d.write(s.read());
        n -= 1;
    }
    if n == 0 {
        return return_value;
    }

    if d.addr() % 4 == s.addr() % 4 {
        debug_assert_eq!(d.addr() % 4, 0);
        debug_assert_eq!(s.addr() % 4, 0);

        let mut d = d.cast::<u32>();
        let mut s = s.cast::<u32>();

        while n >= 64 {
            d = d.sub(16);
            s = s.sub(16);
            debug_assert_eq!(d.addr() % 4, 0);
            debug_assert_eq!(s.addr() % 4, 0);
            // Descending stores preserve source words even for a one-word overlap.
            seq_macro::seq!(N in 0..16 {
                d.add(15 - N).write(s.add(15 - N).read());
            });
            n -= 64;
        }

        if n & 32 != 0 {
            d = d.sub(8);
            s = s.sub(8);
            seq_macro::seq!(N in 0..8 {
                d.add(7 - N).write(s.add(7 - N).read());
            });
        }
        if n & 16 != 0 {
            d = d.sub(4);
            s = s.sub(4);
            seq_macro::seq!(N in 0..4 {
                d.add(3 - N).write(s.add(3 - N).read());
            });
        }
        if n & 8 != 0 {
            d = d.sub(2);
            s = s.sub(2);
            seq_macro::seq!(N in 0..2 {
                d.add(1 - N).write(s.add(1 - N).read());
            });
        }
        if n & 4 != 0 {
            d = d.sub(1);
            s = s.sub(1);
            d.write(s.read());
        }

        // The remaining one to three bytes lie below the aligned words.
        if n & 3 != 0 {
            let mut d = d.cast::<u8>();
            let mut s = s.cast::<u8>();
            if n & 2 != 0 {
                d = d.sub(2);
                s = s.sub(2);
                debug_assert_eq!(d.addr() % 2, 0);
                debug_assert_eq!(s.addr() % 2, 0);
                d.cast::<u16>().write(s.cast::<u16>().read());
            }
            if n & 1 != 0 {
                d = d.sub(1);
                s = s.sub(1);
                d.write(s.read());
            }
        }
    } else {
        debug_assert_eq!(d.addr() % 4, 0);
        debug_assert_ne!(s.addr() % 4, 0);
        match s.addr() % 4 {
            1 => copy_misaligned::<1>(d, s, n),
            2 => copy_misaligned::<2>(d, s, n),
            3 => copy_misaligned::<3>(d, s, n),
            _ => core::hint::unreachable_unchecked(),
        }
    }

    return_value
}

#[inline(always)]
unsafe fn copy_misaligned<const R: usize>(mut d: *mut u8, mut s: *const u8, mut n: usize) {
    debug_assert_eq!(d.addr() % 4, 0);
    debug_assert_eq!(s.addr() % 4, R);

    if n >= R + 4 {
        // The guard keeps both the first aligned word and the R-byte head in range.
        let mut s_al = s.sub(R);
        debug_assert_eq!(s_al.addr() % 4, 0);
        let mut hi = match R {
            1 => u32::from(s_al.read()),
            2 => u32::from(s_al.cast::<u16>().read()),
            3 => u32::from(s_al.cast::<u16>().read()) | (u32::from(s_al.add(2).read()) << 16),
            _ => core::hint::unreachable_unchecked(),
        };
        let mut m = n - R;

        while m >= 16 {
            seq_macro::seq!(N in 0..4 {
                s_al = s_al.sub(4);
                d = d.sub(4);
                debug_assert_eq!(s_al.addr() % 4, 0);
                debug_assert_eq!(d.addr() % 4, 0);
                let lo = s_al.cast::<u32>().read();
                d.cast::<u32>().write((lo >> (8 * R)) | (hi << (32 - 8 * R)));
                hi = lo;
            });
            m -= 16;
        }
        while m >= 4 {
            s_al = s_al.sub(4);
            d = d.sub(4);
            debug_assert_eq!(s_al.addr() % 4, 0);
            debug_assert_eq!(d.addr() % 4, 0);
            let lo = s_al.cast::<u32>().read();
            d.cast::<u32>()
                .write((lo >> (8 * R)) | (hi << (32 - 8 * R)));
            hi = lo;
            m -= 4;
        }

        // Only R plus at most three source bytes remain below the word stores.
        s = s_al.add(R);
        n = m + R;
    }

    while n > 0 {
        d = d.sub(1);
        s = s.sub(1);
        d.write(s.read());
        n -= 1;
    }
}
