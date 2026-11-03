/// Copies forward: before storing destination byte `j`, all source bytes at offsets
/// below `j` that will be read have already been loaded. `memmove_impl` relies on
/// this order when `dest < src` and the ranges overlap; its forward-overlap tests
/// enforce it. The mismatched path keeps it by `copy_merge`'s invariant. The
/// `memcpy_via_precompile` path keeps it too: both pointers are 32-byte aligned
/// there, so overlapping ranges are at least 32 bytes apart.
#[allow(dead_code)]
#[inline(always)]
pub(crate) unsafe fn memcpy_impl(dest: *mut u8, src: *const u8, n: usize) -> *mut u8 {
    #[cfg(not(target_endian = "little"))]
    {
        compile_error!("unsupported arch - only LE is supported");
    }

    // Somewhat opinionated implementation of memcopy. We will try to unroll where we can,
    // and aim for good "happy cases" where dest % size_of::<usize> == src % size_of::<usize>

    let return_value = dest;

    // previously Rust was bad in having mut variables in input parameters, so let's just
    // see how compiler handles it at the end
    let mut dest = dest;
    let mut src = src;
    let mut n = n;

    // first happy case to align both source and dest to the word size

    #[cfg(all(target_arch = "riscv32", feature = "memcpy_via_precompile"))]
    {
        if src.addr() >= common_constants::rom::ROM_BYTE_SIZE
            && src.addr() % 32 == 0
            && dest.addr() % 32 == 0
            && n >= 32
        {
            let MEMCPY_CONTROL_VALUE: u32 =
                const { 1 << common_constants::delegation_types::MEMCOPY_BIT_IDX };
            while n >= 32 {
                let _ = common_constants::delegation_types::bigint_csr_trigger_delegation(
                    dest.cast::<u32>(),
                    src.cast::<u32>(),
                    MEMCPY_CONTROL_VALUE,
                );

                dest = dest.add(32);
                src = src.add(32);
                n -= 32;
            }

            if n == 0 {
                return return_value;
            }
        }
    }

    const WORD_SIZE: usize = const { core::mem::size_of::<u32>() };

    if (dest.addr() | src.addr()).is_multiple_of(WORD_SIZE) {
        copy_aligned_words(dest, src, n);
    } else if (dest.addr() ^ src.addr()).is_multiple_of(WORD_SIZE) {
        // Same misalignment: one byte and then one u16 align both pointers.
        if n < WORD_SIZE {
            copy_bytes_lt4(dest, src, n);
            return return_value;
        }
        if src.addr() & 1 != 0 {
            dest.write(src.read());
            src = src.add(1);
            dest = dest.add(1);
            n -= 1;
        }
        if src.addr() & 2 != 0 {
            dest.cast::<u16>().write(src.cast::<u16>().read());
            src = src.add(2);
            dest = dest.add(2);
            n -= 2;
        }
        copy_aligned_words(dest, src, n);
    } else {
        copy_mismatched(dest, src, n);
    }

    return_value
}

/// # Safety
/// `memcpy` contract for `n` bytes, and `n == 0 || (dest and src are both 4-aligned)`.
#[inline(always)]
unsafe fn copy_aligned_words(dest: *mut u8, src: *const u8, mut n: usize) {
    const WORD_SIZE: usize = const { core::mem::size_of::<u32>() };
    // start via unrolling. Unroll size choice is somewhat arbitrary, but 16 as the maximum seems the best as:
    // - copy is done as mem -> reg -> mem, so we need 16 available registers + values of source, dest and n itself
    // - offset of 16 * core::mem::size_of::<u32>() is encodable as IMM in the ISA

    // NOTE: in practice compiler uses just single register to load to it and then store, so no efficient pipeline loading
    // by LLVM
    // 6ec: 0005a703     	lw	a4, 0x0(a1)
    // 6f0: 00e52023     	sw	a4, 0x0(a0)
    // 6f4: 0045a703     	lw	a4, 0x4(a1)
    // 6f8: 00e52223     	sw	a4, 0x4(a0)

    if n > 0 {
        debug_assert_eq!(src.addr() % WORD_SIZE, 0);
        debug_assert_eq!(dest.addr() % WORD_SIZE, 0);
    }

    let mut src = src.cast::<u32>();
    let mut dest = dest.cast::<u32>();

    {
        const BYTE_COPY_SIZE: usize = WORD_SIZE * 16;
        const WORD_COPY_SIZE: usize = 16;
        while n >= 16 * WORD_SIZE {
            debug_assert_eq!(src.addr() % WORD_SIZE, 0);
            debug_assert_eq!(dest.addr() % WORD_SIZE, 0);

            seq_macro::seq!(N in 0..16 {
                dest.add(N).write(src.add(N).read());
            });

            src = src.add(WORD_COPY_SIZE);
            dest = dest.add(WORD_COPY_SIZE);
            n -= BYTE_COPY_SIZE;
        }
    }

    // continue unrolling, but now we know that at most we need 1 iteration each time

    core::hint::assert_unchecked(n < 64);

    {
        const M: usize = 3;
        const WORD_COPY_SIZE: usize = 1 << M;
        const BYTE_COPY_SIZE: usize = WORD_COPY_SIZE * WORD_SIZE;

        if n & BYTE_COPY_SIZE > 0 {
            debug_assert_eq!(src.addr() % WORD_SIZE, 0);
            debug_assert_eq!(dest.addr() % WORD_SIZE, 0);
            seq_macro::seq!(N in 0..8 {
                dest.add(N).write(src.add(N).read());
            });

            src = src.add(WORD_COPY_SIZE);
            dest = dest.add(WORD_COPY_SIZE);
        }
    }

    {
        const M: usize = 2;
        const WORD_COPY_SIZE: usize = 1 << M;
        const BYTE_COPY_SIZE: usize = WORD_COPY_SIZE * WORD_SIZE;

        if n & BYTE_COPY_SIZE > 0 {
            debug_assert_eq!(src.addr() % WORD_SIZE, 0);
            debug_assert_eq!(dest.addr() % WORD_SIZE, 0);
            seq_macro::seq!(N in 0..4 {
                dest.add(N).write(src.add(N).read());
            });

            src = src.add(WORD_COPY_SIZE);
            dest = dest.add(WORD_COPY_SIZE);
        }
    }

    {
        const M: usize = 1;
        const WORD_COPY_SIZE: usize = 1 << M;
        const BYTE_COPY_SIZE: usize = WORD_COPY_SIZE * WORD_SIZE;

        if n & BYTE_COPY_SIZE > 0 {
            debug_assert_eq!(src.addr() % WORD_SIZE, 0);
            debug_assert_eq!(dest.addr() % WORD_SIZE, 0);
            seq_macro::seq!(N in 0..2 {
                dest.add(N).write(src.add(N).read());
            });

            src = src.add(WORD_COPY_SIZE);
            dest = dest.add(WORD_COPY_SIZE);
        }
    }

    {
        const M: usize = 0;
        const WORD_COPY_SIZE: usize = 1 << M;
        const BYTE_COPY_SIZE: usize = WORD_COPY_SIZE * WORD_SIZE;

        if n & BYTE_COPY_SIZE > 0 {
            debug_assert_eq!(src.addr() % WORD_SIZE, 0);
            debug_assert_eq!(dest.addr() % WORD_SIZE, 0);
            dest.write(src.read());

            src = src.add(WORD_COPY_SIZE);
            dest = dest.add(WORD_COPY_SIZE);
        }
    }

    // and copy the tail - by by u16 and by byte
    let mut src = src.cast::<u16>();
    let mut dest = dest.cast::<u16>();
    {
        const BYTE_COPY_SIZE: usize = 2;

        if n & BYTE_COPY_SIZE > 0 {
            debug_assert_eq!(src.addr() % core::mem::size_of::<u16>(), 0);
            debug_assert_eq!(dest.addr() % core::mem::size_of::<u16>(), 0);

            dest.write(src.read());

            src = src.add(1);
            dest = dest.add(1);
        }
    }

    let src = src.cast::<u8>();
    let dest = dest.cast::<u8>();
    if n & 1 > 0 {
        dest.write(src.read());
    }
}

/// # Safety
/// `memcpy` contract for `n` bytes, and `(dest ^ src) % 4 != 0`.
#[inline(always)]
unsafe fn copy_mismatched(mut dest: *mut u8, mut src: *const u8, mut n: usize) {
    debug_assert!(!(dest.addr() ^ src.addr()).is_multiple_of(4));
    // Below 32 bytes the byte copy is cheaper than the merge setup (measured).
    if n < 32 {
        copy_bytes(dest, src, n);
        return;
    }

    if src.addr().is_multiple_of(4) {
        // The first source word is inside the source (n >= 32): its low bytes are the
        // destination head and its high bytes the first `prev`.
        let w = src.cast::<u32>().read();
        let p = src.add(4);
        let q = n - 4;
        match dest.addr() % 4 {
            1 => {
                dest.write(w as u8);
                dest.add(1).write((w >> 8) as u8);
                dest.add(2).write((w >> 16) as u8);
                merge_words::<3>(dest.add(3), p, q, w >> 24);
            }
            2 => {
                dest.write(w as u8);
                dest.add(1).write((w >> 8) as u8);
                merge_words::<2>(dest.add(2), p, q, w >> 16);
            }
            _ => {
                dest.write(w as u8);
                merge_words::<1>(dest.add(1), p, q, w >> 8);
            }
        }
        return;
    }

    // Align the destination with byte copies only (the source is misaligned
    // relative to it).
    let head = dest.addr().wrapping_neg() % 4;
    match head {
        0 => {}
        1 => dest.write(src.read()),
        2 => {
            seq_macro::seq!(N in 0..2 {
                dest.add(N).write(src.add(N).read());
            });
        }
        _ => {
            seq_macro::seq!(N in 0..3 {
                dest.add(N).write(src.add(N).read());
            });
        }
    }
    dest = dest.add(head);
    src = src.add(head);
    n -= head;

    debug_assert_eq!(dest.addr() % 4, 0);
    match src.addr() % 4 {
        1 => copy_merge::<1>(dest, src, n),
        2 => copy_merge::<2>(dest, src, n),
        3 => copy_merge::<3>(dest, src, n),
        _ => core::hint::unreachable_unchecked(),
    }
}

/// Copies `n` bytes from `s` (`s % 4 == R`) to the 4-aligned `d`, merging aligned source
/// words. With `L = 4 - R` and `o` destination bytes merged so far: `p = s + o + L`,
/// `prev` holds source[o, o + L), and a step stores [o, o + 4) after loading
/// source[o + L, o + L + 4); every later load starts at or above `o + 4` (including the
/// short-tail re-read), which is the forward order `memcpy_impl` promises.
///
/// # Safety
/// `memcpy` contract for `n` bytes, `d % 4 == 0`, `s % 4 == R` and `n >= L`.
#[inline(always)]
unsafe fn copy_merge<const R: usize>(d: *mut u8, s: *const u8, n: usize) {
    const { assert!(1 <= R && R <= 3) };
    const WORD_SIZE: usize = const { core::mem::size_of::<u32>() };
    let l = WORD_SIZE - R;
    debug_assert_eq!(d.addr() % WORD_SIZE, 0);
    debug_assert_eq!(s.addr() % WORD_SIZE, R);
    debug_assert!(n >= l);

    // The first L bytes are loaded without reading before s.
    let prev = match R {
        1 => u32::from(s.read()) | (u32::from(s.add(1).cast::<u16>().read()) << 8),
        2 => u32::from(s.cast::<u16>().read()),
        3 => u32::from(s.read()),
        _ => core::hint::unreachable_unchecked(),
    };
    merge_words::<R>(d, s.add(l), n - l, prev);
}

/// The word loop of `copy_merge`: `p` is 4-aligned, `q` source bytes remain at and above
/// `p`, and `prev` holds the `L = 4 - R` source bytes just below `p` in its low lanes.
///
/// # Safety
/// `memcpy` contract for the `L + q` bytes from `p - L` to `d`, `d % 4 == 0`, `p % 4 == 0`.
#[inline(always)]
unsafe fn merge_words<const R: usize>(
    mut d: *mut u8,
    mut p: *const u8,
    mut q: usize,
    mut prev: u32,
) {
    const { assert!(1 <= R && R <= 3) };
    const WORD_SIZE: usize = const { core::mem::size_of::<u32>() };
    let l = WORD_SIZE - R;
    debug_assert_eq!(d.addr() % WORD_SIZE, 0);
    debug_assert_eq!(p.addr() % WORD_SIZE, 0);

    while q >= 64 {
        seq_macro::seq!(N in 0..16 {
            let w = p.cast::<u32>().read();
            d.cast::<u32>().write(prev | (w << (8 * l)));
            prev = w >> (8 * R);
            p = p.add(4);
            d = d.add(4);
        });
        q -= 64;
    }
    if q & 32 != 0 {
        seq_macro::seq!(N in 0..8 {
            let w = p.cast::<u32>().read();
            d.cast::<u32>().write(prev | (w << (8 * l)));
            prev = w >> (8 * R);
            p = p.add(4);
            d = d.add(4);
        });
    }
    if q & 16 != 0 {
        seq_macro::seq!(N in 0..4 {
            let w = p.cast::<u32>().read();
            d.cast::<u32>().write(prev | (w << (8 * l)));
            prev = w >> (8 * R);
            p = p.add(4);
            d = d.add(4);
        });
    }
    if q & 8 != 0 {
        seq_macro::seq!(N in 0..2 {
            let w = p.cast::<u32>().read();
            d.cast::<u32>().write(prev | (w << (8 * l)));
            prev = w >> (8 * R);
            p = p.add(4);
            d = d.add(4);
        });
    }
    if q & 4 != 0 {
        let w = p.cast::<u32>().read();
        d.cast::<u32>().write(prev | (w << (8 * l)));
        prev = w >> (8 * R);
        p = p.add(4);
        d = d.add(4);
    }

    // The blocks above consumed q & !3; the logical source position is p - L.
    let mut q = q & 3;
    if q >= R {
        let narrow = match R {
            1 => u32::from(p.read()),
            2 => u32::from(p.cast::<u16>().read()),
            3 => u32::from(p.cast::<u16>().read()) | (u32::from(p.add(2).read()) << 16),
            _ => core::hint::unreachable_unchecked(),
        };
        d.cast::<u32>().write(prev | (narrow << (8 * l)));
        d = d.add(4);
        p = p.add(R);
        q -= R;
        copy_bytes_lt4(d, p, q);
    } else {
        // p - L is at or after s; only L + q <= 3 bytes remain.
        copy_bytes_lt4(d, p.sub(l), l + q);
    }
}

/// # Safety
/// `memcpy` contract for `n < 32` bytes.
#[inline(always)]
unsafe fn copy_bytes(mut dest: *mut u8, mut src: *const u8, n: usize) {
    debug_assert!(n < 32);
    if n & 16 != 0 {
        seq_macro::seq!(N in 0..16 {
            dest.add(N).write(src.add(N).read());
        });
        dest = dest.add(16);
        src = src.add(16);
    }
    if n & 8 != 0 {
        seq_macro::seq!(N in 0..8 {
            dest.add(N).write(src.add(N).read());
        });
        dest = dest.add(8);
        src = src.add(8);
    }
    if n & 4 != 0 {
        seq_macro::seq!(N in 0..4 {
            dest.add(N).write(src.add(N).read());
        });
        dest = dest.add(4);
        src = src.add(4);
    }
    if n & 2 != 0 {
        seq_macro::seq!(N in 0..2 {
            dest.add(N).write(src.add(N).read());
        });
        dest = dest.add(2);
        src = src.add(2);
    }
    if n & 1 != 0 {
        dest.write(src.read());
    }
}

/// # Safety
/// `memcpy` contract for `n < 4` bytes.
#[inline(always)]
unsafe fn copy_bytes_lt4(dest: *mut u8, src: *const u8, n: usize) {
    debug_assert!(n < 4);
    if n & 2 != 0 {
        seq_macro::seq!(N in 0..2 {
            dest.add(N).write(src.add(N).read());
        });
    }
    if n & 1 != 0 {
        dest.add(n & 2).write(src.add(n & 2).read());
    }
}
