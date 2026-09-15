#[allow(dead_code)]
#[inline(always)]
pub(crate) unsafe fn memset_impl(dest: *mut u8, value: u32, n: usize) -> *mut u8 {
    #[cfg(not(target_endian = "little"))]
    {
        compile_error!("unsupported arch - only LE is supported");
    }

    // Somewhat opinionated implementation of memset. We will try to unroll where we can,
    // and aim for good "happy cases" where dest is word-aligned

    let return_value = dest;

    // previously Rust was bad in having mut variables in input parameters, so let's just
    // see how compiler handles it at the end
    let mut dest = dest;
    let mut n = n;

    const WORD_SIZE: usize = const { core::mem::size_of::<u32>() };

    // align head
    while n > 0 && dest.addr() % WORD_SIZE != 0 {
        dest.write(value as u8);
        dest = dest.add(1);
        n -= 1;
    }

    // quickly finish tail
    let mut tail = n % WORD_SIZE;
    let mut tail_ptr = dest.add(n).sub(1);
    n -= tail; // can not underflow
    while tail > 0 {
        tail_ptr.write(value as u8);
        tail_ptr = tail_ptr.sub(1);
        tail -= 1;
    }

    if n == 0 {
        return return_value;
    }

    // here we only have to work by aligned word
    {
        debug_assert!(n > 0);
        debug_assert_eq!(dest.addr() % WORD_SIZE, 0);
        debug_assert_eq!(n % WORD_SIZE, 0);

        let mut dest = dest.cast::<u32>();
        let u32_fill_value = cfg_select! {
            all(target_arch = "riscv32", target_feature = "m") => {
                0x01_01_01_01u32.wrapping_mul(value as u32)
            }
            target_arch = "riscv32" => {
                ((value as u32) << 24)
                    | ((value as u32) << 16)
                    | ((value as u32) << 8)
                    | (value as u32)
            }
            _ => 0x01_01_01_01u32.wrapping_mul(value as u32),
        };

        {
            const BYTE_COPY_SIZE: usize = WORD_SIZE * 16;
            const WORD_COPY_SIZE: usize = 16;
            while n >= 16 * WORD_SIZE {
                debug_assert_eq!(dest.addr() % WORD_SIZE, 0);
                seq_macro::seq!(N in 0..16 {
                    dest.add(N).write(u32_fill_value);
                });
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
                debug_assert_eq!(dest.addr() % WORD_SIZE, 0);
                seq_macro::seq!(N in 0..8 {
                    dest.add(N).write(u32_fill_value);
                });
                dest = dest.add(WORD_COPY_SIZE);
            }
        }

        {
            const M: usize = 2;
            const WORD_COPY_SIZE: usize = 1 << M;
            const BYTE_COPY_SIZE: usize = WORD_COPY_SIZE * WORD_SIZE;

            if n & BYTE_COPY_SIZE > 0 {
                debug_assert_eq!(dest.addr() % WORD_SIZE, 0);
                seq_macro::seq!(N in 0..4 {
                    dest.add(N).write(u32_fill_value);
                });
                dest = dest.add(WORD_COPY_SIZE);
            }
        }

        {
            const M: usize = 1;
            const WORD_COPY_SIZE: usize = 1 << M;
            const BYTE_COPY_SIZE: usize = WORD_COPY_SIZE * WORD_SIZE;

            if n & BYTE_COPY_SIZE > 0 {
                debug_assert_eq!(dest.addr() % WORD_SIZE, 0);
                seq_macro::seq!(N in 0..2 {
                    dest.add(N).write(u32_fill_value);
                });
                dest = dest.add(WORD_COPY_SIZE);
            }
        }

        {
            const M: usize = 0;
            const WORD_COPY_SIZE: usize = 1 << M;
            const BYTE_COPY_SIZE: usize = WORD_COPY_SIZE * WORD_SIZE;

            if n & BYTE_COPY_SIZE > 0 {
                debug_assert_eq!(dest.addr() % WORD_SIZE, 0);
                dest.write(u32_fill_value);
                let _dest = dest.add(WORD_COPY_SIZE);
            }
        }
    }

    return_value
}
