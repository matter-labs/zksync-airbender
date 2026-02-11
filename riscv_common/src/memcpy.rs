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

    while n > 0 && src.addr() % WORD_SIZE != 0 {
        dest.write(src.read());
        src = src.add(1);
        dest = dest.add(1);
        n -= 1;
    }

    // So source is aligned to word size

    // Now happy case - both(!) source and destination are aligned

    if dest.addr() % WORD_SIZE == 0 {
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

        return return_value;
    }

    // Not so happy case - we need to read word, "glue it" with the previous one,
    // and then write back. We have extra consideration to make: as there is an opcode for aligned
    // u16 read/write in the ISA, then we may want to use load_u16 -> reg -> store_u16 (3 opcodes for 2 bytes),
    // instead of load_u32 -> reg -> shift -> shift_previous -> or -> write (6 opcodes for 4 bytes)

    // For simplicity we will stick to reading u32s, and will not unroll that much

    // NOTE: on bounds: we have somewhat "strage" bounds like 20 and 17/18/19 below - this way
    // we ensure that we do not access out of bounds of src/dest
    if n >= 20 {
        // NOTE: source is aligned
        debug_assert_eq!(src.addr() % WORD_SIZE, 0);

        const BYTE_COPY_SIZE: usize = 16;

        let mut word_0;
        let mut word_1;
        match dest.addr() % WORD_SIZE {
            1 => {
                word_0 = src.cast::<u32>().read();
                // we skip 3 bytes

                // byte copies to align dest, and then we read source, shift/glue and write words
                seq_macro::seq!(N in 0..3 {
                    dest.add(N).write(src.add(N).read());
                });
                dest = dest.add(3);
                src = src.add(3);
                n -= 3;

                // and now by word
                debug_assert_eq!(src.addr() % WORD_SIZE, 3);
                debug_assert_eq!(dest.addr() % WORD_SIZE, 0);

                // NOTE on shifts - we assume LE. We previously read memory [0x12, 0x34, 0x56, 0x78]
                // as integer 0x12345678, but we want to write only 0x12 into the lowest bits,
                // so we shift right the previous word, and left - recently read one

                while n >= 17 {
                    debug_assert_eq!(src.addr() % WORD_SIZE, 3);
                    debug_assert_eq!(dest.addr() % WORD_SIZE, 0);
                    seq_macro::seq!(N in 0..2 {
                        word_1 = src.add(1 + N * 8).cast::<u32>().read();
                        dest.cast::<u32>().add(0 + 2 * N).write(word_0 >> 24 | word_1 << 8);
                        word_0 = src.add(5 + N * 8).cast::<u32>().read();
                        dest.cast::<u32>().add(1 + 2 * N).write(word_1 >> 24 | word_0 << 8);
                    });

                    src = src.add(BYTE_COPY_SIZE);
                    dest = dest.add(BYTE_COPY_SIZE);
                    n -= BYTE_COPY_SIZE;
                }
            }
            2 => {
                word_0 = src.cast::<u32>().read();
                // we skip 2 bytes

                seq_macro::seq!(N in 0..2 {
                    dest.add(N).write(src.add(N).read());
                });
                dest = dest.add(2);
                src = src.add(2);
                n -= 2;

                debug_assert_eq!(src.addr() % WORD_SIZE, 2);
                debug_assert_eq!(dest.addr() % WORD_SIZE, 0);

                while n >= 18 {
                    debug_assert_eq!(src.addr() % WORD_SIZE, 2);
                    debug_assert_eq!(dest.addr() % WORD_SIZE, 0);
                    seq_macro::seq!(N in 0..2 {
                        word_1 = src.add(2 + N * 8).cast::<u32>().read();
                        dest.cast::<u32>().add(0 + 2 * N).write(word_0 >> 16 | word_1 << 16);
                        word_0 = src.add(6 + N * 8).cast::<u32>().read();
                        dest.cast::<u32>().add(1 + 2 * N).write(word_1 >> 16 | word_0 << 16);
                    });

                    src = src.add(BYTE_COPY_SIZE);
                    dest = dest.add(BYTE_COPY_SIZE);
                    n -= BYTE_COPY_SIZE;
                }
            }
            3 => {
                word_0 = src.cast::<u32>().read();
                // we skip 1 byte

                dest.write(src.read());
                dest = dest.add(1);
                src = src.add(1);
                n -= 1;

                debug_assert_eq!(src.addr() % WORD_SIZE, 1);
                debug_assert_eq!(dest.addr() % WORD_SIZE, 0);

                while n >= 19 {
                    debug_assert_eq!(src.addr() % WORD_SIZE, 1);
                    debug_assert_eq!(dest.addr() % WORD_SIZE, 0);
                    seq_macro::seq!(N in 0..2 {
                        word_1 = src.add(3 + N * 8).cast::<u32>().read();
                        dest.cast::<u32>().add(0 + 2 * N).write(word_0 >> 8 | word_1 << 24);
                        word_0 = src.add(7 + N * 8).cast::<u32>().read();
                        dest.cast::<u32>().add(1 + 2 * N).write(word_1 >> 8 | word_0 << 24);
                    });

                    src = src.add(BYTE_COPY_SIZE);
                    dest = dest.add(BYTE_COPY_SIZE);
                    n -= BYTE_COPY_SIZE;
                }
            }
            _ => {
                core::hint::unreachable_unchecked();
            }
        }
    }

    core::hint::assert_unchecked(n < 32);

    // and now just byte copy tail
    {
        const BYTE_COPY_SIZE: usize = 16;

        if n & BYTE_COPY_SIZE > 0 {
            seq_macro::seq!(N in 0..16 {
                dest.add(N).write(src.add(N).read());
            });

            src = src.add(BYTE_COPY_SIZE);
            dest = dest.add(BYTE_COPY_SIZE);
        }
    }
    {
        const BYTE_COPY_SIZE: usize = 8;

        if n & BYTE_COPY_SIZE > 0 {
            seq_macro::seq!(N in 0..8 {
                dest.add(N).write(src.add(N).read());
            });

            src = src.add(BYTE_COPY_SIZE);
            dest = dest.add(BYTE_COPY_SIZE);
        }
    }
    {
        const BYTE_COPY_SIZE: usize = 4;

        if n & BYTE_COPY_SIZE > 0 {
            seq_macro::seq!(N in 0..4 {
                dest.add(N).write(src.add(N).read());
            });

            src = src.add(BYTE_COPY_SIZE);
            dest = dest.add(BYTE_COPY_SIZE);
        }
    }
    {
        const BYTE_COPY_SIZE: usize = 2;

        if n & BYTE_COPY_SIZE > 0 {
            seq_macro::seq!(N in 0..2 {
                dest.add(N).write(src.add(N).read());
            });

            src = src.add(BYTE_COPY_SIZE);
            dest = dest.add(BYTE_COPY_SIZE);
        }
    }
    {
        if n & 1 > 0 {
            dest.write(src.read());
        }
    }

    return_value
}
