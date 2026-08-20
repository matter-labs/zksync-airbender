pub(crate) const P: u128 = 0x7800_0001;
const MONT_K: u32 = 0x77ff_ffff;
const R: u128 = 1u128 << 32;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct U96 {
    lo: u32,
    mid: u32,
    hi: u32,
}

impl U96 {
    pub(crate) fn add_product(&mut self, a: u32, b: u32) {
        let before = self.as_u128();
        let product = u64::from(a) * u64::from(b);
        let (lo, carry_lo) = self.lo.overflowing_add(product as u32);
        let (mid0, carry_mid0) = self.mid.overflowing_add((product >> 32) as u32);
        let (mid, carry_mid1) = mid0.overflowing_add(u32::from(carry_lo));
        self.lo = lo;
        self.mid = mid;
        self.hi = self
            .hi
            .checked_add(u32::from(carry_mid0) + u32::from(carry_mid1))
            .unwrap();
        assert_eq!(self.as_u128(), before + u128::from(a) * u128::from(b));
    }

    pub(crate) fn as_u128(self) -> u128 {
        u128::from(self.lo) | (u128::from(self.mid) << 32) | (u128::from(self.hi) << 64)
    }

    pub(crate) const fn high_word(self) -> u32 {
        self.hi
    }
}

pub(crate) fn red_wide_model(low: u64) -> u32 {
    let m = (low as u32).wrapping_mul(MONT_K);
    let quotient = (u128::from(low) + u128::from(m) * P) >> 32;
    let mut quotient = if quotient >= R {
        quotient - R + (R % P)
    } else {
        quotient
    };
    if quotient >= P {
        quotient -= P;
    }
    if quotient >= P {
        quotient -= P;
    }
    assert!(quotient < P);
    quotient as u32
}

pub(crate) fn reduce_u96_raw(value: U96) -> u32 {
    let low = u64::from(value.lo) | (u64::from(value.mid) << 32);
    ((u128::from(red_wide_model(low)) + u128::from(value.hi) * (R % P)) % P) as u32
}

fn mod_pow(mut base: u128, mut exponent: u128) -> u128 {
    let mut result = 1u128;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = result * base % P;
        }
        base = base * base % P;
        exponent >>= 1;
    }
    result
}

pub(crate) fn redc_reference(value: u128) -> u32 {
    (value % P * mod_pow(R % P, P - 2) % P) as u32
}

fn non_residue_raw(value: u32) -> u32 {
    (u128::from(value) * 11 % P) as u32
}

pub(crate) fn accumulate_e4_product(out: &mut [U96; 4], a: [u32; 4], b: [u32; 4]) {
    let a1n = non_residue_raw(a[1]);
    let a2n = non_residue_raw(a[2]);
    let a3n = non_residue_raw(a[3]);

    out[0].add_product(a[0], b[0]);
    out[0].add_product(a1n, b[1]);
    out[0].add_product(a2n, b[3]);
    out[0].add_product(a3n, b[2]);

    out[1].add_product(a[0], b[1]);
    out[1].add_product(a[1], b[0]);
    out[1].add_product(a[2], b[2]);
    out[1].add_product(a3n, b[3]);

    out[2].add_product(a[0], b[2]);
    out[2].add_product(a1n, b[3]);
    out[2].add_product(a[2], b[0]);
    out[2].add_product(a3n, b[1]);

    out[3].add_product(a[0], b[3]);
    out[3].add_product(a[1], b[2]);
    out[3].add_product(a[2], b[1]);
    out[3].add_product(a[3], b[0]);
}

#[test]
fn u96_add_product_propagates_both_carries() {
    let mut value = U96::default();
    value.add_product(u32::MAX, u32::MAX);
    value.add_product(u32::MAX, u32::MAX);

    assert_eq!(
        value,
        U96 {
            lo: 2,
            mid: 0xffff_fffc,
            hi: 1,
        }
    );
    assert_eq!(value.as_u128(), 36_893_488_130_239_234_050);
}

#[test]
fn reduction_maps_montgomery_r_to_one() {
    let montgomery_r = U96 {
        lo: 0,
        mid: 1,
        hi: 0,
    };

    assert_eq!(reduce_u96_raw(montgomery_r), 1);
}

#[test]
fn e4_product_wires_all_four_output_rows() {
    let mut out = [U96::default(); 4];
    accumulate_e4_product(&mut out, [1, 2, 3, 4], [5, 6, 7, 8]);

    assert_eq!(out[0].as_u128(), 709);
    assert_eq!(out[1].as_u128(), 389);
    assert_eq!(out[2].as_u128(), 462);
    assert_eq!(out[3].as_u128(), 60);
}

#[test]
fn reduction_matches_reference_at_adversarial_boundaries() {
    let lows = [
        u64::MAX,
        (P as u64) * (1u64 << 32) - 1,
        (P as u64) * (1u64 << 32),
        (P as u64) * (1u64 << 32) + 1,
        (4 * P * P) as u64,
    ];
    for low in lows {
        for hi in [0u32, 14, 20] {
            let value = U96 {
                lo: low as u32,
                mid: (low >> 32) as u32,
                hi,
            };
            assert_eq!(reduce_u96_raw(value), redc_reference(value.as_u128()));
        }
    }
}

#[test]
fn reduction_matches_reference_for_10_000_fixed_random_cases() {
    let mut state = 0x4d59_5df4_d0f3_3173u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };

    for _ in 0..10_000 {
        let low = next();
        let hi = (next() % 21) as u32;
        let value = U96 {
            lo: low as u32,
            mid: (low >> 32) as u32,
            hi,
        };
        assert_eq!(reduce_u96_raw(value), redc_reference(value.as_u128()));
    }
}

#[test]
fn proven_outer_bounds_are_68_and_69_bits() {
    let bf = 65 * (P - 1) * (P - 1);
    let full = 93 * (P - 1) * (P - 1);
    assert!(bf < (1u128 << 68) && bf >= (1u128 << 67));
    assert!(full < (1u128 << 69) && full >= (1u128 << 68));
    assert_eq!(bf >> 64, 14);
    assert_eq!(full >> 64, 20);
}

#[test]
fn bf_outer_fold_matches_literal_worst_case_bound() {
    let mut out = U96::default();
    for _ in 0..65 {
        out.add_product((P - 1) as u32, (P - 1) as u32);
    }

    assert_eq!(out.as_u128(), 263_460_578_201_174_016_000);
    assert_eq!(out.hi, 14);
    assert_eq!(
        reduce_u96_raw(out),
        redc_reference(263_460_578_201_174_016_000)
    );
}

#[test]
fn e4_products_match_1_000_direct_u128_references() {
    let mut state = 0xa076_1d64_78bd_642fu64;
    let mut next_limb = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state % P as u64) as u32
    };

    for _ in 0..1_000 {
        let a = [next_limb(), next_limb(), next_limb(), next_limb()];
        let b = [next_limb(), next_limb(), next_limb(), next_limb()];
        let mut out = [U96::default(); 4];
        accumulate_e4_product(&mut out, a, b);

        let a1n = u128::from(a[1]) * 11 % P;
        let a2n = u128::from(a[2]) * 11 % P;
        let a3n = u128::from(a[3]) * 11 % P;
        let expected = [
            u128::from(a[0]) * u128::from(b[0])
                + a1n * u128::from(b[1])
                + a2n * u128::from(b[3])
                + a3n * u128::from(b[2]),
            u128::from(a[0]) * u128::from(b[1])
                + u128::from(a[1]) * u128::from(b[0])
                + u128::from(a[2]) * u128::from(b[2])
                + a3n * u128::from(b[3]),
            u128::from(a[0]) * u128::from(b[2])
                + a1n * u128::from(b[3])
                + u128::from(a[2]) * u128::from(b[0])
                + a3n * u128::from(b[1]),
            u128::from(a[0]) * u128::from(b[3])
                + u128::from(a[1]) * u128::from(b[2])
                + u128::from(a[2]) * u128::from(b[1])
                + u128::from(a[3]) * u128::from(b[0]),
        ];

        for limb in 0..4 {
            assert_eq!(out[limb].as_u128(), expected[limb]);
            assert_eq!(reduce_u96_raw(out[limb]), redc_reference(expected[limb]));
        }
    }
}

#[test]
fn c_init_relocation_matches_all_selector_predicates_and_cells() {
    let mut wide_contributions = [[U96::default(); 4]; 3];
    let mut canonical_contributions = [[0u32; 4]; 3];

    for atom in 0..65u128 {
        let core = [
            (P - 1 - atom * 17) as u32,
            (P - 2 - atom * 19) as u32,
            (P - 3 - atom * 23) as u32,
            (P - 4 - atom * 29) as u32,
        ];
        for cell in 0..3u128 {
            let sum = (P - 1 - atom * 31 - cell * 101) as u32;
            for limb in 0..4 {
                wide_contributions[cell as usize][limb].add_product(core[limb], sum);
                let raw = u128::from(core[limb]) * u128::from(sum);
                canonical_contributions[cell as usize][limb] =
                    ((u128::from(canonical_contributions[cell as usize][limb])
                        + u128::from(redc_reference(raw)))
                        % P) as u32;
            }
        }
    }

    for atom in 0..7u128 {
        let core = [
            (P - 11 - atom * 37) as u32,
            (P - 13 - atom * 41) as u32,
            (P - 17 - atom * 43) as u32,
            (P - 19 - atom * 47) as u32,
        ];
        for cell in 0..3u128 {
            let sum = [
                (P - 23 - atom * 53 - cell * 103) as u32,
                (P - 29 - atom * 59 - cell * 107) as u32,
                (P - 31 - atom * 61 - cell * 109) as u32,
                (P - 37 - atom * 67 - cell * 113) as u32,
            ];
            accumulate_e4_product(&mut wide_contributions[cell as usize], core, sum);

            let a1n = u128::from(core[1]) * 11 % P;
            let a2n = u128::from(core[2]) * 11 % P;
            let a3n = u128::from(core[3]) * 11 % P;
            let direct = [
                u128::from(core[0]) * u128::from(sum[0])
                    + a1n * u128::from(sum[1])
                    + a2n * u128::from(sum[3])
                    + a3n * u128::from(sum[2]),
                u128::from(core[0]) * u128::from(sum[1])
                    + u128::from(core[1]) * u128::from(sum[0])
                    + u128::from(core[2]) * u128::from(sum[2])
                    + a3n * u128::from(sum[3]),
                u128::from(core[0]) * u128::from(sum[2])
                    + a1n * u128::from(sum[3])
                    + u128::from(core[2]) * u128::from(sum[0])
                    + a3n * u128::from(sum[1]),
                u128::from(core[0]) * u128::from(sum[3])
                    + u128::from(core[1]) * u128::from(sum[2])
                    + u128::from(core[2]) * u128::from(sum[1])
                    + u128::from(core[3]) * u128::from(sum[0]),
            ];
            for limb in 0..4 {
                canonical_contributions[cell as usize][limb] =
                    ((u128::from(canonical_contributions[cell as usize][limb])
                        + u128::from(redc_reference(direct[limb])))
                        % P) as u32;
            }
        }
    }

    let c_init = [0x0123_4567u32, 0x2345_6789, 0x3456_789a, 0x4567_89ab];
    for (infinity0, infinity1) in [(false, false), (false, true), (true, false), (true, true)] {
        for cell in 0..3 {
            for limb in 0..4 {
                assert!(wide_contributions[cell][limb].hi <= 20);
                let add_c_init = !infinity0 && !infinity1 && cell < 2;

                let mut canonical_path = if add_c_init { c_init[limb] } else { 0 };
                canonical_path = ((u128::from(canonical_path)
                    + u128::from(canonical_contributions[cell][limb]))
                    % P) as u32;

                let mut wide_path = reduce_u96_raw(wide_contributions[cell][limb]);
                if add_c_init {
                    wide_path = ((u128::from(wide_path) + u128::from(c_init[limb])) % P) as u32;
                }

                assert_eq!(wide_path, canonical_path);
            }
        }
    }
}
