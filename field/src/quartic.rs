use super::*;
use rand::Rng;

#[cfg(not(target_arch = "riscv32"))]
#[derive(Clone, Copy, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C, align(16))]
pub struct Mersenne31Quartic {
    pub c0: Mersenne31Complex,
    pub c1: Mersenne31Complex,
}

#[cfg(target_arch = "riscv32")]
#[derive(Clone, Copy, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct Mersenne31Quartic {
    pub c0: Mersenne31Complex,
    pub c1: Mersenne31Complex,
}

const _: () = const {
    assert!(core::mem::size_of::<Mersenne31Quartic>() == 4 * core::mem::size_of::<u32>());

    #[cfg(not(target_arch = "riscv32"))]
    assert!(core::mem::align_of::<Mersenne31Quartic>() == 16);

    #[cfg(target_arch = "riscv32")]
    assert!(core::mem::align_of::<Mersenne31Quartic>() == 4);

    ()
};

impl Mersenne31Quartic {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn new(c0: Mersenne31Complex, c1: Mersenne31Complex) -> Self {
        Self { c0, c1 }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn from_array_of_base(els: [Mersenne31Field; 4]) -> Self {
        Self {
            c0: Mersenne31Complex {
                c0: els[0],
                c1: els[1],
            },
            c1: Mersenne31Complex {
                c0: els[2],
                c1: els[3],
            },
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub unsafe fn read_unaligned(base_ptr: *const Mersenne31Field) -> Self {
        let [c0, c1, c2, c3] = base_ptr.cast::<[Mersenne31Field; 4]>().read();
        Self {
            c0: Mersenne31Complex { c0: c0, c1: c1 },
            c1: Mersenne31Complex { c0: c2, c1: c3 },
        }
    }

    #[cfg(not(target_arch = "riscv32"))]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn project_ref_from_array(els: &'_ [Mersenne31Field; 4]) -> &'_ Self {
        if core::mem::align_of::<Self>() == core::mem::align_of::<Mersenne31Field>()
            && core::mem::size_of::<Self>() == core::mem::size_of::<Mersenne31Field>() * 4
        {
            // alignments and expected sized match, so we can just cast pointer
            unsafe { core::mem::transmute(els) }
        } else {
            unimplemented!()
        }
    }

    #[cfg(target_arch = "riscv32")]
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    pub const fn project_ref_from_array(els: &'_ [Mersenne31Field; 4]) -> &'_ Self {
        // alignments match, so we can just cast pointer
        unsafe { core::mem::transmute(els) }
    }
}

impl core::cmp::PartialEq for Mersenne31Quartic {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn eq(&self, other: &Self) -> bool {
        self.c0 == other.c0 && self.c1 == other.c1
    }
}

impl core::cmp::Eq for Mersenne31Quartic {}

impl core::default::Default for Mersenne31Quartic {
    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn default() -> Self {
        Self {
            c0: Mersenne31Complex::ZERO,
            c1: Mersenne31Complex::ZERO,
        }
    }
}

impl Rand for Mersenne31Quartic {
    fn random_element<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Self {
            c0: Rand::random_element(rng),
            c1: Rand::random_element(rng),
        }
    }
}

impl Field for Mersenne31Quartic {
    const ZERO: Self = Self {
        c0: Mersenne31Complex::ZERO,
        c1: Mersenne31Complex::ZERO,
    };

    const ONE: Self = Self {
        c0: Mersenne31Complex::ONE,
        c1: Mersenne31Complex::ZERO,
    };

    type CharField = Mersenne31Complex;

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn is_one(&self) -> bool {
        self.c0.is_one() && self.c1.is_zero()
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.c0.add_assign(&other.c0);
        self.c1.add_assign(&other.c1);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.c0.sub_assign(&other.c0);
        self.c1.sub_assign(&other.c1);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        let mut v0 = self.c0;
        v0.mul_assign(&other.c0);
        let mut v1 = self.c1;
        v1.mul_assign(&other.c1);

        let t = self.c0;
        self.c1.add_assign(&t);

        let mut t0 = other.c0;
        t0.add_assign(&other.c1);
        self.c1.mul_assign(&t0);
        self.c1.sub_assign(&v0);
        self.c1.sub_assign(&v1);
        self.c0 = v0;
        Mersenne31Complex::mul_by_non_residue(&mut v1);
        self.c0.add_assign(&v1);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn square(&mut self) -> &mut Self {
        let mut v0 = self.c0;
        v0.sub_assign(&self.c1);
        let mut v3 = self.c0;
        let mut t0 = self.c1;
        Mersenne31Complex::mul_by_non_residue(&mut t0);
        v3.sub_assign(&t0);
        let mut v2 = self.c0;
        v2.mul_assign(&self.c1);
        v0.mul_assign(&v3);
        v0.add_assign(&v2);

        self.c1 = v2;
        self.c1.double();
        self.c0 = v0;
        Mersenne31Complex::mul_by_non_residue(&mut v2);
        self.c0.add_assign(&v2);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn negate(&mut self) -> &mut Self {
        self.c0.negate();
        self.c1.negate();

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn double(&mut self) -> &mut Self {
        self.c0.double();
        self.c1.double();

        self
    }

    fn inverse(&self) -> Option<Self> {
        let mut v0 = self.c0;
        v0.square();
        let mut v1 = self.c1;
        v1.square();
        // v0 = v0 - beta * v1
        let mut v1_by_nonresidue = v1;
        Mersenne31Complex::mul_by_non_residue(&mut v1_by_nonresidue);
        v0.sub_assign(&v1_by_nonresidue);
        match v0.inverse() {
            Some(inversed) => {
                let mut c0 = self.c0;
                c0.mul_assign(&inversed);
                let mut c1 = self.c1;
                c1.mul_assign(&inversed);
                c1.negate();

                let new = Self { c0, c1 };
                Some(new)
            }
            None => None,
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_by_two(&'_ mut self) -> &'_ mut Self {
        self.c0.mul_by_two();
        self.c1.mul_by_two();
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn div_by_two(&'_ mut self) -> &'_ mut Self {
        self.c0.div_by_two();
        self.c1.div_by_two();
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn fused_mul_add_assign(&'_ mut self, a: &Self, b: &Self) -> &'_ mut Self {
        #[cfg(not(all(target_arch = "riscv32", feature = "modular_ext4_ops")))]
        fma_implementation(self, a, b);

        #[cfg(all(target_arch = "riscv32", feature = "modular_ext4_ops"))]
        fma_implementation_via_delegation(self, a, b);

        self
    }
}

impl core::fmt::Debug for Mersenne31Quartic {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "F4[{}, {}, {}, {}]",
            self.c0.c0.as_u64_reduced(),
            self.c0.c1.as_u64_reduced(),
            self.c1.c0.as_u64_reduced(),
            self.c1.c1.as_u64_reduced(),
        )
    }
}

impl core::fmt::Display for Mersenne31Quartic {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "F4[{}, {}, {}, {}]",
            self.c0.c0.as_u64_reduced(),
            self.c0.c1.as_u64_reduced(),
            self.c1.c0.as_u64_reduced(),
            self.c1.c1.as_u64_reduced(),
        )
    }
}

impl FieldExtension<Mersenne31Complex> for Mersenne31Quartic {
    const DEGREE: usize = 2;

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign_by_base(&mut self, elem: &Mersenne31Complex) -> &mut Self {
        self.c0.mul_assign(elem);
        self.c1.mul_assign(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_base_coeffs_array(coefs: &[Mersenne31Complex; 2]) -> Self {
        Self {
            c0: coefs[0],
            c1: coefs[1],
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn into_coeffs_in_base(self) -> [Mersenne31Complex; 2] {
        let Self { c0, c1 } = self;

        [c0, c1]
    }

    fn from_coeffs_in_base(coeffs: &[Mersenne31Complex]) -> Self {
        debug_assert_eq!(coeffs.len(), 2);
        let c0 = coeffs[0];
        let c1 = coeffs[1];

        Self { c0, c1 }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs_in_base_ref(_coeffs: &[&Mersenne31Complex]) -> Self {
        todo!();
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs_in_base_iter<I: Iterator<Item = Mersenne31Complex>>(_coefs_iter: I) -> Self {
        todo!();
    }

    fn coeffs_in_base(&self) -> &[Mersenne31Complex] {
        todo!();
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign_base(&mut self, elem: &Mersenne31Complex) -> &mut Self {
        self.c0.add_assign_base(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn sub_assign_base(&mut self, elem: &Mersenne31Complex) -> &mut Self {
        self.c0.sub_assign_base(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_base(elem: Mersenne31Complex) -> Self {
        Self {
            c0: elem,
            c1: Mersenne31Complex::ZERO,
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn get_coef_mut(&mut self, _idx: usize) -> &mut Mersenne31Complex {
        todo!();
    }
}

impl FieldExtension<Mersenne31Field> for Mersenne31Quartic {
    const DEGREE: usize = 4;

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn mul_assign_by_base(&mut self, elem: &Mersenne31Field) -> &mut Self {
        self.c0.mul_assign_by_base(elem);
        self.c1.mul_assign_by_base(elem);

        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline)]
    fn into_coeffs_in_base(self) -> [Mersenne31Field; 4] {
        let Mersenne31Quartic { c0, c1 } = self;
        let [c2, c3] = c1.into_coeffs_in_base();
        let [c0, c1] = c0.into_coeffs_in_base();

        [c0, c1, c2, c3]
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_base_coeffs_array(coefs: &[Mersenne31Field; 4]) -> Self {
        Self {
            c0: Mersenne31Complex {
                c0: coefs[0],
                c1: coefs[1],
            },
            c1: Mersenne31Complex {
                c0: coefs[2],
                c1: coefs[3],
            },
        }
    }

    fn from_coeffs_in_base(coefs: &[Mersenne31Field]) -> Self {
        Self {
            c0: Mersenne31Complex {
                c0: coefs[0],
                c1: coefs[1],
            },
            c1: Mersenne31Complex {
                c0: coefs[2],
                c1: coefs[3],
            },
        }
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs_in_base_ref(_coeffs: &[&Mersenne31Field]) -> Self {
        todo!();
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn from_coeffs_in_base_iter<I: Iterator<Item = Mersenne31Field>>(_coefs_iter: I) -> Self {
        todo!()
    }

    fn coeffs_in_base(&self) -> &[Mersenne31Field] {
        todo!();
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn add_assign_base(&mut self, elem: &Mersenne31Field) -> &mut Self {
        self.c0.add_assign_base(elem);
        self
    }

    #[cfg_attr(not(feature = "no_inline"), inline(always))]
    fn sub_assign_base(&mut self, elem: &Mersenne31Field) -> &mut Self {
        self.c0.sub_assign_base(elem);
        self
    }

    fn from_base(elem: Mersenne31Field) -> Self {
        let c0 = Mersenne31Complex::from_base(elem);
        Self {
            c0,
            c1: Mersenne31Complex::ZERO,
        }
    }

    fn get_coef_mut(&mut self, _idx: usize) -> &mut Mersenne31Field {
        todo!();
    }
}

#[cfg(not(all(target_arch = "riscv32", feature = "modular_ext4_ops")))]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
fn fma_implementation(dst: &mut Mersenne31Quartic, a: &Mersenne31Quartic, b: &Mersenne31Quartic) {
    dst.mul_assign(a);
    dst.add_assign(b);
}

#[cfg(all(target_arch = "riscv32", feature = "modular_ext4_ops"))]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
fn fma_implementation_via_delegation(
    dst: &mut Mersenne31Quartic,
    a: &Mersenne31Quartic,
    b: &Mersenne31Quartic,
) {
    // NOTE: no guaranteed reduction here, so we will need to be careful to fully reduce
    // for comparisons after such functions

    unsafe {
        core::arch::asm!(
            "csrrw x0, 0x7c8, x0",
            in("x10") (dst as *mut Mersenne31Quartic as *mut Mersenne31Field).addr(),
            in("x11") (a as *const Mersenne31Quartic as *const Mersenne31Field).addr(),
            in("x12") (b as *const Mersenne31Quartic as *const Mersenne31Field).addr(),
            options(nostack, preserves_flags)
        )
    }
}

// We need these for precompile to work with data in RAM and not ROM
#[cfg(all(target_arch = "riscv32", feature = "modular_ext4_ops"))]
pub static mut ZERO_STATIC: core::mem::MaybeUninit<Mersenne31Quartic> =
    core::mem::MaybeUninit::uninit();

#[cfg(all(target_arch = "riscv32", feature = "modular_ext4_ops"))]
pub static mut ONE_STATIC: core::mem::MaybeUninit<Mersenne31Quartic> =
    core::mem::MaybeUninit::uninit();

#[cfg(all(target_arch = "riscv32", feature = "modular_ext4_ops"))]
pub static mut MINUS_ONE_STATIC: core::mem::MaybeUninit<Mersenne31Quartic> =
    core::mem::MaybeUninit::uninit();

impl Mersenne31Quartic {
    #[cfg(not(all(target_arch = "riscv32", feature = "modular_ext4_ops")))]
    pub const USE_SPEC_MUL_BY_BASE_VIA_MUL_BY_SELF: bool = false;

    #[cfg(not(all(target_arch = "riscv32", feature = "modular_ext4_ops")))]
    pub const PREFER_FMA: bool = false;

    #[cfg(not(all(target_arch = "riscv32", feature = "modular_ext4_ops")))]
    pub const CAN_PROJECT_FROM_BASE: bool = const {
        core::mem::align_of::<Self>() == core::mem::align_of::<Mersenne31Field>()
            && core::mem::size_of::<Self>() == core::mem::size_of::<Mersenne31Field>() * 4
    };

    #[cfg(all(target_arch = "riscv32", feature = "modular_ext4_ops"))]
    pub const USE_SPEC_MUL_BY_BASE_VIA_MUL_BY_SELF: bool = true;

    #[cfg(all(target_arch = "riscv32", feature = "modular_ext4_ops"))]
    pub const PREFER_FMA: bool = true;

    #[cfg(all(target_arch = "riscv32", feature = "modular_ext4_ops"))]
    pub const CAN_PROJECT_FROM_BASE: bool = true;

    #[cfg(not(all(target_arch = "riscv32", feature = "modular_ext4_ops")))]
    pub fn pow_with_fma(&self, exp: u32) -> Self {
        // no difference here
        self.pow(exp)
    }

    #[cfg(all(target_arch = "riscv32", feature = "modular_ext4_ops"))]
    pub fn pow_with_fma(&self, mut exp: u32) -> Self {
        unsafe {
            let mut base = *self;
            let mut result = Self::ONE;
            while exp > 0 {
                if exp % 2 == 1 {
                    result.fused_mul_add_assign(&base, ZERO_STATIC.assume_init_ref());
                }

                exp >>= 1;
                // we can not provide two references here to the same value, so make a copy
                let current_base = core::hint::black_box(base);
                base.fused_mul_add_assign(&current_base, ZERO_STATIC.assume_init_ref());
            }

            result
        }
    }

    #[cfg(not(all(target_arch = "riscv32", feature = "modular_ext4_ops")))]
    pub fn add_assign_with_fma(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.add_assign(other)
    }

    #[cfg(all(target_arch = "riscv32", feature = "modular_ext4_ops"))]
    pub fn add_assign_with_fma(&'_ mut self, other: &Self) -> &'_ mut Self {
        unsafe { self.fused_mul_add_assign(ONE_STATIC.assume_init_ref(), other) }
    }

    #[cfg(not(all(target_arch = "riscv32", feature = "modular_ext4_ops")))]
    pub fn negate_self_and_add_other_with_fma(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.negate();
        self.add_assign(other)
    }

    #[cfg(all(target_arch = "riscv32", feature = "modular_ext4_ops"))]
    pub fn negate_self_and_add_other_with_fma(&'_ mut self, other: &Self) -> &'_ mut Self {
        unsafe { self.fused_mul_add_assign(MINUS_ONE_STATIC.assume_init_ref(), other) }
    }

    #[cfg(not(all(target_arch = "riscv32", feature = "modular_ext4_ops")))]
    pub fn mul_assign_with_fma(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.mul_assign(other)
    }

    #[cfg(all(target_arch = "riscv32", feature = "modular_ext4_ops"))]
    pub fn mul_assign_with_fma(&'_ mut self, other: &Self) -> &'_ mut Self {
        unsafe { self.fused_mul_add_assign(other, ZERO_STATIC.assume_init_ref()) }
    }

    #[cfg(not(all(target_arch = "riscv32", feature = "modular_ext4_ops")))]
    pub fn square_with_fma(&'_ mut self) -> &'_ mut Self {
        self.square()
    }

    #[cfg(all(target_arch = "riscv32", feature = "modular_ext4_ops"))]
    pub fn square_with_fma(&'_ mut self) -> &'_ mut Self {
        unsafe {
            let self_copy = core::hint::black_box(*self);
            self.fused_mul_add_assign(&self_copy, ZERO_STATIC.assume_init_ref())
        }
    }

    #[cfg(not(all(target_arch = "riscv32", feature = "modular_ext4_ops")))]
    pub fn init_ext4_fma_ops() {}

    #[cfg(all(target_arch = "riscv32", feature = "modular_ext4_ops"))]
    pub fn init_ext4_fma_ops() {
        // NOTE: even though in Rust constant is just an inline constant, and taking a reference
        // to such value will give a reference to the temporary copy and so it's fine for our
        // ROM + RAM model, we anyway can use statics to avoid making temporary copies

        unsafe {
            ZERO_STATIC.as_mut_ptr().write(Mersenne31Quartic::ZERO);
            ONE_STATIC.as_mut_ptr().write(Mersenne31Quartic::ONE);
            let mut minus_one = Self::ONE;
            minus_one.negate();
            MINUS_ONE_STATIC.as_mut_ptr().write(minus_one);
        }
    }
}
