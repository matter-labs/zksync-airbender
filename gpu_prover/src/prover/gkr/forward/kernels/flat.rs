use std::ptr::null;

use era_cudart::execution::KernelFunction;
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use super::{
    gkr_forward_launch_config, GpuGKRForwardCacheAddressSpaceKind, MEMORY_TUPLE_LINEAR_TERMS,
};
use crate::primitives::context::ProverContext;
use crate::primitives::field::{BF, E4};
use crate::upstream::Field;

// ---------------------------------------------------------------------------
// Flat forward kernel descriptors
// ---------------------------------------------------------------------------
//
// Mirrors `flat_forward_static_desc<E>` in native/prover/gkr/forward/flat.cuh.
// The forward scheduler populates these descriptors directly and chunks them
// when any per-category array would exceed the grid-constant budget.

pub(in crate::prover::gkr) const FLAT_FWD_MAX_SOURCES: usize = 256;
pub(in crate::prover::gkr) const FLAT_FWD_MAX_PER_CATEGORY: usize = 16;

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdProductEntry<E> {
    pub(in crate::prover::gkr) src_a: u16,
    pub(in crate::prover::gkr) src_b: u16,
    pub(in crate::prover::gkr) dst: *mut E,
}

impl<E> Copy for GpuFlatFwdProductEntry<E> {}

impl<E> Clone for GpuFlatFwdProductEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdMaskEntry<E> {
    pub(in crate::prover::gkr) src_mask: u16,
    pub(in crate::prover::gkr) src_input: u16,
    pub(in crate::prover::gkr) dst: *mut E,
}

impl<E> Copy for GpuFlatFwdMaskEntry<E> {}

impl<E> Clone for GpuFlatFwdMaskEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdLookup4Entry<E> {
    pub(in crate::prover::gkr) src_a: u16,
    pub(in crate::prover::gkr) src_b: u16,
    pub(in crate::prover::gkr) src_c: u16,
    pub(in crate::prover::gkr) src_d: u16,
    pub(in crate::prover::gkr) num: *mut E,
    pub(in crate::prover::gkr) den: *mut E,
}

impl<E> Copy for GpuFlatFwdLookup4Entry<E> {}

impl<E> Clone for GpuFlatFwdLookup4Entry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdBfPairEntry<E> {
    pub(in crate::prover::gkr) src_b: u16,
    pub(in crate::prover::gkr) src_d: u16,
    pub(in crate::prover::gkr) num: *mut E,
    pub(in crate::prover::gkr) den: *mut E,
}

impl<E> Copy for GpuFlatFwdBfPairEntry<E> {}

impl<E> Clone for GpuFlatFwdBfPairEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdE4PairEntry<E> {
    pub(in crate::prover::gkr) src_b: u16,
    pub(in crate::prover::gkr) src_d: u16,
    pub(in crate::prover::gkr) num: *mut E,
    pub(in crate::prover::gkr) den: *mut E,
}

impl<E> Copy for GpuFlatFwdE4PairEntry<E> {}

impl<E> Clone for GpuFlatFwdE4PairEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdCachedDensEntry<E> {
    pub(in crate::prover::gkr) src_a: u16,
    pub(in crate::prover::gkr) src_b: u16,
    pub(in crate::prover::gkr) src_c: u16,
    pub(in crate::prover::gkr) src_d: u16,
    pub(in crate::prover::gkr) num: *mut E,
    pub(in crate::prover::gkr) den: *mut E,
}

impl<E> Copy for GpuFlatFwdCachedDensEntry<E> {}

impl<E> Clone for GpuFlatFwdCachedDensEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdBfMinusMultEntry<E> {
    pub(in crate::prover::gkr) src_b: u16,
    pub(in crate::prover::gkr) src_c: u16,
    pub(in crate::prover::gkr) src_d: u16,
    pub(in crate::prover::gkr) _pad: u16,
    pub(in crate::prover::gkr) num: *mut E,
    pub(in crate::prover::gkr) den: *mut E,
}

impl<E> Copy for GpuFlatFwdBfMinusMultEntry<E> {}

impl<E> Clone for GpuFlatFwdBfMinusMultEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdE4MinusMultEntry<E> {
    pub(in crate::prover::gkr) src_b: u16,
    pub(in crate::prover::gkr) src_c: u16,
    pub(in crate::prover::gkr) src_d: u16,
    pub(in crate::prover::gkr) _pad: u16,
    pub(in crate::prover::gkr) num: *mut E,
    pub(in crate::prover::gkr) den: *mut E,
}

impl<E> Copy for GpuFlatFwdE4MinusMultEntry<E> {}

impl<E> Clone for GpuFlatFwdE4MinusMultEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdBfUnbalancedEntry<E> {
    pub(in crate::prover::gkr) src_a: u16,
    pub(in crate::prover::gkr) src_b: u16,
    pub(in crate::prover::gkr) src_d: u16,
    pub(in crate::prover::gkr) _pad: u16,
    pub(in crate::prover::gkr) num: *mut E,
    pub(in crate::prover::gkr) den: *mut E,
}

impl<E> Copy for GpuFlatFwdBfUnbalancedEntry<E> {}

impl<E> Clone for GpuFlatFwdBfUnbalancedEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdE4UnbalancedEntry<E> {
    pub(in crate::prover::gkr) src_a: u16,
    pub(in crate::prover::gkr) src_b: u16,
    pub(in crate::prover::gkr) src_d: u16,
    pub(in crate::prover::gkr) _pad: u16,
    pub(in crate::prover::gkr) num: *mut E,
    pub(in crate::prover::gkr) den: *mut E,
}

impl<E> Copy for GpuFlatFwdE4UnbalancedEntry<E> {}

impl<E> Clone for GpuFlatFwdE4UnbalancedEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdMappedBfPairEntry<E> {
    pub(in crate::prover::gkr) mapping_b: *const u32,
    pub(in crate::prover::gkr) mapping_d: *const u32,
    pub(in crate::prover::gkr) num: *mut E,
    pub(in crate::prover::gkr) den: *mut E,
}

impl<E> Copy for GpuFlatFwdMappedBfPairEntry<E> {}

impl<E> Clone for GpuFlatFwdMappedBfPairEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdMappedE4PairEntry<E> {
    pub(in crate::prover::gkr) mapping_b: *const u32,
    pub(in crate::prover::gkr) mapping_d: *const u32,
    pub(in crate::prover::gkr) generic_lookup: *const E,
    pub(in crate::prover::gkr) num: *mut E,
    pub(in crate::prover::gkr) den: *mut E,
}

impl<E> Copy for GpuFlatFwdMappedE4PairEntry<E> {}

impl<E> Clone for GpuFlatFwdMappedE4PairEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdMappedCachedDensEntry<E> {
    pub(in crate::prover::gkr) mapping_b: *const u32,
    pub(in crate::prover::gkr) generic_lookup: *const E,
    pub(in crate::prover::gkr) decoder_mask: *const BF,
    pub(in crate::prover::gkr) decoder_fill_value: *const E,
    pub(in crate::prover::gkr) src_a: u16,
    pub(in crate::prover::gkr) src_c: u16,
    pub(in crate::prover::gkr) generic_lookup_len: u32,
    pub(in crate::prover::gkr) _pad: u32,
    pub(in crate::prover::gkr) num: *mut E,
    pub(in crate::prover::gkr) den: *mut E,
}

impl<E> Copy for GpuFlatFwdMappedCachedDensEntry<E> {}

impl<E> Clone for GpuFlatFwdMappedCachedDensEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdMappedE4MinusMultEntry<E> {
    pub(in crate::prover::gkr) mapping_b: *const u32,
    pub(in crate::prover::gkr) generic_lookup: *const E,
    pub(in crate::prover::gkr) src_c: u16,
    pub(in crate::prover::gkr) _pad: u16,
    pub(in crate::prover::gkr) generic_lookup_len: u32,
    pub(in crate::prover::gkr) num: *mut E,
    pub(in crate::prover::gkr) den: *mut E,
}

impl<E> Copy for GpuFlatFwdMappedE4MinusMultEntry<E> {}

impl<E> Clone for GpuFlatFwdMappedE4MinusMultEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(in crate::prover::gkr) struct GpuFlatFwdMappedE4UnbalancedEntry<E> {
    pub(in crate::prover::gkr) src_a: u16,
    pub(in crate::prover::gkr) src_b: u16,
    pub(in crate::prover::gkr) _pad: u32,
    pub(in crate::prover::gkr) mapping_d: *const u32,
    pub(in crate::prover::gkr) generic_lookup: *const E,
    pub(in crate::prover::gkr) num: *mut E,
    pub(in crate::prover::gkr) den: *mut E,
}

impl<E> Copy for GpuFlatFwdMappedE4UnbalancedEntry<E> {}

impl<E> Clone for GpuFlatFwdMappedE4UnbalancedEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug)]
pub(in crate::prover::gkr) struct GpuFlatFwdMemoryExpr<E> {
    pub(in crate::prover::gkr) address_space_kind: GpuGKRForwardCacheAddressSpaceKind,
    pub(in crate::prover::gkr) address_space_ptr: *const BF,
    pub(in crate::prover::gkr) address_space_constant: BF,
    pub(in crate::prover::gkr) constant_term: E,
    pub(in crate::prover::gkr) linear_inputs: [*const BF; MEMORY_TUPLE_LINEAR_TERMS],
    pub(in crate::prover::gkr) linear_challenges: [E; MEMORY_TUPLE_LINEAR_TERMS],
}

impl<E: Field> Default for GpuFlatFwdMemoryExpr<E> {
    fn default() -> Self {
        Self {
            address_space_kind: GpuGKRForwardCacheAddressSpaceKind::Empty,
            address_space_ptr: null(),
            address_space_constant: BF::ZERO,
            constant_term: E::ZERO,
            linear_inputs: [null(); MEMORY_TUPLE_LINEAR_TERMS],
            linear_challenges: [E::ZERO; MEMORY_TUPLE_LINEAR_TERMS],
        }
    }
}

impl<E: Copy> Copy for GpuFlatFwdMemoryExpr<E> {}

impl<E: Copy> Clone for GpuFlatFwdMemoryExpr<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug)]
pub(in crate::prover::gkr) struct GpuFlatFwdMemoryProductEntry<E> {
    pub(in crate::prover::gkr) lhs: GpuFlatFwdMemoryExpr<E>,
    pub(in crate::prover::gkr) rhs: GpuFlatFwdMemoryExpr<E>,
    pub(in crate::prover::gkr) dst: *mut E,
}

impl<E: Field> Default for GpuFlatFwdMemoryProductEntry<E> {
    fn default() -> Self {
        Self {
            lhs: GpuFlatFwdMemoryExpr::default(),
            rhs: GpuFlatFwdMemoryExpr::default(),
            dst: null::<E>().cast_mut(),
        }
    }
}

impl<E: Copy> Copy for GpuFlatFwdMemoryProductEntry<E> {}

impl<E: Copy> Clone for GpuFlatFwdMemoryProductEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug)]
pub(in crate::prover::gkr) struct GpuFlatFwdMemoryMaterializeEntry<E> {
    pub(in crate::prover::gkr) expr: GpuFlatFwdMemoryExpr<E>,
    pub(in crate::prover::gkr) dst: *mut E,
}

impl<E: Field> Default for GpuFlatFwdMemoryMaterializeEntry<E> {
    fn default() -> Self {
        Self {
            expr: GpuFlatFwdMemoryExpr::default(),
            dst: null::<E>().cast_mut(),
        }
    }
}

impl<E: Copy> Copy for GpuFlatFwdMemoryMaterializeEntry<E> {}

impl<E: Copy> Clone for GpuFlatFwdMemoryMaterializeEntry<E> {
    fn clone(&self) -> Self {
        *self
    }
}

/// Static description for the flat forward kernel.
///
/// Mirrors `flat_forward_static_desc<E>` in native/prover/gkr/forward/flat.cuh.
/// Passed as `__grid_constant__`. Sources are encoded as raw pointers: real
/// device pointers for memory-backed sources, low-bit-tagged null pointers
/// for virtual base sources (range checks / inits+teardowns).
#[repr(C)]
pub(crate) struct GpuFlatForwardStaticDesc<E> {
    pub(in crate::prover::gkr) sources: [*const u8; FLAT_FWD_MAX_SOURCES],
    pub(in crate::prover::gkr) num_sources: u32,

    pub(in crate::prover::gkr) products: [GpuFlatFwdProductEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_products: u32,

    pub(in crate::prover::gkr) masks: [GpuFlatFwdMaskEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_masks: u32,

    pub(in crate::prover::gkr) lookup4s: [GpuFlatFwdLookup4Entry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_lookup4s: u32,

    pub(in crate::prover::gkr) bf_pairs: [GpuFlatFwdBfPairEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_bf_pairs: u32,

    pub(in crate::prover::gkr) e4_pairs: [GpuFlatFwdE4PairEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_e4_pairs: u32,

    pub(in crate::prover::gkr) cached_denses:
        [GpuFlatFwdCachedDensEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_cached_denses: u32,

    pub(in crate::prover::gkr) bf_minus_mults:
        [GpuFlatFwdBfMinusMultEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_bf_minus_mults: u32,

    pub(in crate::prover::gkr) e4_minus_mults:
        [GpuFlatFwdE4MinusMultEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_e4_minus_mults: u32,

    pub(in crate::prover::gkr) bf_unbalanceds:
        [GpuFlatFwdBfUnbalancedEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_bf_unbalanceds: u32,

    pub(in crate::prover::gkr) e4_unbalanceds:
        [GpuFlatFwdE4UnbalancedEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_e4_unbalanceds: u32,

    pub(in crate::prover::gkr) mapped_bf_pairs:
        [GpuFlatFwdMappedBfPairEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_mapped_bf_pairs: u32,

    pub(in crate::prover::gkr) mapped_e4_pairs:
        [GpuFlatFwdMappedE4PairEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_mapped_e4_pairs: u32,

    pub(in crate::prover::gkr) mapped_cached_denses:
        [GpuFlatFwdMappedCachedDensEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_mapped_cached_denses: u32,

    pub(in crate::prover::gkr) mapped_e4_minus_mults:
        [GpuFlatFwdMappedE4MinusMultEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_mapped_e4_minus_mults: u32,

    pub(in crate::prover::gkr) mapped_e4_unbalanceds:
        [GpuFlatFwdMappedE4UnbalancedEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_mapped_e4_unbalanceds: u32,

    pub(in crate::prover::gkr) memory_products:
        [GpuFlatFwdMemoryProductEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_memory_products: u32,

    pub(in crate::prover::gkr) memory_materializes:
        [GpuFlatFwdMemoryMaterializeEntry<E>; FLAT_FWD_MAX_PER_CATEGORY],
    pub(in crate::prover::gkr) num_memory_materializes: u32,
}

// The descriptor contains only POD data (pointers, indices, counts). Raw
// pointers aren't auto-Send/Sync; safety is the caller's responsibility: the
// forward scheduler ensures source pointers outlive the kernel launch.
unsafe impl<E> Send for GpuFlatForwardStaticDesc<E> {}
unsafe impl<E> Sync for GpuFlatForwardStaticDesc<E> {}

impl<E: Copy> Copy for GpuFlatForwardStaticDesc<E> {}

impl<E: Copy> Clone for GpuFlatForwardStaticDesc<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E: Field> Default for GpuFlatForwardStaticDesc<E> {
    fn default() -> Self {
        Self {
            sources: [null::<u8>(); FLAT_FWD_MAX_SOURCES],
            num_sources: 0,
            products: std::array::from_fn(|_| GpuFlatFwdProductEntry {
                src_a: 0,
                src_b: 0,
                dst: null::<E>().cast_mut(),
            }),
            num_products: 0,
            masks: std::array::from_fn(|_| GpuFlatFwdMaskEntry {
                src_mask: 0,
                src_input: 0,
                dst: null::<E>().cast_mut(),
            }),
            num_masks: 0,
            lookup4s: std::array::from_fn(|_| GpuFlatFwdLookup4Entry {
                src_a: 0,
                src_b: 0,
                src_c: 0,
                src_d: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_lookup4s: 0,
            bf_pairs: std::array::from_fn(|_| GpuFlatFwdBfPairEntry {
                src_b: 0,
                src_d: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_bf_pairs: 0,
            e4_pairs: std::array::from_fn(|_| GpuFlatFwdE4PairEntry {
                src_b: 0,
                src_d: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_e4_pairs: 0,
            cached_denses: std::array::from_fn(|_| GpuFlatFwdCachedDensEntry {
                src_a: 0,
                src_b: 0,
                src_c: 0,
                src_d: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_cached_denses: 0,
            bf_minus_mults: std::array::from_fn(|_| GpuFlatFwdBfMinusMultEntry {
                src_b: 0,
                src_c: 0,
                src_d: 0,
                _pad: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_bf_minus_mults: 0,
            e4_minus_mults: std::array::from_fn(|_| GpuFlatFwdE4MinusMultEntry {
                src_b: 0,
                src_c: 0,
                src_d: 0,
                _pad: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_e4_minus_mults: 0,
            bf_unbalanceds: std::array::from_fn(|_| GpuFlatFwdBfUnbalancedEntry {
                src_a: 0,
                src_b: 0,
                src_d: 0,
                _pad: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_bf_unbalanceds: 0,
            e4_unbalanceds: std::array::from_fn(|_| GpuFlatFwdE4UnbalancedEntry {
                src_a: 0,
                src_b: 0,
                src_d: 0,
                _pad: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_e4_unbalanceds: 0,
            mapped_bf_pairs: std::array::from_fn(|_| GpuFlatFwdMappedBfPairEntry {
                mapping_b: null(),
                mapping_d: null(),
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_mapped_bf_pairs: 0,
            mapped_e4_pairs: std::array::from_fn(|_| GpuFlatFwdMappedE4PairEntry {
                mapping_b: null(),
                mapping_d: null(),
                generic_lookup: null(),
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_mapped_e4_pairs: 0,
            mapped_cached_denses: std::array::from_fn(|_| GpuFlatFwdMappedCachedDensEntry {
                mapping_b: null(),
                generic_lookup: null(),
                decoder_mask: null(),
                decoder_fill_value: null(),
                src_a: 0,
                src_c: 0,
                generic_lookup_len: 0,
                _pad: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_mapped_cached_denses: 0,
            mapped_e4_minus_mults: std::array::from_fn(|_| GpuFlatFwdMappedE4MinusMultEntry {
                mapping_b: null(),
                generic_lookup: null(),
                src_c: 0,
                _pad: 0,
                generic_lookup_len: 0,
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_mapped_e4_minus_mults: 0,
            mapped_e4_unbalanceds: std::array::from_fn(|_| GpuFlatFwdMappedE4UnbalancedEntry {
                src_a: 0,
                src_b: 0,
                _pad: 0,
                mapping_d: null(),
                generic_lookup: null(),
                num: null::<E>().cast_mut(),
                den: null::<E>().cast_mut(),
            }),
            num_mapped_e4_unbalanceds: 0,
            memory_products: std::array::from_fn(|_| GpuFlatFwdMemoryProductEntry::default()),
            num_memory_products: 0,
            memory_materializes: std::array::from_fn(|_| {
                GpuFlatFwdMemoryMaterializeEntry::default()
            }),
            num_memory_materializes: 0,
        }
    }
}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRFlatForwardLayer<T>,
    desc: GpuFlatForwardStaticDesc<T>,
    count: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_flat_forward_layer_e4_kernel(
        desc: GpuFlatForwardStaticDesc<E4>,
        count: u32,
    )
);

pub(in crate::prover::gkr) fn launch_flat_forward_layer<E: crate::prover::gkr::GpuKernels>(
    desc: &GpuFlatForwardStaticDesc<E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(trace_len <= u32::MAX as usize);
    let count = trace_len as u32;
    let config = gkr_forward_launch_config(count, context);
    let args = GpuGKRFlatForwardLayerArguments::new(*desc, count);
    GpuGKRFlatForwardLayerFunction(E::FLAT_FORWARD_LAYER).launch(&config, &args)
}

/// True iff the flat descriptor has any gate entry. Used by the scheduler to
/// skip the flat kernel launch when no gates were migrated.
pub(in crate::prover::gkr) fn flat_desc_has_work<E>(desc: &GpuFlatForwardStaticDesc<E>) -> bool {
    desc.num_products
        | desc.num_masks
        | desc.num_lookup4s
        | desc.num_bf_pairs
        | desc.num_e4_pairs
        | desc.num_cached_denses
        | desc.num_bf_minus_mults
        | desc.num_e4_minus_mults
        | desc.num_bf_unbalanceds
        | desc.num_e4_unbalanceds
        | desc.num_mapped_bf_pairs
        | desc.num_mapped_e4_pairs
        | desc.num_mapped_cached_denses
        | desc.num_mapped_e4_minus_mults
        | desc.num_mapped_e4_unbalanceds
        | desc.num_memory_products
        | desc.num_memory_materializes
        != 0
}
