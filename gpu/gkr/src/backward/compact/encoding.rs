//! u16 source-encoding masks and pack/unpack helpers for both round-0 and
//! continuation (rounds ≥ 1) source records.
//!
//! Round-0 source u16 layout (no folding cache; bit 15 doubles as
//! `is_virtual`):
//!
//!   bit 15      : is_virtual (1 = virtual base-field source, 0 = real consolidated poly)
//!   bits 14..11 : ptr_idx into `tables.bases` / `tables.log2_stride` (real path, 4 bits / 16 slots)
//!   bits 10..0  : poly_idx within the chosen slot (real path, 11 bits / max 2048) OR
//!                 low 3 bits = `gkr_base_source_kind` for the virtual path
//!                 (high bits zero by construction)
//!
//! Round 1+ source u16 layouts differ between base and ext records — see
//! the per-helper docs below.

use super::super::kernels::GKR_DIM_REDUCING_BASE_SLOTS;

// ---------------------------------------------------------------------------
// Round 0 — pack/unpack
// ---------------------------------------------------------------------------

pub(crate) const FLAT_SOURCE_VIRTUAL_FLAG: u16 = 0x8000;
// 4-bit ptr_idx (16 slots) shifted by 11; 11-bit poly_idx (max 2048).
const FLAT_SOURCE_PTR_IDX_SHIFT: u32 = 11;
#[cfg(test)]
const FLAT_SOURCE_PTR_IDX_MASK: u16 = 0xF;
pub(crate) const FLAT_SOURCE_POLY_IDX_MASK: u16 = 0x07FF;
const FLAT_SOURCE_VIRTUAL_KIND_MASK: u16 = 0x7;

/// Pack a real consolidated-poly source reference. `slot` indexes
/// `tables.bases`/`tables.log2_stride`; `poly_idx` is the per-class poly
/// index within that backing.
#[inline]
pub(crate) fn pack_flat_round0_source_real(slot: u8, poly_idx: u16) -> u16 {
    debug_assert!(
        (slot as usize) < GKR_DIM_REDUCING_BASE_SLOTS,
        "flat round0 slot {slot} >= GKR_DIM_REDUCING_BASE_SLOTS={GKR_DIM_REDUCING_BASE_SLOTS}",
    );
    debug_assert!(
        poly_idx <= FLAT_SOURCE_POLY_IDX_MASK,
        "flat round0 poly_idx {poly_idx} exceeds 11-bit budget {FLAT_SOURCE_POLY_IDX_MASK}",
    );
    ((slot as u16) << FLAT_SOURCE_PTR_IDX_SHIFT) | (poly_idx & FLAT_SOURCE_POLY_IDX_MASK)
}

/// Pack a virtual base-field source (range-check, inits/teardowns). `kind`
/// must be one of the `gkr_base_source_kind` discriminants in
/// [0, 7] (low 3 bits).
#[inline]
pub(crate) fn pack_flat_round0_source_virtual(kind: u8) -> u16 {
    debug_assert!(
        (kind as u16) <= FLAT_SOURCE_VIRTUAL_KIND_MASK,
        "flat round0 virtual kind {kind} exceeds 3-bit budget",
    );
    FLAT_SOURCE_VIRTUAL_FLAG | (kind as u16 & FLAT_SOURCE_VIRTUAL_KIND_MASK)
}

/// Decoded view of a packed flat round-0 source. Used by tests.
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnpackedFlatRound0Source {
    Real { slot: u8, poly_idx: u16 },
    Virtual { kind: u8 },
}

#[cfg(test)]
#[inline]
pub(crate) fn unpack_flat_round0_source(packed: u16) -> UnpackedFlatRound0Source {
    if (packed & FLAT_SOURCE_VIRTUAL_FLAG) != 0 {
        UnpackedFlatRound0Source::Virtual {
            kind: (packed & FLAT_SOURCE_VIRTUAL_KIND_MASK) as u8,
        }
    } else {
        UnpackedFlatRound0Source::Real {
            slot: ((packed >> FLAT_SOURCE_PTR_IDX_SHIFT) & FLAT_SOURCE_PTR_IDX_MASK) as u8,
            poly_idx: packed & FLAT_SOURCE_POLY_IDX_MASK,
        }
    }
}

// ---------------------------------------------------------------------------
// Rounds 1+ — bit-mask constants and pack/unpack helpers
// ---------------------------------------------------------------------------
//
// ext_sources (no virtual variant):
//   bit 15      : `first_access` — 1 ⇒ read from previous_layer slot,
//                 fold into cache. 0 ⇒ read from cache (and overwrite).
//   bits 14..11 : `ptr_idx` (4 bits / 16 slots) into `tables.bases`
//                 holding the previous-layer backing.
//   bits 10..0  : `poly_idx` (11 bits / max 2048) within that backing.
//
// base_sources (round 1/2 only — continuation has no base sources):
//   bit 15      : `first_access` (same semantics as ext).
//   bit 14      : `is_virtual` — 1 ⇒ low 3 bits encode `gkr_base_source_kind`.
//   bits 13..10 : `ptr_idx` (4 bits / 16 slots) — real path slot index, or
//                 virtual_cache_slot for the virtual path.
//   bits 9..0   : `poly_idx` (10 bits / max 1024) — real path. For the virtual
//                 path the low 3 bits are `gkr_base_source_kind`.

// Round 1+ pack/unpack helpers below are test-only — production round12_descs
// builds source records using `CONT_BASE_FIRST_ACCESS_FLAG`,
// `CONT_BASE_CACHE_VIRTUAL_FLAG`, `CONT_BASE_VIRTUAL_KIND_MASK` directly.

/// Round 1+ ext_source u16 layout (no base/virtual distinction):
///   bit 15      : first_access
///   bits 14..11 : ptr_idx (4 bits, 16 slots)
///   bits 10..0  : poly_idx (11 bits, max 2048)
#[cfg(test)]
const CONT_EXT_FIRST_ACCESS_FLAG: u16 = 0x8000;
#[cfg(test)]
const CONT_EXT_PTR_IDX_SHIFT: u32 = 11;
#[cfg(test)]
const CONT_EXT_PTR_IDX_MASK: u16 = 0xF;
#[cfg(test)]
const CONT_EXT_POLY_IDX_MASK: u16 = 0x07FF;

/// Round 1/2 base_source u16 layout:
///   bit 15      : first_access
///   bit 14      : is_virtual
///   bits 13..10 : ptr_idx (4 bits, 16 slots) — real path OR virtual_cache_slot (virtual)
///   bits 9..0   : poly_idx (10 bits, max 1024) — real path OR low 3 bits = source_kind (virtual)
pub(crate) const CONT_BASE_FIRST_ACCESS_FLAG: u16 = 0x8000;
#[cfg(test)]
const CONT_BASE_VIRTUAL_FLAG: u16 = 0x4000;
pub(crate) const CONT_BASE_CACHE_VIRTUAL_FLAG: u16 = 0x8000;
#[cfg(test)]
const CONT_BASE_PTR_IDX_SHIFT: u32 = 10;
#[cfg(test)]
const CONT_BASE_PTR_IDX_MASK: u16 = 0xF;
#[cfg(test)]
const CONT_BASE_POLY_IDX_MASK: u16 = 0x03FF;
pub(crate) const CONT_BASE_VIRTUAL_KIND_MASK: u16 = 0x7;

#[cfg(test)]
#[inline]
pub(crate) fn pack_cont_ext_source(first_access: bool, slot: u8, poly_idx: u16) -> u16 {
    debug_assert!((slot as u16) <= CONT_EXT_PTR_IDX_MASK);
    debug_assert!(poly_idx <= CONT_EXT_POLY_IDX_MASK);
    let first_bit = if first_access {
        CONT_EXT_FIRST_ACCESS_FLAG
    } else {
        0
    };
    first_bit | ((slot as u16) << CONT_EXT_PTR_IDX_SHIFT) | (poly_idx & CONT_EXT_POLY_IDX_MASK)
}

#[cfg(test)]
#[inline]
pub(crate) fn pack_cont_base_source_real(first_access: bool, slot: u8, poly_idx: u16) -> u16 {
    debug_assert!((slot as u16) <= CONT_BASE_PTR_IDX_MASK);
    debug_assert!(poly_idx <= CONT_BASE_POLY_IDX_MASK);
    let first_bit = if first_access {
        CONT_BASE_FIRST_ACCESS_FLAG
    } else {
        0
    };
    first_bit | ((slot as u16) << CONT_BASE_PTR_IDX_SHIFT) | (poly_idx & CONT_BASE_POLY_IDX_MASK)
}

/// Pack a virtual base source. `cache_slot` is the index in
/// `tables.bases` holding the virtual cache backing
/// (`intermediate_base_folding_consolidated.virtual_per_class[class]`).
/// `kind` is the `GpuBaseFieldSourceKind` discriminant (2..=5 for the four
/// virtual variants); the kernel synthesizes the value by calling
/// `gkr_virtual_base_value(kind, gid)`.
///
/// poly_idx within the virtual cache backing comes from
/// `virtual_index[poly]` and is encoded into the descriptor's
/// `virtual_cache_poly_idx` table (per-source array), so the source u16
/// itself doesn't need to carry it for the virtual path.
#[cfg(test)]
#[inline]
pub(crate) fn pack_cont_base_source_virtual(first_access: bool, cache_slot: u8, kind: u8) -> u16 {
    debug_assert!((cache_slot as u16) <= CONT_BASE_PTR_IDX_MASK);
    debug_assert!((kind as u16) <= CONT_BASE_VIRTUAL_KIND_MASK);
    let first_bit = if first_access {
        CONT_BASE_FIRST_ACCESS_FLAG
    } else {
        0
    };
    first_bit
        | CONT_BASE_VIRTUAL_FLAG
        | ((cache_slot as u16) << CONT_BASE_PTR_IDX_SHIFT)
        | ((kind as u16) & CONT_BASE_VIRTUAL_KIND_MASK)
}

/// Decoded view of a packed continuation ext-source u16.
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct UnpackedContExtSource {
    pub(crate) first_access: bool,
    pub(crate) slot: u8,
    pub(crate) poly_idx: u16,
}

#[cfg(test)]
#[inline]
pub(crate) fn unpack_cont_ext_source(packed: u16) -> UnpackedContExtSource {
    UnpackedContExtSource {
        first_access: (packed & CONT_EXT_FIRST_ACCESS_FLAG) != 0,
        slot: ((packed >> CONT_EXT_PTR_IDX_SHIFT) & CONT_EXT_PTR_IDX_MASK) as u8,
        poly_idx: packed & CONT_EXT_POLY_IDX_MASK,
    }
}

/// Decoded view of a packed continuation base-source u16.
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnpackedContBaseSource {
    Real {
        first_access: bool,
        slot: u8,
        poly_idx: u16,
    },
    Virtual {
        first_access: bool,
        cache_slot: u8,
        kind: u8,
    },
}

#[cfg(test)]
#[inline]
pub(crate) fn unpack_cont_base_source(packed: u16) -> UnpackedContBaseSource {
    let first_access = (packed & CONT_BASE_FIRST_ACCESS_FLAG) != 0;
    if (packed & CONT_BASE_VIRTUAL_FLAG) != 0 {
        UnpackedContBaseSource::Virtual {
            first_access,
            cache_slot: ((packed >> CONT_BASE_PTR_IDX_SHIFT) & CONT_BASE_PTR_IDX_MASK) as u8,
            kind: (packed & CONT_BASE_VIRTUAL_KIND_MASK) as u8,
        }
    } else {
        UnpackedContBaseSource::Real {
            first_access,
            slot: ((packed >> CONT_BASE_PTR_IDX_SHIFT) & CONT_BASE_PTR_IDX_MASK) as u8,
            poly_idx: packed & CONT_BASE_POLY_IDX_MASK,
        }
    }
}
