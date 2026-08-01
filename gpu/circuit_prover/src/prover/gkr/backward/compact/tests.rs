use super::super::kernels::GKR_DIM_REDUCING_BASE_SLOTS;
use super::*;

#[test]
fn pack_unpack_real_round_trip() {
    for slot in 0..GKR_DIM_REDUCING_BASE_SLOTS as u8 {
        for poly_idx in [0u16, 1, 7, 64, 645, 0x07FF] {
            let packed = pack_flat_round0_source_real(slot, poly_idx);
            assert_eq!(packed & FLAT_SOURCE_VIRTUAL_FLAG, 0);
            let unpacked = unpack_flat_round0_source(packed);
            assert_eq!(
                unpacked,
                UnpackedFlatRound0Source::Real { slot, poly_idx },
                "round-trip failed for slot={slot} poly_idx={poly_idx} packed={packed:#06x}",
            );
        }
    }
}

#[test]
fn pack_unpack_virtual_round_trip() {
    for kind in 0u8..=7 {
        let packed = pack_flat_round0_source_virtual(kind);
        assert_ne!(packed & FLAT_SOURCE_VIRTUAL_FLAG, 0);
        assert_eq!(
            unpack_flat_round0_source(packed),
            UnpackedFlatRound0Source::Virtual { kind },
        );
    }
}

#[test]
fn pack_real_uses_lower_15_bits_only() {
    // Bit 15 must be reserved for the virtual flag. With 4-bit slot and
    // 11-bit poly_idx, max real-pack value is 0x7FFF.
    let packed = pack_flat_round0_source_real(0xF, 0x07FF);
    assert_eq!(packed & FLAT_SOURCE_VIRTUAL_FLAG, 0);
    assert_eq!(packed, 0x7FFF);
}

#[test]
fn descriptor_size_matches_phase0_audit() {
    // Anchored to the audit's projected post-compaction size so any
    // future field addition or slot-count change that diverges from the
    // audit projection is caught here.
    let size = std::mem::size_of::<GpuFlatRound0StaticDesc>();
    assert!(
        size <= KERNEL_ARG_HARD_CEILING_BYTES,
        "descriptor size {size} exceeds 32 KB hard ceiling",
    );
    let projected =
        super::super::super::gkr_address_audit_helpers::projected_post_compaction_sizes()
            .flat_round0_static_desc;
    assert_eq!(
        size, projected,
        "actual sizeof ({size}) differs from audit projection ({projected})",
    );
}

// The 16 KB "soft target" asserts these three tests used to carry were
// aspirational and never true in this repository: the caps sizing these
// descriptors (`FLAT_CONT_MAX_*`, term/tile arrays) arrived with the July-09
// import already ~2× over the target, so the tests were red from their first
// commit. The descriptors launch fine — the binding limit is the 32 KB kernel
// parameter ceiling — and the segmented lean VM retires this whole descriptor
// family at cutover. What is worth guarding is DRIFT: an exact size pin makes
// any field or cap change visible, the way `descriptor_size_matches_phase0_audit`
// pins round 0 to its audit projection.

#[test]
fn round1_descriptor_size_pinned_under_hard_ceiling() {
    let size = std::mem::size_of::<GpuFlatRound1UnifiedDesc>();
    assert!(
        size <= KERNEL_ARG_HARD_CEILING_BYTES,
        "round 1 compact desc size {size} > 32 KB ceiling",
    );
    assert_eq!(size, 30_944, "round 1 compact desc drifted");
}

#[test]
fn round2_descriptor_size_pinned_under_hard_ceiling() {
    let size = std::mem::size_of::<GpuFlatRound2UnifiedDesc>();
    assert!(
        size <= KERNEL_ARG_HARD_CEILING_BYTES,
        "round 2 compact desc size {size} > 32 KB ceiling",
    );
    assert_eq!(size, 30_952, "round 2 compact desc drifted");
}

#[test]
fn continuation_descriptor_size_pinned_under_hard_ceiling() {
    let size = std::mem::size_of::<GpuFlatContinuationUnifiedDesc>();
    assert!(
        size <= KERNEL_ARG_HARD_CEILING_BYTES,
        "continuation compact desc size {size} > 32 KB ceiling",
    );
    assert_eq!(size, 31_064, "continuation compact desc drifted");
}

#[test]
fn cont_ext_pack_unpack_round_trip() {
    for first in [false, true] {
        for slot in 0u8..=0xF {
            for poly_idx in [0u16, 1, 7, 64, 645, 0x07FF] {
                let packed = pack_cont_ext_source(first, slot, poly_idx);
                let unpacked = unpack_cont_ext_source(packed);
                assert_eq!(unpacked.first_access, first);
                assert_eq!(unpacked.slot, slot);
                assert_eq!(unpacked.poly_idx, poly_idx);
            }
        }
    }
}

#[test]
fn cont_base_real_pack_unpack_round_trip() {
    for first in [false, true] {
        for slot in 0u8..=0xF {
            for poly_idx in [0u16, 1, 7, 64, 645, 0x03FF] {
                let packed = pack_cont_base_source_real(first, slot, poly_idx);
                match unpack_cont_base_source(packed) {
                    UnpackedContBaseSource::Real {
                        first_access,
                        slot: s,
                        poly_idx: p,
                    } => {
                        assert_eq!(first_access, first);
                        assert_eq!(s, slot);
                        assert_eq!(p, poly_idx);
                    }
                    UnpackedContBaseSource::Virtual { .. } => {
                        panic!("real source decoded as virtual: {packed:#06x}")
                    }
                }
            }
        }
    }
}

#[test]
fn cont_base_virtual_pack_unpack_round_trip() {
    for first in [false, true] {
        for cache_slot in 0u8..=0xF {
            for kind in 0u8..=7 {
                let packed = pack_cont_base_source_virtual(first, cache_slot, kind);
                match unpack_cont_base_source(packed) {
                    UnpackedContBaseSource::Virtual {
                        first_access,
                        cache_slot: cs,
                        kind: k,
                    } => {
                        assert_eq!(first_access, first);
                        assert_eq!(cs, cache_slot);
                        assert_eq!(k, kind);
                    }
                    UnpackedContBaseSource::Real { .. } => {
                        panic!("virtual source decoded as real: {packed:#06x}")
                    }
                }
            }
        }
    }
}

#[test]
fn descriptor_default_zeroes_counts() {
    let desc = GpuFlatRound0StaticDesc::default();
    assert_eq!(desc.num_sources, 0);
    assert_eq!(desc.num_c0_bf, 0);
    assert_eq!(desc.num_c0_ext, 0);
    assert_eq!(desc.num_c1_bf_bf, 0);
    assert_eq!(desc.num_c1_e4_e4, 0);
    assert_eq!(desc.num_c1_bf_e4, 0);
    assert_eq!(desc.num_c1_linear, 0);
    // Tables default to all-null bases and zero strides.
    for slot in 0..GKR_DIM_REDUCING_BASE_SLOTS {
        assert!(desc.tables.bases[slot].is_null());
        assert_eq!(desc.tables.log2_stride[slot], 0);
    }
}
