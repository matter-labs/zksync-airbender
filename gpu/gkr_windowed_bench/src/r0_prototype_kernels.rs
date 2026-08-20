use era_cudart::execution::CudaLaunchConfig;
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaError;

use crate::r0_geometry::{R0LaunchMetadata, R0LaunchPlan};
use crate::r0_kernels::launch_r0_geometry;
use crate::r0_prototype_abi::{PreparedPrototypeDescriptor, R0PrototypePayload};
use crate::r0_prototype_manifest::{
    R0CandidateSymbolV1, R0InnerFold, R0Lineage, R0OuterFold, R0ProgramEncoding,
    R0SectionedGeometry, R0SectionedManifestV1, R0SectionedShapeMergePolicy, R0SectionedSymbolV1,
    R0SourcePolicy,
};

mod generated {
    include!("generated/r0_prototype_registry.rs");
}

mod generated_sectioned {
    include!("generated/r0_sectioned_registry.rs");
}

pub fn r0_prototype_link_proof_summary() -> String {
    format!(
        "R0_PROTOTYPE_LINK_PROOF manifest={} symbols={} configurations={}",
        generated::R0_PROTOTYPE_MANIFEST_SHA256,
        generated::R0_PROTOTYPE_CANDIDATE_IDS.len(),
        generated::R0_PROTOTYPE_CONFIGURATION_IDS.len(),
    )
}

pub fn r0_sectioned_link_proof_summary() -> String {
    format!(
        "R0_SECTIONED_LINK_PROOF manifest={} symbols={}",
        generated_sectioned::R0_SECTIONED_MANIFEST_SHA256,
        generated_sectioned::R0_SECTIONED_CANDIDATE_IDS.len(),
    )
}

pub fn r0_sectioned_manifest_sha256() -> &'static str {
    generated_sectioned::R0_SECTIONED_MANIFEST_SHA256
}

pub fn r0_sectioned_shape_merge_policy() -> R0SectionedShapeMergePolicy {
    R0SectionedShapeMergePolicy::parse(generated_sectioned::R0_SECTIONED_SHAPE_MERGE_POLICY)
        .unwrap_or_else(|error| panic!("invalid generated sectioned shape merge policy: {error}"))
}

pub fn r0_sectioned_symbol_is_exact(candidate: &R0SectionedSymbolV1) -> bool {
    generated_sectioned::sectioned_symbol_is_exact(candidate)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum R0SectionedShapePolicy {
    Exact,
    Compatible,
    Universal,
}

pub fn select_r0_sectioned_candidate(
    manifest: &R0SectionedManifestV1,
    shape_bits: Option<u16>,
    geometry: R0SectionedGeometry,
    min_blocks: Option<u32>,
) -> CudaResult<&R0SectionedSymbolV1> {
    manifest
        .symbols
        .iter()
        .find(|candidate| {
            candidate.geometry == geometry
                && candidate.shape_bits == shape_bits
                && candidate.min_blocks == min_blocks
        })
        .ok_or(CudaError::ErrorInvalidValue)
}

pub fn r0_sectioned_launch_plan(
    geometry: R0SectionedGeometry,
    log_trace: u32,
) -> Result<R0LaunchPlan, crate::r0_geometry::R0GeometryError> {
    use crate::r0_geometry::R0Geometry;
    match geometry {
        R0SectionedGeometry::Wide9 => R0Geometry::Cta288Pair,
        R0SectionedGeometry::Split3 => R0Geometry::Cta96Partitioned,
        R0SectionedGeometry::Serial3Low | R0SectionedGeometry::Serial3High => {
            R0Geometry::Cta96X0Major
        }
    }
    .launch_plan(log_trace)
}

pub fn r0_sectioned_base_geometry(geometry: R0SectionedGeometry) -> crate::r0_geometry::R0Geometry {
    use crate::r0_geometry::R0Geometry;
    match geometry {
        R0SectionedGeometry::Wide9 => R0Geometry::Cta288Pair,
        R0SectionedGeometry::Split3 => R0Geometry::Cta96Partitioned,
        R0SectionedGeometry::Serial3Low | R0SectionedGeometry::Serial3High => {
            R0Geometry::Cta96X0Major
        }
    }
}

pub fn validate_sectioned_binding(
    candidate: &R0SectionedSymbolV1,
    descriptor_shape_bits: u16,
    requested_min_blocks: Option<u32>,
    plan: R0LaunchPlan,
) -> CudaResult<()> {
    let bound_is_valid = match candidate.geometry {
        R0SectionedGeometry::Wide9 => crate::r0_prototype_manifest::R0_SECTIONED_WIDE_MIN_BLOCKS_V3
            .contains(&candidate.min_blocks),
        R0SectionedGeometry::Split3 | R0SectionedGeometry::Serial3Low => {
            crate::r0_prototype_manifest::R0_SECTIONED_SWEEP_MIN_BLOCKS
                .contains(&candidate.min_blocks)
        }
        R0SectionedGeometry::Serial3High => false,
    };
    if !r0_sectioned_symbol_is_exact(candidate)
        || candidate.shape_bits.is_some_and(|shape| {
            !crate::r0_prototype_manifest::r0_sectioned_shape_dispatch_is_allowed(
                descriptor_shape_bits,
                shape,
            )
        })
        || candidate.min_blocks != requested_min_blocks
        || !bound_is_valid
        || plan.geometry != r0_sectioned_base_geometry(candidate.geometry)
        || plan.block[0] != candidate.geometry.threads()
    {
        return Err(CudaError::ErrorInvalidValue);
    }
    Ok(())
}

pub fn launch_r0_sectioned(
    candidate: &R0SectionedSymbolV1,
    descriptor: &PreparedPrototypeDescriptor,
    plan: R0LaunchPlan,
    stream: &CudaStream,
) -> CudaResult<R0LaunchMetadata> {
    let R0PrototypePayload::GroupedSlotOrdinary(desc) = descriptor.payload else {
        return Err(CudaError::ErrorInvalidValue);
    };
    let shape_bits =
        u16::try_from(desc.meta.sections[4]).map_err(|_| CudaError::ErrorInvalidValue)?;
    validate_sectioned_binding(candidate, shape_bits, candidate.min_blocks, plan)?;
    let config = CudaLaunchConfig::basic(
        (plan.grid[0], plan.grid[1], plan.grid[2]),
        (plan.block[0], plan.block[1], plan.block[2]),
        stream,
    );
    #[cfg(r0_prototype_bank_full)]
    generated_sectioned::launch_sectioned(candidate, desc, &config)?;
    #[cfg(not(r0_prototype_bank_full))]
    {
        let _ = (candidate, desc, config);
        return Err(CudaError::ErrorInvalidValue);
    }
    #[cfg(r0_prototype_bank_full)]
    Ok(R0LaunchMetadata {
        geometry: plan.geometry,
        symbol: candidate.symbol.clone(),
        grid: plan.grid,
        block: plan.block,
    })
}

pub fn launch_r0_prototype(
    candidate: &R0CandidateSymbolV1,
    descriptor: &PreparedPrototypeDescriptor,
    plan: R0LaunchPlan,
    dynamic_shared_bytes: u32,
    stream: &CudaStream,
) -> CudaResult<R0LaunchMetadata> {
    validate_descriptor_binding(candidate, descriptor, plan, dynamic_shared_bytes)?;
    if candidate.lineage == R0Lineage::Reference {
        let R0PrototypePayload::CurrentOrdinary(desc) = &descriptor.payload else {
            return Err(CudaError::ErrorInvalidValue);
        };
        if candidate.encoding != R0ProgramEncoding::CurrentFixedSlot
            || candidate.inner != R0InnerFold::Canonical
            || candidate.outer != R0OuterFold::Canonical
            || candidate.source_policy != R0SourcePolicy::Ordinary
            || candidate.symbol != reference_symbol(candidate.geometry)
        {
            return Err(CudaError::ErrorInvalidValue);
        }
        return launch_r0_geometry(candidate.geometry, *desc, plan, stream);
    }

    let mut config = CudaLaunchConfig::basic(
        (plan.grid[0], plan.grid[1], plan.grid[2]),
        (plan.block[0], plan.block[1], plan.block[2]),
        stream,
    );
    config.dynamic_smem_bytes = dynamic_shared_bytes as usize;
    #[cfg(r0_prototype_bank_full)]
    generated::launch_template(candidate, &descriptor.payload, &config)?;
    #[cfg(not(r0_prototype_bank_full))]
    {
        let _ = (candidate, descriptor, config);
        return Err(CudaError::ErrorInvalidValue);
    }
    #[cfg(r0_prototype_bank_full)]
    Ok(R0LaunchMetadata {
        geometry: candidate.geometry,
        symbol: candidate.symbol.clone(),
        grid: plan.grid,
        block: plan.block,
    })
}

pub fn configure_materialized_shared_memory(
    candidate: &R0CandidateSymbolV1,
    dynamic_shared_bytes: u32,
) -> CudaResult<()> {
    if candidate.lineage != R0Lineage::Template
        || candidate.source_policy != R0SourcePolicy::Materialized
    {
        return Err(CudaError::ErrorInvalidValue);
    }
    #[cfg(r0_prototype_bank_full)]
    return generated::configure_materialized(candidate, dynamic_shared_bytes);
    #[cfg(not(r0_prototype_bank_full))]
    {
        let _ = dynamic_shared_bytes;
        Err(CudaError::ErrorInvalidValue)
    }
}

fn validate_descriptor_binding(
    candidate: &R0CandidateSymbolV1,
    descriptor: &PreparedPrototypeDescriptor,
    plan: R0LaunchPlan,
    dynamic_shared_bytes: u32,
) -> CudaResult<()> {
    let source_matches = match candidate.source_policy {
        R0SourcePolicy::Ordinary => {
            descriptor.capacity.is_none()
                && descriptor.max_dynamic_shared_bytes() == 0
                && dynamic_shared_bytes == 0
        }
        R0SourcePolicy::Materialized => {
            descriptor.capacity.is_some()
                && descriptor.max_dynamic_shared_bytes() == dynamic_shared_bytes
        }
    };
    if candidate.encoding == descriptor.encoding
        && candidate.geometry == plan.geometry
        && source_matches
    {
        Ok(())
    } else {
        Err(CudaError::ErrorInvalidValue)
    }
}

fn reference_symbol(geometry: crate::r0_geometry::R0Geometry) -> &'static str {
    use crate::r0_geometry::R0Geometry;
    match geometry {
        R0Geometry::Cta288Pair => "ab_gkr_windowed_r0_cta288_pair_kernel",
        R0Geometry::Cta96Partitioned => "ab_gkr_windowed_r0_cta96_partitioned_kernel",
        R0Geometry::Cta96X0Major => "ab_gkr_windowed_r0_cta96_x0_major_kernel",
        R0Geometry::Cta96X1Major => "ab_gkr_windowed_r0_cta96_x1_major_kernel",
        R0Geometry::Cta96X2Major => "ab_gkr_windowed_r0_cta96_x2_major_kernel",
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::Path;

    use era_cudart::result::CudaResult;
    use era_cudart::stream::CudaStream;

    use crate::r0_geometry::{R0LaunchMetadata, R0LaunchPlan};
    use crate::r0_prototype_abi::PreparedPrototypeDescriptor;
    use crate::r0_prototype_manifest::{
        build_r0_prototype_manifest, R0CandidateSymbolV1, R0Lineage, R0SectionedOwnership,
    };

    use super::{
        configure_materialized_shared_memory, launch_r0_prototype, r0_prototype_link_proof_summary,
    };

    #[test]
    fn cpu_generated_launch_surface_has_the_exact_checked_signature() {
        let _: fn(
            &R0CandidateSymbolV1,
            &PreparedPrototypeDescriptor,
            R0LaunchPlan,
            u32,
            &CudaStream,
        ) -> CudaResult<R0LaunchMetadata> = launch_r0_prototype;
        let _: fn(&R0CandidateSymbolV1, u32) -> CudaResult<()> =
            configure_materialized_shared_memory;
        assert_eq!(super::generated::R0_PROTOTYPE_CANDIDATE_IDS.len(), 245);
        assert_eq!(super::generated::R0_PROTOTYPE_CONFIGURATION_IDS.len(), 425);
    }

    #[test]
    fn cpu_link_proof_summary_pins_the_generated_bank() {
        let summary = r0_prototype_link_proof_summary();
        assert!(summary.contains("symbols=245"));
        assert!(summary.contains("configurations=425"));
        assert!(summary
            .contains("manifest=204f07437e4ae23b90d155c6c229711a76fcee912b14eb783d2886ed53f578b9"));
    }

    #[test]
    fn cpu_sectioned_link_proof_summary_pins_the_generated_family() {
        let merge_policy = super::r0_sectioned_shape_merge_policy();
        assert_eq!(
            merge_policy,
            crate::r0_prototype_manifest::R0SectionedShapeMergePolicy::Merged,
        );
        let summary = super::r0_sectioned_link_proof_summary();
        assert!(summary.contains("symbols=26"), "{summary}");
        let manifest =
            crate::r0_prototype_manifest::build_r0_sectioned_manifest_v4_for_merge_policy(
                merge_policy,
            )
            .unwrap();
        assert!(manifest
            .symbols
            .iter()
            .all(super::r0_sectioned_symbol_is_exact));
        let mut wrong_ownership = manifest.symbols[0].clone();
        wrong_ownership.ownership = R0SectionedOwnership::FixedX0;
        assert!(!super::r0_sectioned_symbol_is_exact(&wrong_ownership));
    }

    #[test]
    fn cpu_sectioned_selection_prefers_exact_shape_and_binds_geometry() {
        let manifest = crate::r0_prototype_manifest::build_r0_sectioned_manifest_v4().unwrap();
        let exact = super::select_r0_sectioned_candidate(
            &manifest,
            Some(0x1b1),
            crate::r0_prototype_manifest::R0SectionedGeometry::Wide9,
            Some(3),
        )
        .unwrap();
        assert_eq!(exact.shape_bits, Some(0x1b1));
        assert_eq!(
            exact.symbol,
            "ab_gkr_windowed_r0_sectioned_shape_1b1_wide9_b3_kernel"
        );

        let universal = super::select_r0_sectioned_candidate(
            &manifest,
            None,
            crate::r0_prototype_manifest::R0SectionedGeometry::Wide9,
            Some(4),
        )
        .unwrap();
        assert_eq!(universal.shape_bits, None);
        assert_eq!(
            universal.symbol,
            "ab_gkr_windowed_r0_sectioned_universal_wide9_b4_kernel"
        );

        let plan = super::r0_sectioned_launch_plan(exact.geometry, 9).unwrap();
        assert_eq!(plan.grid, [2, 1, 1]);
        assert_eq!(plan.block, [288, 1, 1]);
        super::validate_sectioned_binding(exact, 0x1b1, Some(3), plan).unwrap();
        assert!(super::validate_sectioned_binding(exact, 0x1b1, Some(4), plan).is_err());
        assert!(super::validate_sectioned_binding(exact, 0x1b7, Some(3), plan).is_err());

        super::validate_sectioned_binding(universal, 0x155, Some(4), plan).unwrap();

        assert!(super::select_r0_sectioned_candidate(
            &manifest,
            Some(0x1b1),
            crate::r0_prototype_manifest::R0SectionedGeometry::Split3,
            Some(8),
        )
        .is_err());
        assert!(super::select_r0_sectioned_candidate(
            &manifest,
            Some(0x1b1),
            crate::r0_prototype_manifest::R0SectionedGeometry::Serial3High,
            None,
        )
        .is_err());
    }

    #[test]
    fn cpu_sectioned_v4_binding_accepts_every_safe_shape_superset() {
        let manifest = crate::r0_prototype_manifest::build_r0_sectioned_manifest_v4().unwrap();
        let candidate = super::select_r0_sectioned_candidate(
            &manifest,
            Some(0xbff),
            crate::r0_prototype_manifest::R0SectionedGeometry::Wide9,
            Some(3),
        )
        .unwrap();
        let plan = super::r0_sectioned_launch_plan(candidate.geometry, 9).unwrap();
        super::validate_sectioned_binding(candidate, 0x3fb, Some(3), plan).unwrap();
        super::validate_sectioned_binding(candidate, 0x9bf, Some(3), plan).unwrap();
        super::validate_sectioned_binding(candidate, 0xbff, Some(3), plan).unwrap();
        super::validate_sectioned_binding(candidate, 0x020, Some(3), plan).unwrap();
        assert!(super::validate_sectioned_binding(candidate, 0xc78, Some(3), plan).is_err());
    }

    #[test]
    fn cpu_generated_registry_covers_every_manifest_symbol_exactly() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let registry =
            fs::read_to_string(root.join("src/generated/r0_prototype_registry.rs")).unwrap();
        let cmake =
            fs::read_to_string(root.join("native/generated/windowed_r0_prototype_sources.cmake"))
                .unwrap();
        let manifest = build_r0_prototype_manifest().unwrap();

        for unit in &manifest.translation_units {
            let file = unit.source_path.rsplit('/').next().unwrap();
            assert_eq!(cmake.matches(file).count(), 1, "CMake owner for {file}");
        }
        for candidate in &manifest.symbols {
            let marker = format!(
                "// R0PB-FFI candidate={} symbol={} descriptor={} geometry={} source={}",
                candidate.candidate_id,
                candidate.symbol,
                candidate.descriptor_kind,
                candidate.geometry.as_str(),
                candidate.source_policy.as_str(),
            );
            assert_eq!(
                registry.matches(&marker).count(),
                1,
                "generated registry row for {}",
                candidate.candidate_id
            );
            if candidate.lineage == R0Lineage::Template {
                assert!(super::generated::template_candidate_is_exact(candidate));
                let mut mutated = candidate.clone();
                mutated.descriptor_kind.push_str("-wrong");
                assert!(!super::generated::template_candidate_is_exact(&mutated));
                let unit = fs::read_to_string(root.join(&candidate.translation_unit)).unwrap();
                assert_eq!(
                    unit.matches(&candidate.symbol).count(),
                    1,
                    "translation-unit owner for {}",
                    candidate.symbol
                );
                assert_eq!(
                    registry
                        .lines()
                        .filter(|line| {
                            line.starts_with("cuda_kernel_declaration!(")
                                && line.contains(&candidate.symbol)
                        })
                        .count(),
                    1,
                    "generated declaration for {}",
                    candidate.symbol
                );
            }
        }
    }
}
