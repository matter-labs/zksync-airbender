#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::{Path, PathBuf};

    fn native() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("native")
    }

    fn crate_file(name: &str) -> String {
        fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(name))
            .unwrap_or_else(|error| panic!("missing prototype build file {name}: {error}"))
    }

    fn required(name: &str) -> String {
        fs::read_to_string(native().join(name))
            .unwrap_or_else(|error| panic!("missing native prototype header {name}: {error}"))
    }

    #[test]
    fn cpu_native_prototype_policy_surface_is_complete_and_static() {
        let cursor = required("windowed_r0_prototype_cursor.cuh");
        for tag in [
            "r0pb_current_fixed_slot_cursor",
            "r0pb_compact_r0_port_cursor",
            "r0pb_split_fixed_slot_cursor",
            "r0pb_split_fixed_direct_cursor",
            "r0pb_homogeneous_slot_cursor",
            "r0pb_homogeneous_direct_cursor",
            "r0pb_grouped_slot_cursor",
            "r0pb_grouped_direct_cursor",
        ] {
            assert!(cursor.contains(tag), "missing cursor {tag}");
        }

        let source = required("windowed_r0_prototype_source.cuh");
        for resolver in [
            "r0pb_ordinary_slot_resolver",
            "r0pb_ordinary_direct_resolver",
            "r0pb_materialized_resolver",
            "__syncthreads",
        ] {
            assert!(
                source.contains(resolver),
                "missing source primitive {resolver}"
            );
        }
        for row_tile_contract in [
            "begin_tile(const Desc &desc, const u32 tile_index, const u32 row_tile)",
            "const u32 global_row = row_tile * R0PB_TILE_ROWS + element / R0PB_TILE_CORNERS",
            "global_row < (1u << desc.ordinary.common.log_rows)",
            "(global_row << 3) | (element & 7u)",
        ] {
            assert!(
                source.contains(row_tile_contract),
                "materialized staging does not bind row tiles: {row_tile_contract}"
            );
        }

        let geometry = required("windowed_r0_prototype_geometry.cuh");
        for policy in [
            "r0pb_cta288_pair_geometry",
            "r0pb_cta96_partitioned_geometry",
            "r0pb_cta96_x0_major_geometry",
            "r0pb_cta96_x1_major_geometry",
            "r0pb_cta96_x2_major_geometry",
        ] {
            assert!(geometry.contains(policy), "missing geometry {policy}");
        }

        let kernel = required("windowed_r0_prototype_kernel.cuh");
        for token in [
            "AB_R0PB_DEFINE_ORDINARY_KERNEL",
            "AB_R0PB_DEFINE_MATERIALIZED_KERNEL",
            "r0pb_execute_program",
            "r0pb_publish",
        ] {
            assert!(kernel.contains(token), "missing kernel primitive {token}");
        }
        for forbidden in [
            "__launch_bounds__",
            "maxrregcount",
            "min_blocks",
            "program_pointer",
            "stage_program",
        ] {
            assert!(
                !cursor.contains(forbidden)
                    && !source.contains(forbidden)
                    && !geometry.contains(forbidden)
                    && !kernel.contains(forbidden),
                "prototype native source contains forbidden token {forbidden}"
            );
        }

        let canary = required("windowed_r0_prototype_canary.cu");
        assert_eq!(
            canary
                .lines()
                .filter(|line| line.starts_with("AB_R0PB_CANARY_KERNEL("))
                .count(),
            8
        );
        assert_eq!(
            canary
                .lines()
                .filter(|line| line.starts_with("AB_R0PB_DEFINE_MATERIALIZED_KERNEL("))
                .count(),
            8
        );
    }

    #[test]
    fn cpu_dedicated_control_converts_only_uncached_procedural_values() {
        let control = required("windowed_r0_prototype_dedicated_control.cuh");
        let accumulator = required("windowed_r0_prototype_accumulator.cuh");

        assert!(!control.contains("procedural_lookup"));
        assert!(!control.contains("procedural_cache"));
        assert!(!control.contains("bool procedural"));
        assert!(control.contains("r0pb_control_procedural_bf_value"));
        assert!(control.contains("R0PB_CONTROL_LINEAR_BF_PROCEDURAL"));
        assert!(control.contains("R0PB_CONTROL_PRODUCT_BF_BF_PROCEDURAL_B"));
        assert_eq!(control.matches("bf::from_u32_unchecked").count(), 1);
        assert!(control.contains("from_reduced_raw_repr"));
        assert!(control.contains("r0_u96_accumulator outer[3][4]{}"));
        assert!(control.contains("r0pb_control_reduce_and_rebase_bf_wide"));
        let mixed_scale = control
            .find("delta_bf = r0pb_control_apply_immediate")
            .expect("mixed BF immediate is not applied in BF");
        let mixed_multiply = control[mixed_scale..]
            .find("e4::mul(delta_e4, delta_bf)")
            .expect("mixed BF-by-E4 multiply is absent");
        assert!(mixed_multiply > 0);
        assert!(control.contains("values[cell] = e4::fma(core, sum.values[cell], values[cell])"));
        assert!(accumulator.contains("r0_u96_high_word_contribution"));
        assert!(!accumulator.contains("bf::from_u32_unchecked"));
    }

    #[test]
    fn cpu_dedicated_e4_pair_body_is_not_duplicated() {
        let control = required("windowed_r0_prototype_dedicated_control.cuh");

        assert!(control.contains("#pragma unroll 1\n  for (u32 member = 0; member < 2; ++member)"));
        assert_eq!(
            control.matches("r0pb_control_e4_group_member").count(),
            2,
            "the broad E4 member evaluator must have one definition and one loop call site"
        );
    }

    #[test]
    fn cpu_dedicated_selector_infinity_is_explicitly_warp_uniform() {
        let executor = required("windowed_r0_executor.cuh");
        let control = required("windowed_r0_prototype_dedicated_control.cuh");

        assert!(executor.contains("bool inf0;\n  bool inf1;"));
        assert!(executor.contains(
            "r0_selector_pair(const u32 a, const u32 b, const bool a_inf, const bool b_inf)"
        ));
        assert!(executor.contains("bool x0_infinity() const { return inf0; }"));
        assert!(executor.contains("bool x1_infinity() const { return inf1; }"));
        assert_eq!(control.matches("__all_sync(0xffffffffu").count(), 4);
        let sectioned_selector = control
            .split_once("r0pb_sectioned_selector")
            .expect("sectioned selector")
            .1
            .split_once("r0pb_evaluate_sectioned_selector")
            .expect("sectioned evaluator follows sectioned selector")
            .0;
        let legacy = control
            .split_once("r0pb_execute_dedicated_grouped_u64_u96_partitioned")
            .expect("legacy executor")
            .1;
        assert_eq!(
            sectioned_selector.matches("__all_sync(0xffffffffu").count(),
            2
        );
        assert_eq!(legacy.matches("__all_sync(0xffffffffu").count(), 2);
    }

    #[test]
    fn cpu_sectioned_shape_bits_specialize_every_declared_hot_loop() {
        let control = required("windowed_r0_prototype_dedicated_control.cuh");

        for feature in [
            "R0PB_SHAPE_BF_PROCEDURAL",
            "R0PB_SHAPE_BF_BANKED_IMMEDIATE",
            "R0PB_SHAPE_BF_INNER_REDUCTION",
            "R0PB_SHAPE_BF_LINEAR_TAIL",
            "R0PB_SHAPE_BF_SINGLE_PRODUCT_PREFIX",
        ] {
            assert!(
                control.matches(feature).count() >= 2,
                "{feature} is declared but does not specialize an active loop"
            );
        }

        let immediate = control
            .split_once("r0pb_control_apply_immediate")
            .expect("sectioned BF immediate evaluator")
            .1
            .split_once("r0pb_control_e4_group_member")
            .expect("broad E4 evaluator follows the sectioned BF immediate evaluator")
            .0;
        assert!(
            !immediate.contains("r0pb_control_immediate"),
            "shape-specialized BF immediates must not re-enter the broad +/-1 decoder"
        );
        assert!(
            immediate.contains("bf::from_reduced_raw_repr(desc.immediates[id - 2])"),
            "banked BF immediates must load their already-Montgomery coefficient directly"
        );

        let pair = control
            .split_once("r0pb_sectioned_execute_pair_members")
            .expect("sectioned fixed-pair evaluator")
            .1
            .split_once("r0pb_sectioned_execute_loaded_pair")
            .expect("fixed-pair shape dispatcher follows member evaluator")
            .0;
        assert!(
            !pair.contains("first.term_class"),
            "fixed-pair class selection must be compile-time"
        );
        assert!(
            control.contains("template <bool MayNegate>\nDEVICE_FORCEINLINE r0pb_control_triplet<e4> r0pb_sectioned_mixed_product"),
            "mixed E4 member negation must be shape-specialized"
        );
        assert!(
            control.contains("template <bool MayNegate>\nDEVICE_FORCEINLINE r0pb_control_triplet<e4> r0pb_sectioned_full_product"),
            "full E4 member negation must be shape-specialized"
        );
        assert!(
            control.contains("template <bool Mixed, bool MayNegate>\nDEVICE_FORCEINLINE void r0pb_sectioned_execute_pair_members"),
            "the fixed-pair evaluator must carry the shape's negative-factor fact"
        );
        assert!(
            pair.contains("r0pb_sectioned_mixed_product<MayNegate>")
                && pair.contains("r0pb_sectioned_full_product<MayNegate>"),
            "fixed-pair members must consume the compile-time negative-factor fact"
        );
        assert!(
            control.contains("if (product_prefix < 2)"),
            "a one-product BF prefix must be evaluated before its optional linear tail"
        );
        assert!(
            control
                .matches("r0pb_sectioned_execute_loaded_pair<Shape>")
                .count()
                >= 2,
            "both the ordinary and serial-high executors must dispatch loaded pairs by shape"
        );
    }

    #[test]
    fn cpu_sectioned_canary_names_the_dedicated_executor() {
        let canary = required("windowed_r0_prototype_canary.cu");
        let control = required("windowed_r0_prototype_dedicated_control.cuh");

        for geometry in ["WIDE9", "SPLIT3", "SERIAL3_LOW", "SERIAL3_HIGH"] {
            assert!(
                canary.contains(&format!("AB_R0PB_DEFINE_SECTIONED_{geometry}_KERNEL(")),
                "missing sectioned {geometry} canary",
            );
        }
        assert!(canary.contains(
            "AB_R0PB_DEFINE_SECTIONED_WIDE9_BOUNDED_KERNEL(ab_gkr_r0pb_canary_sectioned_wide9_b4, R0PB_SHAPE_UNIVERSAL, 4)"
        ));
        assert!(control.contains("r0pb_execute_sectioned"));
        assert!(control.contains("R0PB_CONTROL_LINEAR_E4_WIDE"));
    }

    #[test]
    fn cpu_native_prototype_build_modes_leave_feature_off_builds_unchanged() {
        let build = crate_file("build.rs");
        assert!(build.contains("CARGO_FEATURE_R0_PROTOTYPE_BANK"));
        assert!(build.contains("prototype native mode requires the r0-prototype-bank feature"));

        let cmake = required("CMakeLists.txt");
        let base_sources = cmake
            .split_once("if (NOT DEFINED GPU_GKR_WINDOWED_R0_PROTOTYPE_NATIVE)")
            .unwrap()
            .0;
        assert!(!base_sources.contains("windowed_r0_prototype_abi_probe.cu"));
        assert!(cmake.contains("if (GPU_GKR_WINDOWED_R0_PROTOTYPE_FEATURE)"));
        assert!(cmake.contains(
            "target_sources(gpu_gkr_windowed_bench_native PRIVATE windowed_r0_prototype_abi_probe.cu)"
        ));
    }
}
