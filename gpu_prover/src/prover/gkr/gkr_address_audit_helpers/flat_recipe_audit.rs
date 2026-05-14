use super::{metadata_qt_lt_term_lens, FLAT_LINEAR_FORM_SENTINEL};

/// Per-layer flat-path round-0 audit: total recipes (= `GpuRecipeHeader`
/// count), total prefactor terms (= `GpuPrefactorTerm` count, summed over
/// recipe groups), and the qt×lt cross-product blowup accounting.
///
/// Mirrors the gate-kind dispatch in [`backward_flat::build_flat_round0_plan`]
/// and the per-emitter recipe shapes:
/// - bare bc0/bc1/neg_bc0 recipes (output evaluations) → 1 recipe, 0 terms
/// - `emit_constraint_gate` → M recipes, each with 1 group of qt[i].ct
/// - `emit_cross_product_gate` → M·N recipes, each with 2 groups (qt[i].ct, lt[j].ct)
/// - `emit_materialize_gate` → N recipes, each with 1 group of lt[j].ct
/// - `emit_single_times_linear_form` → N recipes, each with 1 group of lt[j].ct
/// - `emit_linear_form_times_ext` → N recipes, each with 1 group of lt[j].ct
#[derive(Default, Debug, Clone, Copy)]
pub(crate) struct FlatRecipeAudit {
    pub(crate) total_recipes: u32,
    pub(crate) total_terms: u32,
    /// Recipes from blueprints with `Immediate` constraint metadata
    /// (immediate_factor = host-pre-evaluated E4 from external_challenges,
    /// prefactors empty). `immediate_factor` is per-recipe distinct in
    /// general; dedup-via-shared-slot doesn't trivially apply.
    pub(crate) recipes_immediate: u32,
    /// Recipes from blueprints with `Deferred` constraint metadata
    /// (immediate_factor = E::ONE, prefactors carry the structural
    /// `(coeff, source, power)` triples that the kernel evaluates on-device).
    /// All such recipes share `immediate_factor = ONE` ⇒ dedup-trivial.
    pub(crate) recipes_deferred: u32,
    /// Recipes emitted by gate-kind paths that don't consult constraint
    /// metadata at all (BaseCopy, ExtCopy, Product, MaskIdentity, LookupPair,
    /// LookupBasePair, etc.) — bare bc0/bc1/neg_bc0/gamma recipes. Same
    /// immediate (= E::ONE) and no prefactors. Dedup-trivial.
    pub(crate) recipes_bare: u32,
    /// Number of blueprints that route through `emit_cross_product_gate`.
    pub(crate) xprod_gates: u32,
    /// Σ M·N — recipes shipped today from cross-product expansion.
    pub(crate) xprod_expanded_recipes: u32,
    /// Σ (M+N) — source-index entries needed if the kernel ABI accepted a
    /// "product of two sums" term type (one recipe per gate, plus M+N source
    /// indices on the side arrays).
    pub(crate) xprod_source_indices_compact: u32,
    /// Σ M·N · (avg terms per recipe) — terms shipped today from the
    /// expansion. Used together with `xprod_source_indices_compact` to bound
    /// the byte-savings of a hypothetical pair-of-sums ABI.
    pub(crate) xprod_expanded_terms: u32,
    /// Σ (Σ qt.ct + Σ lt.ct) — terms across all cross-product gates if the
    /// kernel kept the prefactor groups merged (one (Σ qt.ct) group + one
    /// (Σ lt.ct) group per gate).
    pub(crate) xprod_compact_terms: u32,
    /// Largest single-gate M·N (worst per-gate blowup).
    pub(crate) xprod_max_m_times_n: u32,
    /// Largest single-gate (M, N).
    pub(crate) xprod_max_m: u32,
    pub(crate) xprod_max_n: u32,
}

impl FlatRecipeAudit {
    pub(super) fn merge_max(&mut self, other: &Self) {
        // For totals we keep per-layer (max layer wins), since the H2D is
        // also per-layer.
        if other.total_recipes > self.total_recipes {
            *self = *other;
        }
    }
}

pub(crate) fn project_layer_flat_round0_recipe_audit<E>(
    blueprints: &[crate::prover::gkr::backward::kernels::GpuGKRMainLayerKernelBlueprint<E>],
) -> FlatRecipeAudit {
    use crate::prover::gkr::backward::kernels::GpuGKRMainLayerConstraintMetadataSource as MS;
    use crate::prover::gkr::backward::kernels::GpuGKRMainLayerKernelKind as K;
    let mut a = FlatRecipeAudit::default();

    // Helper: account for one cross-product expansion (qt × lt). The path
    // tag (Immediate vs Deferred) determines whether we count the M·N
    // recipes as immediate-bucket (16 B `immediate_factor` per recipe set
    // to qt.challenge·lt.challenge) or deferred-bucket (immediate_factor =
    // ONE, prefactors carry the structural terms).
    let account_xprod =
        |a: &mut FlatRecipeAudit, qt_lens: &[usize], lt_lens: &[usize], is_immediate: bool| {
            let m = qt_lens.len();
            let n = lt_lens.len();
            if m == 0 || n == 0 {
                return;
            }
            let mn = (m * n) as u32;
            let qt_total: usize = qt_lens.iter().sum();
            let lt_total: usize = lt_lens.iter().sum();
            let xprod_terms_today = (n * qt_total + m * lt_total) as u32;
            let xprod_terms_compact = (qt_total + lt_total) as u32;

            a.xprod_gates += 1;
            a.xprod_expanded_recipes += mn;
            a.xprod_source_indices_compact += (m + n) as u32;
            a.xprod_expanded_terms += xprod_terms_today;
            a.xprod_compact_terms += xprod_terms_compact;
            a.xprod_max_m_times_n = a.xprod_max_m_times_n.max(mn);
            a.xprod_max_m = a.xprod_max_m.max(m as u32);
            a.xprod_max_n = a.xprod_max_n.max(n as u32);

            a.total_recipes += mn;
            a.total_terms += xprod_terms_today;
            if is_immediate {
                a.recipes_immediate += mn;
            } else {
                a.recipes_deferred += mn;
            }
        };

    // Helper: account for a list of recipes whose prefactors carry one group
    // of `lens[i]` terms each. `lens.len()` recipes, Σ lens terms.
    // `is_immediate` selects the path bucket.
    let account_single_group = |a: &mut FlatRecipeAudit, lens: &[usize], is_immediate: bool| {
        let n = lens.len() as u32;
        a.total_recipes += n;
        a.total_terms += lens.iter().sum::<usize>() as u32;
        if is_immediate {
            a.recipes_immediate += n;
        } else {
            a.recipes_deferred += n;
        }
    };

    // Helper: bare bc0/bc1/neg_bc0 recipes (immediate=ONE, no prefactors).
    let account_bare = |a: &mut FlatRecipeAudit, n: u32| {
        a.total_recipes += n;
        a.recipes_bare += n;
    };

    let is_immediate = |src: &Option<MS<E>>| matches!(src, Some(MS::Immediate(_)));

    for bp in blueprints {
        let imm = is_immediate(&bp.constraint_metadata_source);
        match bp.kind {
            K::BaseCopy | K::LinearBaseOutput => account_bare(&mut a, 1),
            K::ExtCopy => account_bare(&mut a, 1),
            K::Product => account_bare(&mut a, 2),
            K::MaskIdentity => account_bare(&mut a, 2),
            K::LookupPair => account_bare(&mut a, 5),
            K::LookupBasePair => account_bare(&mut a, 3),
            K::LookupBaseMinusMultiplicityByBase => account_bare(&mut a, 4),
            K::LookupExtMinusMultiplicityByExt => account_bare(&mut a, 4),
            K::LookupUnbalanced => account_bare(&mut a, 4),
            K::LookupUnbalancedExtension => account_bare(&mut a, 4),
            K::LookupWithCachedDensAndSetup => account_bare(&mut a, 5),
            K::LookupExtPair => account_bare(&mut a, 3),
            K::EnforceConstraintsMaxQuadratic => {
                let (qt, _) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, false);
                account_single_group(&mut a, &qt, imm);
            }
            K::MaxQuadraticBaseOutput => {
                account_bare(&mut a, 1);
                let (qt, _) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, false);
                account_single_group(&mut a, &qt, imm);
            }
            K::InitsAndTeardownsInitialPair => {
                account_bare(&mut a, 1);
                let (qt, _) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, false);
                account_single_group(&mut a, &qt, imm);
            }
            K::InitialGrandProductWithoutCaches => {
                account_bare(&mut a, 1);
                let (qt, lt) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, true);
                account_xprod(&mut a, &qt, &lt, imm);
            }
            K::MaterializeGrandProductTermExpression => {
                account_bare(&mut a, 1);
                let (_, lt) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, true);
                account_single_group(&mut a, &lt, imm);
            }
            K::LookupPairFromBaseInputs | K::LookupPairFromVectorInputs => {
                account_bare(&mut a, 2);
                let (qt, lt) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, true);
                account_xprod(&mut a, &qt, &lt, imm);
            }
            K::LookupWithDensAndSetupExpressions => {
                account_bare(&mut a, 2);
                let (qt, lt) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, true);
                account_single_group(&mut a, &lt, imm);
                account_single_group(&mut a, &qt, imm);
                account_xprod(&mut a, &qt, &lt, imm);
            }
            K::LookupFromVectorInputWithSetup => {
                account_bare(&mut a, 2);
                let (qt, lt) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, true);
                account_single_group(&mut a, &qt, imm);
                account_xprod(&mut a, &qt, &lt, imm);
            }
            K::LookupUnbalancedPairWithVectorInputs => {
                account_bare(&mut a, 2);
                let (_, lt) = metadata_qt_lt_term_lens(&bp.constraint_metadata_source, true);
                account_single_group(&mut a, &lt, imm);
                account_single_group(&mut a, &lt, imm);
            }
        }
    }

    a
}

/// Per-layer flat-path **continuation** audit — same shape as the round-0
/// audit but mirrors `backward_flat::build_flat_continuation_plan` and its
/// `emit_continuation_*` helpers. Continuation runs on rounds 3+ (after the
/// dimension-reducing folds), so the recipe shapes differ from round-0.
///
/// Same fields as `FlatRecipeAudit`. Cross-product accounting follows the
/// (qt, lt) loop in `emit_continuation_cross_product_gate` exactly: real
/// (qt, lt) pairs and (qt, lt_const) / (qt_const, lt) / (qt_const, lt_const)
/// fan-out are all counted as expanded recipes today.
pub(crate) fn project_layer_flat_continuation_recipe_audit<E>(
    blueprints: &[crate::prover::gkr::backward::kernels::GpuGKRMainLayerKernelBlueprint<E>],
) -> FlatRecipeAudit {
    use crate::prover::gkr::backward::kernels::GpuGKRMainLayerConstraintMetadataSource as MS;
    use crate::prover::gkr::backward::kernels::GpuGKRMainLayerKernelKind as K;
    let mut a = FlatRecipeAudit::default();

    // Bare-recipe accumulator (n recipes, 0 terms — no prefactors).
    let bare = |a: &mut FlatRecipeAudit, n: u32| {
        a.total_recipes += n;
        a.recipes_bare += n;
    };
    // Gamma-recipe accumulator (n recipes, n terms each carrying 1 ChallengeTerm
    // — `bc0_gamma`/`bc1_gamma`/`neg_bc0_gamma`). The kernel evaluates the
    // gamma against on-device `lookup_add`, so gamma recipes are deferred-bucket
    // (immediate_factor = ONE).
    let gamma = |a: &mut FlatRecipeAudit, n: u32| {
        a.total_recipes += n;
        a.total_terms += n;
        a.recipes_deferred += n;
    };

    // emit_continuation_constraint_gate: walks qt, non-sentinel lt, plus
    // sentinel-lt push_constants and a tail constant_terms push_constant.
    // `is_immediate` selects the bucket.
    let emit_constraint = |a: &mut FlatRecipeAudit, src: &Option<MS<E>>, is_immediate: bool| {
        let (qt_lens, lt_lens, qt_consts_total, lt_consts_total, n_qt_consts, n_lt_consts) =
            metadata_split_with_consts(src);
        let n = qt_lens.len() as u32 + lt_lens.len() as u32 + n_lt_consts as u32;
        a.total_recipes += n;
        a.total_terms += qt_lens.iter().sum::<usize>() as u32;
        a.total_terms += lt_lens.iter().sum::<usize>() as u32;
        a.total_terms += lt_consts_total as u32;
        if is_immediate {
            a.recipes_immediate += n;
        } else {
            a.recipes_deferred += n;
        }
        let _ = (qt_consts_total, n_qt_consts);
    };

    // emit_continuation_cross_product_gate: walks (qt_real × lt_real) +
    // (qt_real × lt_const) + (lt_real × qt_const) + (qt_const × lt_const).
    let emit_xprod = |a: &mut FlatRecipeAudit, src: &Option<MS<E>>, is_immediate: bool| {
        let (qt_lens, lt_lens, qt_consts_total, lt_consts_total, n_qt_consts, n_lt_consts) =
            metadata_split_with_consts(src);
        let m = qt_lens.len();
        let n = lt_lens.len();
        let qt_total: usize = qt_lens.iter().sum();
        let lt_total: usize = lt_lens.iter().sum();
        if m == 0 && n == 0 && n_qt_consts == 0 && n_lt_consts == 0 {
            return;
        }

        let xprod_mn = (m * n) as u32;
        let xprod_mn_terms = (n * qt_total + m * lt_total) as u32;
        let mn_lc = (m * n_lt_consts) as u32;
        let mn_lc_terms = (n_lt_consts * qt_total + m * lt_consts_total) as u32;
        let nm_qc = (n * n_qt_consts) as u32;
        let nm_qc_terms = (n_qt_consts * lt_total + n * qt_consts_total) as u32;
        let cc = (n_qt_consts * n_lt_consts) as u32;
        let cc_terms = (n_lt_consts * qt_consts_total + n_qt_consts * lt_consts_total) as u32;

        let total_recipes = xprod_mn + mn_lc + nm_qc + cc;
        let total_terms = xprod_mn_terms + mn_lc_terms + nm_qc_terms + cc_terms;
        a.total_recipes += total_recipes;
        a.total_terms += total_terms;
        if is_immediate {
            a.recipes_immediate += total_recipes;
        } else {
            a.recipes_deferred += total_recipes;
        }

        if total_recipes > 0 {
            a.xprod_gates += 1;
            a.xprod_expanded_recipes += total_recipes;
            a.xprod_expanded_terms += total_terms;
            a.xprod_max_m_times_n = a.xprod_max_m_times_n.max(xprod_mn);
            a.xprod_max_m = a.xprod_max_m.max(m as u32);
            a.xprod_max_n = a.xprod_max_n.max(n as u32);
            a.xprod_source_indices_compact += (m + n + n_qt_consts + n_lt_consts) as u32;
            a.xprod_compact_terms +=
                (qt_total + lt_total + qt_consts_total + lt_consts_total) as u32;
        }
    };

    let emit_materialize = |a: &mut FlatRecipeAudit, src: &Option<MS<E>>, is_immediate: bool| {
        let (_, lt_lens, _, lt_consts_total, _, n_lt_consts) = metadata_split_with_consts(src);
        let n = lt_lens.len() as u32 + n_lt_consts as u32;
        a.total_recipes += n;
        a.total_terms += lt_lens.iter().sum::<usize>() as u32;
        a.total_terms += lt_consts_total as u32;
        if is_immediate {
            a.recipes_immediate += n;
        } else {
            a.recipes_deferred += n;
        }
    };

    let emit_single_times_linear =
        |a: &mut FlatRecipeAudit, src: &Option<MS<E>>, use_qt_side: bool, is_immediate: bool| {
            let (qt_lens, lt_lens, qt_consts_total, lt_consts_total, n_qt_consts, n_lt_consts) =
                metadata_split_with_consts(src);
            let (lens, consts_total, n_consts) = if use_qt_side {
                (&qt_lens, qt_consts_total, n_qt_consts)
            } else {
                (&lt_lens, lt_consts_total, n_lt_consts)
            };
            let n = lens.len() as u32 + n_consts as u32;
            a.total_recipes += n;
            a.total_terms += lens.iter().sum::<usize>() as u32;
            a.total_terms += consts_total as u32;
            if is_immediate {
                a.recipes_immediate += n;
            } else {
                a.recipes_deferred += n;
            }
        };

    let emit_linear_form = |a: &mut FlatRecipeAudit, src: &Option<MS<E>>, is_immediate: bool| {
        emit_single_times_linear(a, src, false, is_immediate);
    };

    let is_immediate = |src: &Option<MS<E>>| matches!(src, Some(MS::Immediate(_)));

    for bp in blueprints {
        let src = &bp.constraint_metadata_source;
        let imm = is_immediate(src);
        match bp.kind {
            K::BaseCopy | K::ExtCopy => bare(&mut a, 1),
            K::LinearBaseOutput => emit_constraint(&mut a, src, imm),
            K::Product => bare(&mut a, 1),
            K::MaskIdentity => bare(&mut a, 3),
            K::LookupPair => bare(&mut a, 3),
            K::LookupBasePair => {
                bare(&mut a, 3);
                gamma(&mut a, 4);
            }
            K::LookupBaseMinusMultiplicityByBase => {
                bare(&mut a, 3);
                gamma(&mut a, 5);
            }
            K::LookupExtMinusMultiplicityByExt => {
                bare(&mut a, 3);
                gamma(&mut a, 5);
            }
            K::LookupUnbalanced => {
                bare(&mut a, 3);
                gamma(&mut a, 2);
            }
            K::LookupUnbalancedExtension => {
                bare(&mut a, 3);
                gamma(&mut a, 2);
            }
            K::LookupWithCachedDensAndSetup => {
                bare(&mut a, 3);
                gamma(&mut a, 5);
            }
            K::EnforceConstraintsMaxQuadratic => emit_constraint(&mut a, src, imm),
            K::MaxQuadraticBaseOutput => emit_constraint(&mut a, src, imm),
            K::InitsAndTeardownsInitialPair => emit_constraint(&mut a, src, imm),
            K::InitialGrandProductWithoutCaches => emit_xprod(&mut a, src, imm),
            K::MaterializeGrandProductTermExpression => emit_materialize(&mut a, src, imm),
            K::LookupPairFromBaseInputs | K::LookupPairFromVectorInputs => {
                emit_linear_form(&mut a, src, imm);
                emit_linear_form(&mut a, src, imm);
                emit_xprod(&mut a, src, imm);
            }
            K::LookupExtPair => {
                bare(&mut a, 3);
                gamma(&mut a, 4);
            }
            K::LookupWithDensAndSetupExpressions => {
                emit_single_times_linear(&mut a, src, false, imm);
                emit_single_times_linear(&mut a, src, true, imm);
                emit_xprod(&mut a, src, imm);
            }
            K::LookupFromVectorInputWithSetup => {
                emit_single_times_linear(&mut a, src, false, imm);
                emit_linear_form(&mut a, src, imm);
                emit_xprod(&mut a, src, imm);
            }
            K::LookupUnbalancedPairWithVectorInputs => {
                emit_linear_form(&mut a, src, imm);
                emit_linear_form(&mut a, src, imm);
                bare(&mut a, 1);
            }
        }
    }

    a
}

/// Helper: split constraint metadata into (qt_real_lens, lt_real_lens,
/// qt_consts_total, lt_consts_total, n_qt_consts, n_lt_consts).
/// `_real_lens` are per-term `challenge_terms.len()` for non-sentinel rows;
/// `_consts_total` is summed `challenge_terms.len()` across sentinel rows;
/// `n_*_consts` is the count of sentinel rows.
/// `Immediate` metadata reports 0-len for everything (no challenge_terms).
fn metadata_split_with_consts<E>(
    src: &Option<crate::prover::gkr::backward::kernels::GpuGKRMainLayerConstraintMetadataSource<E>>,
) -> (Vec<usize>, Vec<usize>, usize, usize, usize, usize) {
    use crate::prover::gkr::backward::kernels::GpuGKRMainLayerConstraintMetadataSource as MS;
    match src {
        None => (Vec::new(), Vec::new(), 0, 0, 0, 0),
        Some(MS::Immediate(meta)) => {
            let qt_real: Vec<usize> = meta
                .quadratic_terms
                .iter()
                .filter(|t| t.lhs != FLAT_LINEAR_FORM_SENTINEL)
                .map(|_| 0)
                .collect();
            let lt_real: Vec<usize> = meta
                .linear_terms
                .iter()
                .filter(|t| t.input != FLAT_LINEAR_FORM_SENTINEL)
                .map(|_| 0)
                .collect();
            let n_qt_consts = meta
                .quadratic_terms
                .iter()
                .filter(|t| t.lhs == FLAT_LINEAR_FORM_SENTINEL)
                .count();
            let n_lt_consts = meta
                .linear_terms
                .iter()
                .filter(|t| t.input == FLAT_LINEAR_FORM_SENTINEL)
                .count();
            (qt_real, lt_real, 0, 0, n_qt_consts, n_lt_consts)
        }
        Some(MS::Deferred(tmpl)) => {
            let qt_real: Vec<usize> = tmpl
                .quadratic_terms
                .iter()
                .filter(|t| t.lhs != FLAT_LINEAR_FORM_SENTINEL)
                .map(|t| t.challenge_terms.len())
                .collect();
            let lt_real: Vec<usize> = tmpl
                .linear_terms
                .iter()
                .filter(|t| t.input != FLAT_LINEAR_FORM_SENTINEL)
                .map(|t| t.challenge_terms.len())
                .collect();
            let qt_consts_total: usize = tmpl
                .quadratic_terms
                .iter()
                .filter(|t| t.lhs == FLAT_LINEAR_FORM_SENTINEL)
                .map(|t| t.challenge_terms.len())
                .sum();
            let lt_consts_total: usize = tmpl
                .linear_terms
                .iter()
                .filter(|t| t.input == FLAT_LINEAR_FORM_SENTINEL)
                .map(|t| t.challenge_terms.len())
                .sum();
            let n_qt_consts = tmpl
                .quadratic_terms
                .iter()
                .filter(|t| t.lhs == FLAT_LINEAR_FORM_SENTINEL)
                .count();
            let n_lt_consts = tmpl
                .linear_terms
                .iter()
                .filter(|t| t.input == FLAT_LINEAR_FORM_SENTINEL)
                .count();
            (
                qt_real,
                lt_real,
                qt_consts_total,
                lt_consts_total,
                n_qt_consts,
                n_lt_consts,
            )
        }
    }
}
