use cs::gkr_compiler::dag_ir::{DagLayer, Expr, FieldKind, SourceKind, join};

use crate::fwd::isa::{MAX_ARITY, Sign};

use super::{
    CacheStoreFrom, EvalOp, EvalPlan, MaterializeFrom, Operand, RootKey, SinkInfo, TempId, TempRef,
    ValueFingerprint, ValueRef, field_lanes, unit_sign_expr,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PackConfig {
    pub max_add_operands: usize,
    pub max_mul_operands: usize,
    pub max_fma_pairs: usize,
}

impl Default for PackConfig {
    fn default() -> Self {
        Self {
            max_add_operands: MAX_ARITY,
            max_mul_operands: MAX_ARITY,
            max_fma_pairs: MAX_ARITY,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PackError {
    ZeroArityLimit,
    ArityLimitExceedsIsa { requested: usize, maximum: usize },
    MissingAccumulator,
    ExpectedSource(ValueRef),
    DramTrafficMismatch { plan: usize, packed: usize },
    ArithmeticCountMismatch { plan: usize, packed: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PackedEvalOp {
    AccInit(Operand),
    AccAdd {
        field: FieldKind,
        promote: bool,
        sign: Sign,
        operands: Vec<Operand>,
    },
    AccMul {
        field: FieldKind,
        promote: bool,
        sign: Sign,
        operands: Vec<Operand>,
    },
    AccFma {
        field_lhs: FieldKind,
        field_rhs: FieldKind,
        promote: bool,
        sign: Sign,
        pairs: Vec<(Operand, Operand)>,
    },
    SaveAcc(TempRef),
    CacheStore {
        value: ValueRef,
        from: CacheStoreFrom,
    },
    CacheDrop(ValueRef),
    Commit {
        root_id: cs::gkr_compiler::dag_ir::RootId,
        root: RootKey,
        sink: SinkInfo,
        from: MaterializeFrom,
    },
    ReturnAcc {
        root: RootKey,
    },
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PackedStats {
    pub unpacked_instructions: usize,
    pub packed_instructions: usize,
    pub arithmetic_instructions: usize,
    pub scalar_arithmetic_ops: usize,
    /// Scalar operations removed by algebraic cancellation while packing.
    pub optimized_away_arithmetic_ops: usize,
    /// Concrete wire lanes before operand binding: headers + operand/dst lanes.
    pub encoded_lanes: usize,
    pub dram_read_lanes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackedEvalPlan {
    pub ops: Vec<PackedEvalOp>,
    pub stats: PackedStats,
}

/// Regroup commutative arithmetic within maximal additive or multiplicative
/// runs, then pack equal shapes into the concrete VM's multi-arity Add/Mul/FMA
/// instructions. Saves, accumulator-backed cache stores, commits, and
/// accumulator initialization are hard barriers. Source-backed cache stores are
/// moved to the nearest pre-use run boundary when the resulting extended
/// lifetime remains within the symbolic lane budget.
/// `CacheDrop` is metadata-only and moves to the end of its surrounding
/// same-family arithmetic run; it neither reads the dropped value nor emits an
/// instruction, so it must not fragment arithmetic packing.
/// Before that scheduling, a local distributive rewrite turns
/// `(a +/- b +/- ...) * factor + seed` into an additive FMA run when repeating
/// `factor` cannot introduce DRAM traffic. This is deliberately post-plan: it
/// preserves sites, oracle cache decisions, and materializations.
pub fn pack_plan(
    plan: &EvalPlan,
    layer: &DagLayer,
    config: PackConfig,
) -> Result<PackedEvalPlan, PackError> {
    validate_config(config)?;
    let baseline = pack_plan_variant(plan, layer, config, false)?;
    let hoisted = pack_plan_variant(plan, layer, config, true)?;
    let baseline_key = (
        baseline.stats.packed_instructions,
        baseline.stats.encoded_lanes,
        baseline.stats.scalar_arithmetic_ops,
    );
    let hoisted_key = (
        hoisted.stats.packed_instructions,
        hoisted.stats.encoded_lanes,
        hoisted.stats.scalar_arithmetic_ops,
    );
    Ok(if hoisted_key < baseline_key {
        hoisted
    } else {
        baseline
    })
}

fn pack_plan_variant(
    plan: &EvalPlan,
    layer: &DagLayer,
    config: PackConfig,
    hoist_source_stores_before_fusion: bool,
) -> Result<PackedEvalPlan, PackError> {
    let mut ops = Vec::with_capacity(plan.ops.len());
    let mut acc_field = None;
    let normalized_units = normalize_unit_arithmetic(&plan.ops, layer);
    let transferred_residents = alias_dropped_resident_to_temp(&normalized_units);
    let aliased_saves = alias_saved_acc_to_resident(&transferred_residents);
    // Source-backed stores are accumulator-neutral. Schedule them before
    // arithmetic rewrites as well as final packing so they cannot hide an
    // otherwise contiguous sum/product/add pattern from FMA formation.
    let scheduled_stores = schedule_source_cache_stores(&aliased_saves, plan.budget_lanes, true)
        .into_iter()
        .cloned()
        .collect::<Vec<_>>();
    let arithmetic_input = if hoist_source_stores_before_fusion {
        &scheduled_stores
    } else {
        &aliased_saves
    };
    let saved_products = fuse_saved_products(arithmetic_input);
    let distributed = distribute_direct_sum_products(&saved_products, layer, plan.budget_lanes);

    for op in post_schedule_order(&distributed, plan.budget_lanes) {
        match op {
            EvalOp::AccInit(operand) => {
                acc_field = Some(operand_field(*operand));
                ops.push(PackedEvalOp::AccInit(*operand));
            }
            EvalOp::AccAdd { sign, operand } => {
                let before = acc_field.ok_or(PackError::MissingAccumulator)?;
                let field = operand_field(*operand);
                let promote = before == FieldKind::Base && field == FieldKind::Ext;
                let appended = if let Some(PackedEvalOp::AccAdd {
                    field: existing,
                    sign: existing_sign,
                    operands,
                    ..
                }) = ops.last_mut()
                {
                    if *existing == field
                        && *existing_sign == *sign
                        && operands.len() < config.max_add_operands
                    {
                        operands.push(*operand);
                        true
                    } else {
                        false
                    }
                } else {
                    false
                };
                if !appended {
                    ops.push(PackedEvalOp::AccAdd {
                        field,
                        promote,
                        sign: *sign,
                        operands: vec![*operand],
                    });
                }
                acc_field = Some(join(before, field));
            }
            EvalOp::AccMul(operand) => {
                let before = acc_field.ok_or(PackError::MissingAccumulator)?;
                let field = operand_field(*operand);
                let promote = before == FieldKind::Base && field == FieldKind::Ext;
                let appended = if let Some(PackedEvalOp::AccMul {
                    field: existing,
                    operands,
                    ..
                }) = ops.last_mut()
                {
                    if *existing == field && operands.len() < config.max_mul_operands {
                        operands.push(*operand);
                        true
                    } else {
                        false
                    }
                } else {
                    false
                };
                if !appended {
                    ops.push(PackedEvalOp::AccMul {
                        field,
                        promote,
                        sign: Sign::Plus,
                        operands: vec![*operand],
                    });
                }
                acc_field = Some(join(before, field));
            }
            EvalOp::AccFma { sign, lhs, rhs } => {
                let before = acc_field.ok_or(PackError::MissingAccumulator)?;
                let (lhs, rhs) = canonical_pair(*lhs, *rhs);
                let field_lhs = operand_field(lhs);
                let field_rhs = operand_field(rhs);
                let product_field = join(field_lhs, field_rhs);
                let promote = before == FieldKind::Base && product_field == FieldKind::Ext;
                let appended = if let Some(PackedEvalOp::AccFma {
                    field_lhs: existing_lhs,
                    field_rhs: existing_rhs,
                    sign: existing_sign,
                    pairs,
                    ..
                }) = ops.last_mut()
                {
                    if *existing_lhs == field_lhs
                        && *existing_rhs == field_rhs
                        && *existing_sign == *sign
                        && pairs.len() < config.max_fma_pairs
                    {
                        pairs.push((lhs, rhs));
                        true
                    } else {
                        false
                    }
                } else {
                    false
                };
                if !appended {
                    ops.push(PackedEvalOp::AccFma {
                        field_lhs,
                        field_rhs,
                        promote,
                        sign: *sign,
                        pairs: vec![(lhs, rhs)],
                    });
                }
                acc_field = Some(join(before, product_field));
            }
            EvalOp::AccNeg => {
                let field = acc_field.ok_or(PackError::MissingAccumulator)?;
                if let Some(PackedEvalOp::AccMul { sign, .. }) = ops.last_mut() {
                    *sign = match *sign {
                        Sign::Plus => Sign::Minus,
                        Sign::Minus => Sign::Plus,
                    };
                    if matches!(
                        ops.last(),
                        Some(PackedEvalOp::AccMul {
                            sign: Sign::Plus,
                            operands,
                            ..
                        }) if operands.is_empty()
                    ) {
                        ops.pop();
                    }
                } else {
                    ops.push(PackedEvalOp::AccMul {
                        field,
                        promote: false,
                        sign: Sign::Minus,
                        operands: Vec::new(),
                    });
                }
            }
            EvalOp::SaveAcc(temp) => ops.push(PackedEvalOp::SaveAcc(*temp)),
            EvalOp::CacheStore { value, from } => ops.push(PackedEvalOp::CacheStore {
                value: *value,
                from: *from,
            }),
            EvalOp::CacheDrop(value) => ops.push(PackedEvalOp::CacheDrop(*value)),
            EvalOp::Commit {
                root_id,
                root,
                sink,
                from,
            } => ops.push(PackedEvalOp::Commit {
                root_id: *root_id,
                root: root.clone(),
                sink: sink.clone(),
                from: *from,
            }),
            EvalOp::ReturnAcc { root } => ops.push(PackedEvalOp::ReturnAcc { root: root.clone() }),
        }
    }

    let stats = packed_stats(plan, &ops, layer)?;
    Ok(PackedEvalPlan { ops, stats })
}

/// Canonicalize field units before instruction formation. Multiplication by
/// positive one is a no-op, multiplication by negative one negates the
/// accumulator, and an FMA containing a unit is an Add with the product sign
/// folded into the additive sign. No concrete Mul/FMA may contain one.
fn normalize_unit_arithmetic(ops: &[EvalOp], layer: &DagLayer) -> Vec<EvalOp> {
    let mut normalized = Vec::with_capacity(ops.len());
    for op in ops {
        match op {
            EvalOp::AccAdd { sign, operand } => {
                if let Some(negative) = operand_unit_sign(*operand, layer) {
                    normalized.push(EvalOp::AccAdd {
                        sign: toggle_sign(*sign, negative),
                        operand: Operand::Unit { negative: false },
                    });
                } else {
                    normalized.push(op.clone());
                }
            }
            EvalOp::AccMul(operand) => match operand_unit_sign(*operand, layer) {
                Some(false) => {}
                Some(true) => normalized.push(EvalOp::AccNeg),
                None => normalized.push(op.clone()),
            },
            EvalOp::AccFma { sign, lhs, rhs } => {
                let lhs_sign = operand_unit_sign(*lhs, layer);
                let rhs_sign = operand_unit_sign(*rhs, layer);
                if lhs_sign.is_none() && rhs_sign.is_none() {
                    normalized.push(op.clone());
                    continue;
                }
                let sign =
                    toggle_sign(*sign, lhs_sign.unwrap_or(false) ^ rhs_sign.unwrap_or(false));
                let operand = match (lhs_sign, rhs_sign) {
                    (Some(_), Some(_)) => Operand::Unit { negative: false },
                    (Some(_), None) => *rhs,
                    (None, Some(_)) => *lhs,
                    (None, None) => unreachable!("handled above"),
                };
                normalized.push(EvalOp::AccAdd { sign, operand });
            }
            op => normalized.push(op.clone()),
        }
    }
    normalized
}

fn operand_unit_sign(operand: Operand, layer: &DagLayer) -> Option<bool> {
    match operand {
        Operand::Unit { negative } => Some(negative),
        Operand::Source(value) | Operand::Resident(value) => unit_sign_expr(layer, value.expr),
        Operand::Temp(_) => None,
    }
}

/// Transfer ownership of a resident cell to a temporary without loading and
/// re-saving the value. The exact safe shape is:
///
/// `init resident; drop resident; save temp; init ...`
///
/// where the temp has one later use and the resident is not redefined first.
/// The resident identity is used at that consumer and its drop moves there.
/// The original resident and temporary lifetimes are contiguous and have the
/// same width, so this changes neither storage pressure nor cache decisions.
fn alias_dropped_resident_to_temp(ops: &[EvalOp]) -> Vec<EvalOp> {
    let mut skip = vec![false; ops.len()];
    let mut replacements = std::collections::HashMap::<usize, EvalOp>::new();
    let mut insert_after = vec![Vec::<EvalOp>::new(); ops.len()];

    for index in 0..ops.len().saturating_sub(3) {
        let (
            EvalOp::AccInit(Operand::Resident(value)),
            EvalOp::CacheDrop(dropped),
            EvalOp::SaveAcc(temp),
            EvalOp::AccInit(_),
        ) = (
            &ops[index],
            &ops[index + 1],
            &ops[index + 2],
            &ops[index + 3],
        )
        else {
            continue;
        };
        if value.fingerprint != dropped.fingerprint || value.field != temp.field {
            continue;
        }

        let mut uses = (index + 3..ops.len()).filter(|&candidate| {
            eval_op_operands(&ops[candidate])
                .iter()
                .any(|operand| matches!(operand, Operand::Temp(found) if found.id == temp.id))
        });
        let Some(use_index) = uses.next() else {
            continue;
        };
        if uses.next().is_some()
            || ops[index + 3..use_index]
                .iter()
                .any(|op| cache_generation_boundary(op, value.fingerprint))
        {
            continue;
        }
        let use_op = replacements.get(&use_index).unwrap_or(&ops[use_index]);
        let Some(replacement) = replace_temp_operand(use_op, *temp, *value) else {
            continue;
        };

        skip[index] = true;
        skip[index + 1] = true;
        skip[index + 2] = true;
        replacements.insert(use_index, replacement);
        insert_after[use_index].push(EvalOp::CacheDrop(*value));
    }

    let mut rewritten = Vec::with_capacity(ops.len());
    for (index, op) in ops.iter().enumerate() {
        if !skip[index] {
            rewritten.push(
                replacements
                    .get(&index)
                    .cloned()
                    .unwrap_or_else(|| op.clone()),
            );
        }
        rewritten.extend(insert_after[index].iter().cloned());
    }
    rewritten
}

/// Elide a temporary save when an adjacent accumulator-backed cache store has
/// already materialized the identical value. The temporary's single use reads
/// that resident value directly, so this is a physical alias and emits no
/// copy. A cache drop or redefinition before the use makes aliasing illegal.
fn alias_saved_acc_to_resident(ops: &[EvalOp]) -> Vec<EvalOp> {
    let mut skip = vec![false; ops.len()];
    let mut replacements = std::collections::HashMap::<usize, EvalOp>::new();

    for index in 0..ops.len().saturating_sub(1) {
        let pair = (&ops[index], &ops[index + 1]);
        let (store_index, save_index, value, temp) = match pair {
            (
                EvalOp::CacheStore {
                    value,
                    from: CacheStoreFrom::Acc,
                },
                EvalOp::SaveAcc(temp),
            ) => (index, index + 1, *value, *temp),
            (
                EvalOp::SaveAcc(temp),
                EvalOp::CacheStore {
                    value,
                    from: CacheStoreFrom::Acc,
                },
            ) => (index + 1, index, *value, *temp),
            _ => continue,
        };
        if skip[save_index] || value.field != temp.field {
            continue;
        }

        let after_pair = store_index.max(save_index) + 1;
        let mut uses = (after_pair..ops.len()).filter(|&candidate| {
            eval_op_operands(&ops[candidate])
                .iter()
                .any(|operand| matches!(operand, Operand::Temp(found) if found.id == temp.id))
        });
        let Some(use_index) = uses.next() else {
            continue;
        };
        if uses.next().is_some()
            || ops[after_pair..use_index]
                .iter()
                .any(|op| cache_generation_boundary(op, value.fingerprint))
        {
            continue;
        }
        let use_op = replacements.get(&use_index).unwrap_or(&ops[use_index]);
        let Some(replacement) = replace_temp_operand(use_op, temp, value) else {
            continue;
        };

        skip[save_index] = true;
        replacements.insert(use_index, replacement);
    }

    ops.iter()
        .enumerate()
        .filter_map(|(index, op)| {
            if skip[index] {
                None
            } else {
                Some(
                    replacements
                        .get(&index)
                        .cloned()
                        .unwrap_or_else(|| op.clone()),
                )
            }
        })
        .collect()
}

fn replace_temp_operand(op: &EvalOp, temp: TempRef, value: ValueRef) -> Option<EvalOp> {
    let replace = |operand: Operand| match operand {
        Operand::Temp(found) if found.id == temp.id => Operand::Resident(value),
        operand => operand,
    };
    Some(match op {
        EvalOp::AccInit(Operand::Temp(found)) if found.id == temp.id => {
            EvalOp::AccInit(Operand::Resident(value))
        }
        EvalOp::AccAdd { sign, operand } if matches!(operand, Operand::Temp(found) if found.id == temp.id) => {
            EvalOp::AccAdd {
                sign: *sign,
                operand: Operand::Resident(value),
            }
        }
        EvalOp::AccMul(Operand::Temp(found)) if found.id == temp.id => {
            EvalOp::AccMul(Operand::Resident(value))
        }
        EvalOp::AccFma { sign, lhs, rhs }
            if matches!(lhs, Operand::Temp(found) if found.id == temp.id)
                || matches!(rhs, Operand::Temp(found) if found.id == temp.id) =>
        {
            EvalOp::AccFma {
                sign: *sign,
                lhs: replace(*lhs),
                rhs: replace(*rhs),
            }
        }
        _ => return None,
    })
}

/// When a product is immediately saved and later added back exactly once,
/// save the pre-product accumulator instead and perform the multiplication at
/// the consuming additive site as an FMA:
///
/// `acc *= factor; save t = acc; ...; acc += t`
/// becomes
/// `save t = acc; ...; acc += t * factor`.
///
/// This uses the existing temporary and removes one arithmetic instruction.
/// Delaying a direct source or unit is always safe; delaying a resident could
/// cross its cache generation boundary, and delaying another temporary would
/// extend its physical lifetime, so those cases remain unchanged. The saved
/// field must also be unchanged by the multiplication.
fn fuse_saved_products(ops: &[EvalOp]) -> Vec<EvalOp> {
    let mut skip = vec![false; ops.len()];
    let mut replacements = std::collections::HashMap::<usize, EvalOp>::new();

    for (mul_index, op) in ops.iter().enumerate() {
        let EvalOp::AccMul(factor) = op else {
            continue;
        };
        if !matches!(factor, Operand::Source(_) | Operand::Unit { .. }) {
            continue;
        }

        let mut save_index = mul_index + 1;
        let negated = matches!(ops.get(save_index), Some(EvalOp::AccNeg));
        save_index += usize::from(negated);
        let Some(EvalOp::SaveAcc(temp)) = ops.get(save_index) else {
            continue;
        };
        if accumulator_field_before(ops, mul_index) != Some(temp.field) {
            continue;
        }

        let mut uses = (save_index + 1..ops.len()).filter(|&index| {
            eval_op_operands(&ops[index]).iter().any(
                |operand| matches!(operand, Operand::Temp(candidate) if candidate.id == temp.id),
            )
        });
        let Some(use_index) = uses.next() else {
            continue;
        };
        if uses.next().is_some() {
            continue;
        }
        let EvalOp::AccAdd {
            sign,
            operand: Operand::Temp(used),
        } = ops[use_index]
        else {
            continue;
        };
        if used.id != temp.id || replacements.contains_key(&use_index) {
            continue;
        }

        let (factor, factor_negative) = normalize_unit(*factor);
        let sign = toggle_sign(sign, negated ^ factor_negative);
        let replacement = match factor {
            Operand::Unit { .. } => EvalOp::AccAdd {
                sign,
                operand: Operand::Temp(used),
            },
            factor => EvalOp::AccFma {
                sign,
                lhs: Operand::Temp(used),
                rhs: factor,
            },
        };
        skip[mul_index] = true;
        if negated {
            skip[mul_index + 1] = true;
        }
        replacements.insert(use_index, replacement);
    }

    ops.iter()
        .enumerate()
        .filter_map(|(index, op)| {
            if skip[index] {
                None
            } else {
                Some(
                    replacements
                        .get(&index)
                        .cloned()
                        .unwrap_or_else(|| op.clone()),
                )
            }
        })
        .collect()
}

fn accumulator_field_before(ops: &[EvalOp], end: usize) -> Option<FieldKind> {
    let mut field = None;
    for op in &ops[..end] {
        match op {
            EvalOp::AccInit(operand) => field = Some(operand_field(*operand)),
            EvalOp::AccAdd { operand, .. } | EvalOp::AccMul(operand) => {
                field = field.map(|before| join(before, operand_field(*operand)));
            }
            EvalOp::AccFma { lhs, rhs, .. } => {
                let product = join(operand_field(*lhs), operand_field(*rhs));
                field = field.map(|before| join(before, product));
            }
            _ => {}
        }
    }
    field
}

/// Distribute a single repeatable factor over a directly accumulated sum when
/// the following positive add supplies a new accumulator seed:
///
/// `acc = (a +/- b +/- ...) * f; acc += seed`
/// becomes
/// `acc = seed; acc += a*f; acc +/-= b*f; ...`.
///
/// The rewrite removes one scalar arithmetic operation and exposes an FMA run.
/// It never repeats a `Read` source or a temporary. Resident operands are
/// already materialized, and non-Read sources are DRAM-free. Signed field units
/// are strength-reduced to signed adds rather than emitted as multiplications.
fn distribute_direct_sum_products(
    ops: &[EvalOp],
    layer: &DagLayer,
    budget_lanes: usize,
) -> Vec<EvalOp> {
    let mut rewritten = Vec::with_capacity(ops.len());
    let live_before = storage_live_lanes_before(ops);
    let mut index = 0;

    while index < ops.len() {
        let EvalOp::AccInit(first) = ops[index] else {
            rewritten.push(ops[index].clone());
            index += 1;
            continue;
        };

        let mut sum_adds = Vec::new();
        let mut source_stores = Vec::new();
        let mut after_sum = index + 1;
        loop {
            match ops.get(after_sum) {
                Some(EvalOp::AccAdd { .. }) => sum_adds.push(after_sum),
                Some(EvalOp::CacheStore {
                    from: CacheStoreFrom::Source,
                    ..
                }) => source_stores.push(after_sum),
                _ => break,
            }
            after_sum += 1;
        }
        // A direct sum has at least two terms.
        if sum_adds.is_empty() {
            rewritten.push(ops[index].clone());
            index += 1;
            continue;
        }

        let Some(EvalOp::AccMul(factor)) = ops.get(after_sum) else {
            rewritten.push(ops[index].clone());
            index += 1;
            continue;
        };
        if !repeatable_factor(*factor, layer) {
            rewritten.push(ops[index].clone());
            index += 1;
            continue;
        }

        let mut after_product = after_sum + 1;
        let negated = matches!(ops.get(after_product), Some(EvalOp::AccNeg));
        after_product += usize::from(negated);
        let Some(EvalOp::AccAdd {
            sign: Sign::Plus,
            operand: seed,
        }) = ops.get(after_product)
        else {
            rewritten.push(ops[index].clone());
            index += 1;
            continue;
        };

        // Source-backed cache stores are accumulator-neutral. If one split the
        // direct sum, move only those matched stores before initialization.
        // Extending each lifetime must remain valid under the symbolic lane
        // budget; unrelated source stores keep their original positions.
        let mut motion_extra = vec![0usize; ops.len()];
        let stores_fit = source_stores.iter().all(|&store_index| {
            let EvalOp::CacheStore { value, .. } = &ops[store_index] else {
                unreachable!("source-store scan contains only CacheStore operations");
            };
            let width = field_lanes(value.field);
            let fits = (index..store_index).all(|position| {
                live_before[position]
                    .saturating_add(motion_extra[position])
                    .saturating_add(width)
                    <= budget_lanes
            });
            if fits {
                for extra in &mut motion_extra[index..store_index] {
                    *extra += width;
                }
            }
            fits
        });
        if !stores_fit {
            rewritten.push(ops[index].clone());
            index += 1;
            continue;
        }

        rewritten.extend(source_stores.iter().map(|&store| ops[store].clone()));
        rewritten.push(EvalOp::AccInit(*seed));
        let (factor, factor_negative) = normalize_unit(*factor);
        let product_negative = negated ^ factor_negative;

        let mut emit_term = |sign: Sign, term: Operand| {
            let (term, term_negative) = normalize_unit(term);
            let sign = toggle_sign(sign, product_negative ^ term_negative);
            match (term, factor) {
                (Operand::Unit { .. }, Operand::Unit { .. }) => {
                    rewritten.push(EvalOp::AccAdd {
                        sign,
                        operand: Operand::Unit { negative: false },
                    });
                }
                (Operand::Unit { .. }, factor) => {
                    rewritten.push(EvalOp::AccAdd {
                        sign,
                        operand: factor,
                    });
                }
                (term, Operand::Unit { .. }) => {
                    rewritten.push(EvalOp::AccAdd {
                        sign,
                        operand: term,
                    });
                }
                (term, factor) => rewritten.push(EvalOp::AccFma {
                    sign,
                    lhs: term,
                    rhs: factor,
                }),
            }
        };

        emit_term(Sign::Plus, first);
        for add_index in sum_adds {
            let EvalOp::AccAdd { sign, operand } = &ops[add_index] else {
                unreachable!("direct-sum add index contains only AccAdd operations");
            };
            emit_term(*sign, *operand);
        }
        index = after_product + 1;
    }

    rewritten
}

fn repeatable_factor(operand: Operand, layer: &DagLayer) -> bool {
    match operand {
        Operand::Resident(_) | Operand::Unit { .. } => true,
        Operand::Temp(_) => false,
        Operand::Source(value) => {
            if layer.resolutions.contains_key(&value.expr) {
                return true;
            }
            let Some(Expr::Source(source)) = layer.exprs.get(value.expr.0 as usize) else {
                return false;
            };
            !matches!(
                layer.sources[source.0 as usize].kind,
                SourceKind::Read { .. }
            )
        }
    }
}

fn normalize_unit(operand: Operand) -> (Operand, bool) {
    match operand {
        Operand::Unit { negative } => (Operand::Unit { negative: false }, negative),
        operand => (operand, false),
    }
}

fn toggle_sign(sign: Sign, toggle: bool) -> Sign {
    if toggle {
        match sign {
            Sign::Plus => Sign::Minus,
            Sign::Minus => Sign::Plus,
        }
    } else {
        sign
    }
}

fn post_schedule_order(ops: &[EvalOp], budget_lanes: usize) -> Vec<&EvalOp> {
    let ops = schedule_source_cache_stores(ops, budget_lanes, false);
    let mut ordered = Vec::with_capacity(ops.len());
    let mut index = 0;
    while index < ops.len() {
        if matches!(ops[index], EvalOp::AccAdd { .. } | EvalOp::AccFma { .. }) {
            let mut run = Vec::new();
            let mut drops = Vec::new();
            while index < ops.len()
                && matches!(
                    ops[index],
                    EvalOp::AccAdd { .. } | EvalOp::AccFma { .. } | EvalOp::CacheDrop(_)
                )
            {
                match ops[index] {
                    EvalOp::CacheDrop(_) => drops.push(ops[index]),
                    _ => run.push(ops[index]),
                }
                index += 1;
            }
            run.sort_by_key(|op| additive_order_key(op));
            ordered.extend(run);
            ordered.extend(drops);
        } else if matches!(ops[index], EvalOp::AccMul(_) | EvalOp::AccNeg) {
            let mut run = Vec::new();
            let mut drops = Vec::new();
            while index < ops.len()
                && matches!(
                    ops[index],
                    EvalOp::AccMul(_) | EvalOp::AccNeg | EvalOp::CacheDrop(_)
                )
            {
                match ops[index] {
                    EvalOp::CacheDrop(_) => drops.push(ops[index]),
                    _ => run.push(ops[index]),
                }
                index += 1;
            }
            run.sort_by_key(|op| match op {
                EvalOp::AccMul(operand) => (0u8, field_key(operand_field(*operand))),
                EvalOp::AccNeg => (1u8, 0),
                _ => unreachable!("multiplicative run contains only Mul/Neg"),
            });
            ordered.extend(run);
            ordered.extend(drops);
        } else {
            ordered.push(ops[index]);
            index += 1;
        }
    }
    ordered
}

/// A source-backed cache fill neither reads nor writes the accumulator. Place
/// each one at the latest boundary before its first resident use that is also
/// outside that use's packable arithmetic run. This permits motion in either
/// direction, avoids splitting both the production-side and consumption-side
/// runs, and minimizes the stored value's physical live range. A same-value
/// drop/store is a hard cache-generation boundary.
fn schedule_source_cache_stores(
    ops: &[EvalOp],
    budget_lanes: usize,
    cross_acc_init: bool,
) -> Vec<&EvalOp> {
    let mut scheduled_before = vec![Vec::<&EvalOp>::new(); ops.len()];
    let mut moved = vec![false; ops.len()];
    let live_before = storage_live_lanes_before(ops);
    let mut motion_extra = vec![0usize; ops.len()];

    for (store_index, op) in ops.iter().enumerate() {
        let EvalOp::CacheStore {
            value,
            from: CacheStoreFrom::Source,
        } = op
        else {
            continue;
        };
        let fingerprint = value.fingerprint;
        let generation_end = ops[store_index + 1..]
            .iter()
            .position(|candidate| cache_generation_boundary(candidate, fingerprint))
            .map_or(ops.len(), |offset| store_index + 1 + offset);
        let Some(first_use) = (store_index + 1..generation_end)
            .find(|&index| eval_op_reads_resident(&ops[index], fingerprint))
        else {
            scheduled_before[store_index].push(op);
            moved[store_index] = true;
            continue;
        };

        let mut target = first_use;
        let family = arithmetic_family(&ops[first_use]);
        while target > 0 {
            let previous = &ops[target - 1];
            if target - 1 != store_index && cache_generation_boundary(previous, fingerprint) {
                break;
            }
            if matches!(previous, EvalOp::CacheDrop(_))
                || matches!(
                    previous,
                    EvalOp::CacheStore {
                        from: CacheStoreFrom::Source,
                        ..
                    }
                )
                || (cross_acc_init && matches!(previous, EvalOp::AccInit(_)))
                || family.is_some_and(|family| arithmetic_family(previous) == Some(family))
            {
                target -= 1;
            } else {
                break;
            }
        }
        if target < store_index {
            let width = field_lanes(value.field);
            let fits = (target..store_index).all(|index| {
                live_before[index]
                    .saturating_add(motion_extra[index])
                    .saturating_add(width)
                    <= budget_lanes
            });
            if fits {
                for extra in &mut motion_extra[target..store_index] {
                    *extra += width;
                }
            } else {
                target = store_index;
            }
        }
        scheduled_before[target].push(op);
        moved[store_index] = true;
    }

    let mut ordered = Vec::with_capacity(ops.len());
    for (index, op) in ops.iter().enumerate() {
        ordered.extend(scheduled_before[index].iter().copied());
        if !moved[index] {
            ordered.push(op);
        }
    }
    ordered
}

fn storage_live_lanes_before(ops: &[EvalOp]) -> Vec<usize> {
    let mut residents = std::collections::HashMap::<ValueFingerprint, usize>::new();
    let mut temps = std::collections::HashMap::<TempId, usize>::new();
    let mut live = 0usize;
    let mut before = Vec::with_capacity(ops.len());
    for op in ops {
        before.push(live);
        for operand in eval_op_operands(op) {
            if let Operand::Temp(temp) = operand {
                if let Some(width) = temps.remove(&temp.id) {
                    live -= width;
                }
            }
        }
        match op {
            EvalOp::SaveAcc(temp) => {
                let width = field_lanes(temp.field);
                temps.insert(temp.id, width);
                live += width;
            }
            EvalOp::CacheStore { value, .. } => {
                let width = field_lanes(value.field);
                residents.insert(value.fingerprint, width);
                live += width;
            }
            EvalOp::CacheDrop(value) => {
                if let Some(width) = residents.remove(&value.fingerprint) {
                    live -= width;
                }
            }
            _ => {}
        }
    }
    before
}

fn eval_op_operands(op: &EvalOp) -> Vec<Operand> {
    match op {
        EvalOp::AccInit(operand) | EvalOp::AccMul(operand) => vec![*operand],
        EvalOp::AccAdd { operand, .. } => vec![*operand],
        EvalOp::AccFma { lhs, rhs, .. } => vec![*lhs, *rhs],
        _ => Vec::new(),
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ArithmeticFamily {
    Additive,
    Multiplicative,
}

fn arithmetic_family(op: &EvalOp) -> Option<ArithmeticFamily> {
    match op {
        EvalOp::AccAdd { .. } | EvalOp::AccFma { .. } => Some(ArithmeticFamily::Additive),
        EvalOp::AccMul(_) | EvalOp::AccNeg => Some(ArithmeticFamily::Multiplicative),
        _ => None,
    }
}

fn cache_generation_boundary(op: &EvalOp, fingerprint: ValueFingerprint) -> bool {
    matches!(
        op,
        EvalOp::CacheStore { value, .. } | EvalOp::CacheDrop(value)
            if value.fingerprint == fingerprint
    )
}

fn eval_op_reads_resident(op: &EvalOp, fingerprint: ValueFingerprint) -> bool {
    let reads = |operand: Operand| matches!(operand, Operand::Resident(value) if value.fingerprint == fingerprint);
    match op {
        EvalOp::AccInit(operand) | EvalOp::AccMul(operand) => reads(*operand),
        EvalOp::AccAdd { operand, .. } => reads(*operand),
        EvalOp::AccFma { lhs, rhs, .. } => reads(*lhs) || reads(*rhs),
        _ => false,
    }
}

fn additive_order_key(op: &EvalOp) -> (u8, u8, u8, u8) {
    match op {
        EvalOp::AccAdd { sign, operand } => {
            (field_key(operand_field(*operand)), 0, sign_key(*sign), 0)
        }
        EvalOp::AccFma { sign, lhs, rhs } => {
            let (lhs, rhs) = canonical_pair(*lhs, *rhs);
            let lhs = field_key(operand_field(lhs));
            let rhs = field_key(operand_field(rhs));
            (lhs.max(rhs), 1, sign_key(*sign), 2 * lhs + rhs)
        }
        _ => unreachable!("additive run contains only Add/Fma"),
    }
}

fn sign_key(sign: Sign) -> u8 {
    match sign {
        Sign::Plus => 0,
        Sign::Minus => 1,
    }
}

fn validate_config(config: PackConfig) -> Result<(), PackError> {
    for requested in [
        config.max_add_operands,
        config.max_mul_operands,
        config.max_fma_pairs,
    ] {
        if requested == 0 {
            return Err(PackError::ZeroArityLimit);
        }
        if requested > MAX_ARITY {
            return Err(PackError::ArityLimitExceedsIsa {
                requested,
                maximum: MAX_ARITY,
            });
        }
    }
    Ok(())
}

fn packed_stats(
    plan: &EvalPlan,
    ops: &[PackedEvalOp],
    layer: &DagLayer,
) -> Result<PackedStats, PackError> {
    let mut stats = PackedStats {
        unpacked_instructions: plan
            .ops
            .iter()
            .filter(|op| !matches!(op, EvalOp::CacheDrop(_) | EvalOp::ReturnAcc { .. }))
            .count(),
        ..PackedStats::default()
    };
    for op in ops {
        match op {
            PackedEvalOp::AccInit(operand) => {
                stats.packed_instructions += 1;
                stats.encoded_lanes += 2;
                count_operand(layer, *operand, &mut stats)?;
            }
            PackedEvalOp::AccAdd { operands, .. } => {
                stats.packed_instructions += 1;
                stats.arithmetic_instructions += 1;
                stats.scalar_arithmetic_ops += operands.len();
                stats.encoded_lanes += 1 + operands.len();
                for &operand in operands {
                    count_operand(layer, operand, &mut stats)?;
                }
            }
            PackedEvalOp::AccMul { sign, operands, .. } => {
                stats.packed_instructions += 1;
                stats.arithmetic_instructions += 1;
                stats.scalar_arithmetic_ops += operands.len() + usize::from(*sign == Sign::Minus);
                stats.encoded_lanes += 1 + operands.len();
                for &operand in operands {
                    count_operand(layer, operand, &mut stats)?;
                }
            }
            PackedEvalOp::AccFma { pairs, .. } => {
                stats.packed_instructions += 1;
                stats.arithmetic_instructions += 1;
                stats.scalar_arithmetic_ops += pairs.len();
                stats.encoded_lanes += 1 + 2 * pairs.len();
                for &(lhs, rhs) in pairs {
                    count_operand(layer, lhs, &mut stats)?;
                    count_operand(layer, rhs, &mut stats)?;
                }
            }
            PackedEvalOp::SaveAcc(_) => {
                stats.packed_instructions += 1;
                stats.encoded_lanes += 2;
            }
            PackedEvalOp::Commit { from, .. } => {
                stats.packed_instructions += 1;
                match from {
                    MaterializeFrom::Acc => stats.encoded_lanes += 2,
                    MaterializeFrom::Source(value) => {
                        stats.encoded_lanes += 3;
                        count_operand(layer, Operand::Source(*value), &mut stats)?;
                    }
                }
            }
            PackedEvalOp::CacheStore { value, from } => {
                stats.packed_instructions += 1;
                match from {
                    CacheStoreFrom::Acc => stats.encoded_lanes += 2,
                    CacheStoreFrom::Source => {
                        stats.encoded_lanes += 3;
                        count_operand(layer, Operand::Source(*value), &mut stats)?;
                    }
                }
            }
            PackedEvalOp::CacheDrop(_) | PackedEvalOp::ReturnAcc { .. } => {}
        }
    }
    if stats.dram_read_lanes != plan.stats.dram_read_lanes {
        return Err(PackError::DramTrafficMismatch {
            plan: plan.stats.dram_read_lanes,
            packed: stats.dram_read_lanes,
        });
    }
    if stats.scalar_arithmetic_ops > plan.stats.arithmetic_ops {
        return Err(PackError::ArithmeticCountMismatch {
            plan: plan.stats.arithmetic_ops,
            packed: stats.scalar_arithmetic_ops,
        });
    }
    stats.optimized_away_arithmetic_ops = plan.stats.arithmetic_ops - stats.scalar_arithmetic_ops;
    Ok(stats)
}

fn count_operand(
    layer: &DagLayer,
    operand: Operand,
    stats: &mut PackedStats,
) -> Result<(), PackError> {
    let Operand::Source(value) = operand else {
        return Ok(());
    };
    if layer.resolutions.contains_key(&value.expr) {
        return Ok(());
    }
    let Expr::Source(source) = layer.exprs[value.expr.0 as usize] else {
        return Err(PackError::ExpectedSource(value));
    };
    if matches!(
        layer.sources[source.0 as usize].kind,
        SourceKind::Read { .. }
    ) {
        stats.dram_read_lanes += field_lanes(value.field);
    }
    Ok(())
}

fn operand_field(operand: Operand) -> FieldKind {
    match operand {
        Operand::Source(value) | Operand::Resident(value) => value.field,
        Operand::Temp(temp) => temp.field,
        Operand::Unit { .. } => FieldKind::Base,
    }
}

fn canonical_pair(lhs: Operand, rhs: Operand) -> (Operand, Operand) {
    if field_key(operand_field(lhs)) <= field_key(operand_field(rhs)) {
        (lhs, rhs)
    } else {
        (rhs, lhs)
    }
}

fn field_key(field: FieldKind) -> u8 {
    match field {
        FieldKind::Base => 0,
        FieldKind::Ext => 1,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::eval_plan::{ValueFingerprint, ValueRef};
    use cs::gkr_compiler::dag_ir::{ArenaBuilder, BatchingOrder, ExprId, ReadPlace, SourceKind};

    fn value(expr: u32, field: FieldKind) -> ValueRef {
        ValueRef {
            expr: ExprId(expr),
            fingerprint: ValueFingerprint([expr as u64, 0]),
            field,
        }
    }

    fn source_value(expr: ExprId, field: FieldKind) -> ValueRef {
        value(expr.0, field)
    }

    fn source(arena: &mut ArenaBuilder, kind: SourceKind) -> ExprId {
        let source = arena.intern_source(kind);
        arena.source_expr(source)
    }

    fn layer(arena: &ArenaBuilder) -> DagLayer {
        DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: Vec::new(),
            batching: BatchingOrder { roots: Vec::new() },
            resolutions: BTreeMap::new(),
        }
    }

    #[test]
    fn unit_products_are_strength_reduced_before_packing() {
        let mut arena = ArenaBuilder::new();
        let expr = source(&mut arena, SourceKind::Constant { value: 2 });
        let layer = layer(&arena);
        let value = source_value(expr, FieldKind::Base);
        let ops = vec![
            EvalOp::AccInit(Operand::Source(value)),
            EvalOp::AccMul(Operand::Unit { negative: false }),
            EvalOp::AccMul(Operand::Unit { negative: true }),
            EvalOp::AccFma {
                sign: Sign::Minus,
                lhs: Operand::Unit { negative: true },
                rhs: Operand::Source(value),
            },
            EvalOp::AccFma {
                sign: Sign::Plus,
                lhs: Operand::Unit { negative: true },
                rhs: Operand::Unit { negative: false },
            },
        ];

        assert_eq!(
            normalize_unit_arithmetic(&ops, &layer),
            vec![
                EvalOp::AccInit(Operand::Source(value)),
                EvalOp::AccNeg,
                EvalOp::AccAdd {
                    sign: Sign::Plus,
                    operand: Operand::Source(value),
                },
                EvalOp::AccAdd {
                    sign: Sign::Minus,
                    operand: Operand::Unit { negative: false },
                },
            ]
        );
    }

    #[test]
    fn source_and_resident_units_are_strength_reduced_before_packing() {
        let mut arena = ArenaBuilder::new();
        let one_expr = source(&mut arena, SourceKind::Constant { value: 1 });
        let value_expr = source(&mut arena, SourceKind::Constant { value: 2 });
        let layer = layer(&arena);
        let one = source_value(one_expr, FieldKind::Base);
        let value = source_value(value_expr, FieldKind::Base);
        let ops = vec![
            EvalOp::AccInit(Operand::Source(value)),
            EvalOp::AccMul(Operand::Source(one)),
            EvalOp::AccFma {
                sign: Sign::Minus,
                lhs: Operand::Resident(one),
                rhs: Operand::Source(value),
            },
        ];

        assert_eq!(
            normalize_unit_arithmetic(&ops, &layer),
            vec![
                EvalOp::AccInit(Operand::Source(value)),
                EvalOp::AccAdd {
                    sign: Sign::Minus,
                    operand: Operand::Source(value),
                },
            ]
        );
    }

    #[test]
    fn dropped_resident_transfers_to_temp_without_a_copy() {
        let resident = value(0, FieldKind::Ext);
        let outer = value(1, FieldKind::Ext);
        let addend = value(2, FieldKind::Base);
        let temp = TempRef {
            id: TempId(0),
            field: FieldKind::Ext,
        };
        let ops = vec![
            EvalOp::AccInit(Operand::Resident(resident)),
            EvalOp::CacheDrop(resident),
            EvalOp::SaveAcc(temp),
            EvalOp::AccInit(Operand::Source(outer)),
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Source(addend),
            },
            EvalOp::AccMul(Operand::Temp(temp)),
        ];

        assert_eq!(
            alias_dropped_resident_to_temp(&ops),
            vec![
                EvalOp::AccInit(Operand::Source(outer)),
                EvalOp::AccAdd {
                    sign: Sign::Plus,
                    operand: Operand::Source(addend),
                },
                EvalOp::AccMul(Operand::Resident(resident)),
                EvalOp::CacheDrop(resident),
            ]
        );
    }

    #[test]
    fn resident_transfer_does_not_cross_a_redefinition() {
        let resident = value(0, FieldKind::Ext);
        let outer = value(1, FieldKind::Ext);
        let temp = TempRef {
            id: TempId(0),
            field: FieldKind::Ext,
        };
        let ops = vec![
            EvalOp::AccInit(Operand::Resident(resident)),
            EvalOp::CacheDrop(resident),
            EvalOp::SaveAcc(temp),
            EvalOp::AccInit(Operand::Source(outer)),
            EvalOp::CacheStore {
                value: resident,
                from: CacheStoreFrom::Acc,
            },
            EvalOp::AccMul(Operand::Temp(temp)),
        ];

        assert_eq!(alias_dropped_resident_to_temp(&ops), ops);
    }

    #[test]
    fn adjacent_acc_store_and_save_share_the_resident_value() {
        let cached = value(0, FieldKind::Ext);
        let outer = value(1, FieldKind::Ext);
        let temp = TempRef {
            id: TempId(0),
            field: FieldKind::Ext,
        };
        let ops = vec![
            EvalOp::CacheStore {
                value: cached,
                from: CacheStoreFrom::Acc,
            },
            EvalOp::SaveAcc(temp),
            EvalOp::AccInit(Operand::Source(outer)),
            EvalOp::AccMul(Operand::Temp(temp)),
            EvalOp::CacheDrop(cached),
        ];

        assert_eq!(
            alias_saved_acc_to_resident(&ops),
            vec![
                EvalOp::CacheStore {
                    value: cached,
                    from: CacheStoreFrom::Acc,
                },
                EvalOp::AccInit(Operand::Source(outer)),
                EvalOp::AccMul(Operand::Resident(cached)),
                EvalOp::CacheDrop(cached),
            ]
        );
    }

    #[test]
    fn resident_alias_does_not_cross_a_cache_drop() {
        let cached = value(0, FieldKind::Ext);
        let outer = value(1, FieldKind::Ext);
        let temp = TempRef {
            id: TempId(0),
            field: FieldKind::Ext,
        };
        let ops = vec![
            EvalOp::SaveAcc(temp),
            EvalOp::CacheStore {
                value: cached,
                from: CacheStoreFrom::Acc,
            },
            EvalOp::CacheDrop(cached),
            EvalOp::AccInit(Operand::Source(outer)),
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Temp(temp),
            },
        ];

        assert_eq!(alias_saved_acc_to_resident(&ops), ops);
    }

    #[test]
    fn two_saved_operands_can_alias_into_the_same_fma() {
        let lhs_value = value(0, FieldKind::Base);
        let rhs_value = value(1, FieldKind::Base);
        let lhs_temp = TempRef {
            id: TempId(0),
            field: FieldKind::Base,
        };
        let rhs_temp = TempRef {
            id: TempId(1),
            field: FieldKind::Base,
        };
        let ops = vec![
            EvalOp::CacheStore {
                value: lhs_value,
                from: CacheStoreFrom::Acc,
            },
            EvalOp::SaveAcc(lhs_temp),
            EvalOp::CacheStore {
                value: rhs_value,
                from: CacheStoreFrom::Acc,
            },
            EvalOp::SaveAcc(rhs_temp),
            EvalOp::AccFma {
                sign: Sign::Plus,
                lhs: Operand::Temp(lhs_temp),
                rhs: Operand::Temp(rhs_temp),
            },
        ];

        let rewritten = alias_saved_acc_to_resident(&ops);
        assert!(matches!(
            rewritten.last(),
            Some(EvalOp::AccFma {
                lhs: Operand::Resident(lhs),
                rhs: Operand::Resident(rhs),
                ..
            }) if *lhs == lhs_value && *rhs == rhs_value
        ));
        assert!(!rewritten.iter().any(|op| matches!(op, EvalOp::SaveAcc(_))));
    }

    #[test]
    fn saved_product_becomes_fma_at_its_additive_use() {
        let inner = value(0, FieldKind::Ext);
        let factor = value(1, FieldKind::Base);
        let outer = value(2, FieldKind::Ext);
        let other = value(3, FieldKind::Base);
        let temp = TempRef {
            id: TempId(0),
            field: FieldKind::Ext,
        };
        let ops = vec![
            EvalOp::AccInit(Operand::Source(inner)),
            EvalOp::AccMul(Operand::Source(factor)),
            EvalOp::AccNeg,
            EvalOp::SaveAcc(temp),
            EvalOp::AccInit(Operand::Source(outer)),
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Source(other),
            },
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Temp(temp),
            },
        ];

        assert_eq!(
            fuse_saved_products(&ops),
            vec![
                EvalOp::AccInit(Operand::Source(inner)),
                EvalOp::SaveAcc(temp),
                EvalOp::AccInit(Operand::Source(outer)),
                EvalOp::AccAdd {
                    sign: Sign::Plus,
                    operand: Operand::Source(other),
                },
                EvalOp::AccFma {
                    sign: Sign::Minus,
                    lhs: Operand::Temp(temp),
                    rhs: Operand::Source(factor),
                },
            ]
        );
    }

    #[test]
    fn saved_product_rewrite_refuses_field_widening() {
        let inner = value(0, FieldKind::Base);
        let factor = value(1, FieldKind::Ext);
        let outer = value(2, FieldKind::Ext);
        let temp = TempRef {
            id: TempId(0),
            field: FieldKind::Ext,
        };
        let ops = vec![
            EvalOp::AccInit(Operand::Source(inner)),
            EvalOp::AccMul(Operand::Source(factor)),
            EvalOp::SaveAcc(temp),
            EvalOp::AccInit(Operand::Source(outer)),
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Temp(temp),
            },
        ];

        assert_eq!(fuse_saved_products(&ops), ops);
    }

    #[test]
    fn saved_unit_product_cancels_sign_without_a_multiply() {
        let inner = value(0, FieldKind::Base);
        let outer = value(1, FieldKind::Base);
        let temp = TempRef {
            id: TempId(0),
            field: FieldKind::Base,
        };
        let ops = vec![
            EvalOp::AccInit(Operand::Source(inner)),
            EvalOp::AccMul(Operand::Unit { negative: true }),
            EvalOp::AccNeg,
            EvalOp::SaveAcc(temp),
            EvalOp::AccInit(Operand::Source(outer)),
            EvalOp::AccAdd {
                sign: Sign::Minus,
                operand: Operand::Temp(temp),
            },
        ];

        let rewritten = fuse_saved_products(&ops);
        assert!(matches!(
            rewritten.last(),
            Some(EvalOp::AccAdd {
                sign: Sign::Minus,
                operand: Operand::Temp(candidate),
            }) if *candidate == temp
        ));
        assert!(
            !rewritten
                .iter()
                .any(|op| matches!(op, EvalOp::AccMul(_) | EvalOp::AccNeg))
        );
    }

    #[test]
    fn distributes_direct_sum_with_sign_cancellation() {
        let mut arena = ArenaBuilder::new();
        let a = source_value(
            source(&mut arena, SourceKind::Constant { value: 2 }),
            FieldKind::Base,
        );
        let b = source_value(
            source(&mut arena, SourceKind::Constant { value: 3 }),
            FieldKind::Base,
        );
        let factor = source_value(
            source(&mut arena, SourceKind::Constant { value: 5 }),
            FieldKind::Base,
        );
        let seed = source_value(
            source(&mut arena, SourceKind::Constant { value: 7 }),
            FieldKind::Base,
        );
        let layer = layer(&arena);
        let ops = vec![
            EvalOp::AccInit(Operand::Source(a)),
            EvalOp::AccAdd {
                sign: Sign::Minus,
                operand: Operand::Source(b),
            },
            EvalOp::AccMul(Operand::Source(factor)),
            EvalOp::AccNeg,
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Source(seed),
            },
        ];

        let rewritten = distribute_direct_sum_products(&ops, &layer, usize::MAX);
        assert_eq!(
            rewritten,
            vec![
                EvalOp::AccInit(Operand::Source(seed)),
                EvalOp::AccFma {
                    sign: Sign::Minus,
                    lhs: Operand::Source(a),
                    rhs: Operand::Source(factor),
                },
                EvalOp::AccFma {
                    sign: Sign::Plus,
                    lhs: Operand::Source(b),
                    rhs: Operand::Source(factor),
                },
            ]
        );
    }

    #[test]
    fn distributed_units_become_signed_adds() {
        let mut arena = ArenaBuilder::new();
        let b = source_value(
            source(&mut arena, SourceKind::Constant { value: 3 }),
            FieldKind::Base,
        );
        let seed = source_value(
            source(&mut arena, SourceKind::Constant { value: 7 }),
            FieldKind::Base,
        );
        let layer = layer(&arena);
        let ops = vec![
            EvalOp::AccInit(Operand::Unit { negative: true }),
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Source(b),
            },
            EvalOp::AccMul(Operand::Unit { negative: true }),
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Source(seed),
            },
        ];

        let rewritten = distribute_direct_sum_products(&ops, &layer, usize::MAX);
        assert_eq!(
            rewritten,
            vec![
                EvalOp::AccInit(Operand::Source(seed)),
                EvalOp::AccAdd {
                    sign: Sign::Plus,
                    operand: Operand::Unit { negative: false },
                },
                EvalOp::AccAdd {
                    sign: Sign::Minus,
                    operand: Operand::Source(b),
                },
            ]
        );
        assert!(!rewritten.iter().any(|op| matches!(
            op,
            EvalOp::AccMul(_)
                | EvalOp::AccFma {
                    lhs: Operand::Unit { .. },
                    ..
                }
                | EvalOp::AccFma {
                    rhs: Operand::Unit { .. },
                    ..
                }
        )));
    }

    #[test]
    fn does_not_distribute_a_dram_factor() {
        let mut arena = ArenaBuilder::new();
        let a = source_value(
            source(&mut arena, SourceKind::Constant { value: 2 }),
            FieldKind::Base,
        );
        let b = source_value(
            source(&mut arena, SourceKind::Constant { value: 3 }),
            FieldKind::Base,
        );
        let factor = source_value(
            source(
                &mut arena,
                SourceKind::Read {
                    place: ReadPlace::BaseLayerWitness { column: 0 },
                },
            ),
            FieldKind::Base,
        );
        let seed = source_value(
            source(&mut arena, SourceKind::Constant { value: 7 }),
            FieldKind::Base,
        );
        let layer = layer(&arena);
        let ops = vec![
            EvalOp::AccInit(Operand::Source(a)),
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Source(b),
            },
            EvalOp::AccMul(Operand::Source(factor)),
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Source(seed),
            },
        ];

        assert_eq!(
            distribute_direct_sum_products(&ops, &layer, usize::MAX),
            ops
        );
    }

    #[test]
    fn cache_drop_does_not_split_an_additive_run() {
        let resident = value(0, FieldKind::Base);
        let lhs = value(1, FieldKind::Base);
        let rhs = value(2, FieldKind::Base);
        let ops = vec![
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Resident(resident),
            },
            EvalOp::CacheDrop(resident),
            EvalOp::AccFma {
                sign: Sign::Plus,
                lhs: Operand::Source(lhs),
                rhs: Operand::Source(rhs),
            },
        ];

        let ordered = post_schedule_order(&ops, 16);
        assert!(matches!(ordered[0], EvalOp::AccAdd { .. }));
        assert!(matches!(ordered[1], EvalOp::AccFma { .. }));
        assert!(matches!(ordered[2], EvalOp::CacheDrop(value) if *value == resident));
    }

    #[test]
    fn source_cache_store_moves_before_first_resident_arithmetic_run() {
        let initial = value(0, FieldKind::Base);
        let cached = value(1, FieldKind::Base);
        let rhs = value(2, FieldKind::Base);
        let ops = vec![
            EvalOp::AccInit(Operand::Source(initial)),
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Source(cached),
            },
            EvalOp::CacheStore {
                value: cached,
                from: CacheStoreFrom::Source,
            },
            EvalOp::AccFma {
                sign: Sign::Plus,
                lhs: Operand::Resident(cached),
                rhs: Operand::Source(rhs),
            },
        ];

        let ordered = post_schedule_order(&ops, 16);
        assert!(matches!(ordered[0], EvalOp::AccInit(_)));
        assert!(matches!(
            ordered[1],
            EvalOp::CacheStore {
                value,
                from: CacheStoreFrom::Source,
            } if *value == cached
        ));
        assert!(matches!(ordered[2], EvalOp::AccAdd { .. }));
        assert!(matches!(ordered[3], EvalOp::AccFma { .. }));
    }

    #[test]
    fn scheduled_source_store_exposes_distributive_fma() {
        let mut arena = ArenaBuilder::new();
        let cached = source_value(
            source(
                &mut arena,
                SourceKind::Read {
                    place: ReadPlace::BaseLayerWitness { column: 0 },
                },
            ),
            FieldKind::Base,
        );
        let factor = source_value(
            source(&mut arena, SourceKind::Constant { value: 2 }),
            FieldKind::Base,
        );
        let seed = source_value(
            source(&mut arena, SourceKind::Constant { value: 3 }),
            FieldKind::Base,
        );
        let layer = layer(&arena);
        let ops = vec![
            EvalOp::AccInit(Operand::Unit { negative: false }),
            EvalOp::CacheStore {
                value: cached,
                from: CacheStoreFrom::Source,
            },
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Resident(cached),
            },
            EvalOp::AccMul(Operand::Source(factor)),
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Source(seed),
            },
        ];

        let scheduled = schedule_source_cache_stores(&ops, 16, true)
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();
        assert!(matches!(scheduled[0], EvalOp::CacheStore { .. }));
        let expected = vec![
            ops[1].clone(),
            EvalOp::AccInit(Operand::Source(seed)),
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Source(factor),
            },
            EvalOp::AccFma {
                sign: Sign::Plus,
                lhs: Operand::Resident(cached),
                rhs: Operand::Source(factor),
            },
        ];
        assert_eq!(
            distribute_direct_sum_products(&scheduled, &layer, 16),
            expected
        );
        assert_eq!(
            distribute_direct_sum_products(&ops, &layer, 16),
            expected,
            "the local distributor should move only its blocking source store"
        );
    }

    #[test]
    fn source_cache_store_does_not_cross_a_full_budget_boundary() {
        let initial = value(0, FieldKind::Ext);
        let cached = value(1, FieldKind::Base);
        let rhs = value(2, FieldKind::Base);
        let temp = TempRef {
            id: TempId(0),
            field: FieldKind::Ext,
        };
        let ops = vec![
            EvalOp::AccInit(Operand::Source(initial)),
            EvalOp::SaveAcc(temp),
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Temp(temp),
            },
            EvalOp::CacheStore {
                value: cached,
                from: CacheStoreFrom::Source,
            },
            EvalOp::AccFma {
                sign: Sign::Plus,
                lhs: Operand::Resident(cached),
                rhs: Operand::Source(rhs),
            },
        ];

        let ordered = post_schedule_order(&ops, 4);
        assert!(matches!(ordered[2], EvalOp::AccAdd { .. }));
        assert!(matches!(
            ordered[3],
            EvalOp::CacheStore {
                value,
                from: CacheStoreFrom::Source,
            } if *value == cached
        ));
        assert!(matches!(ordered[4], EvalOp::AccFma { .. }));
    }

    #[test]
    fn distributive_store_motion_respects_a_full_pre_init_budget() {
        let mut arena = ArenaBuilder::new();
        let cached = source_value(
            source(
                &mut arena,
                SourceKind::Read {
                    place: ReadPlace::BaseLayerWitness { column: 0 },
                },
            ),
            FieldKind::Base,
        );
        let factor = source_value(
            source(&mut arena, SourceKind::Constant { value: 2 }),
            FieldKind::Base,
        );
        let seed = source_value(
            source(&mut arena, SourceKind::Constant { value: 3 }),
            FieldKind::Base,
        );
        let layer = layer(&arena);
        let temp = TempRef {
            id: TempId(0),
            field: FieldKind::Ext,
        };
        let ops = vec![
            EvalOp::AccInit(Operand::Unit { negative: false }),
            EvalOp::SaveAcc(temp),
            EvalOp::AccInit(Operand::Temp(temp)),
            EvalOp::CacheStore {
                value: cached,
                from: CacheStoreFrom::Source,
            },
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Resident(cached),
            },
            EvalOp::AccMul(Operand::Source(factor)),
            EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Source(seed),
            },
        ];

        assert_eq!(
            distribute_direct_sum_products(&ops, &layer, 4),
            ops,
            "the Base store cannot move across an Ext temporary filling b4"
        );
    }
}
