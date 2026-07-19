use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::FieldKind;

use crate::bwd::cost::{CELL_BYTES, EXT_BYTES};
use crate::bwd::source::FoldState;

use super::{BackwardSearchError, RoundProfile, SourceCost, SourceOpCost, SourceRoundBinding};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceOriginKind {
    Read { field: FieldKind },
    VirtualSetup,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceRoundUse {
    pub desc: u16,
    pub round: u8,
    pub structural_occurrences: u32,
    pub origin: SourceOriginKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StaticMaterialization {
    pub bindings: BTreeMap<(u16, u8), SourceRoundBinding>,
    pub all_ext_from: Option<u8>,
    pub fixed_writes: SourceCost,
}

impl StaticMaterialization {
    pub fn binding(&self, desc: u16, round: u8) -> Option<SourceRoundBinding> {
        self.bindings.get(&(desc, round)).copied()
    }
}

pub fn build_static_materialization(
    uses: &[SourceRoundUse],
    rounds: &[RoundProfile],
) -> Result<StaticMaterialization, BackwardSearchError> {
    validate_rounds(rounds)?;
    let by_desc = index_uses(uses, rounds)?;

    let mut bindings = BTreeMap::new();
    let mut previous_store = BTreeMap::<u16, bool>::new();
    let mut all_ext_from = None;
    let mut fixed_writes = SourceCost::default();

    for profile in rounds {
        let accessed = by_desc
            .iter()
            .filter_map(|(&desc, source_uses)| {
                source_uses
                    .get(&profile.round)
                    .copied()
                    .map(|source_use| (desc, source_use))
            })
            .collect::<Vec<_>>();
        let read_accesses = accessed
            .iter()
            .filter(|(_, source_use)| matches!(source_use.origin, SourceOriginKind::Read { .. }))
            .collect::<Vec<_>>();
        let all_reads_are_ext = !read_accesses.is_empty()
            && read_accesses.iter().all(|(desc, source_use)| {
                matches!(
                    source_use.origin,
                    SourceOriginKind::Read {
                        field: FieldKind::Ext
                    }
                ) || previous_store.get(desc).copied().unwrap_or(false)
            });
        if all_ext_from.is_none() && all_reads_are_ext {
            all_ext_from = Some(profile.round);
        }

        let forced_suffix = all_ext_from.is_some();
        let mut next_store = BTreeMap::<u16, bool>::new();
        for (desc, source_use) in accessed {
            let was_stored = previous_store.get(&desc).copied().unwrap_or(false);
            let state = if was_stored {
                FoldState::Materialized
            } else {
                FoldState::LazyFromOriginals {
                    depth: profile.round,
                }
            };
            let store = match source_use.origin {
                SourceOriginKind::VirtualSetup => false,
                SourceOriginKind::Read { .. } if forced_suffix => true,
                SourceOriginKind::Read { .. } => should_store_early(
                    desc,
                    profile.round,
                    source_use,
                    by_desc.get(&desc).expect("descriptor was inserted"),
                    rounds,
                )?,
            };
            bindings.insert(
                (desc, profile.round),
                SourceRoundBinding {
                    state,
                    store_for_next_round: store,
                },
            );
            next_store.insert(desc, store);
            if store {
                fixed_writes.materialization_write_bytes = fixed_writes
                    .materialization_write_bytes
                    .checked_add((profile.rows as u128) * (EXT_BYTES as u128))
                    .ok_or(BackwardSearchError::CostOverflow)?;
            }
        }
        previous_store = next_store;
    }

    Ok(StaticMaterialization {
        bindings,
        all_ext_from,
        fixed_writes,
    })
}

pub fn miss_cost(
    uses: &[SourceRoundUse],
    rounds: &[RoundProfile],
    policy: &StaticMaterialization,
) -> Result<SourceCost, BackwardSearchError> {
    validate_rounds(rounds)?;
    let by_desc = index_uses(uses, rounds)?;
    let rows = round_rows(rounds);
    let mut total = policy.fixed_writes;

    for (&desc, source_uses) in &by_desc {
        for (&round, &source_use) in source_uses {
            let binding = policy
                .binding(desc, round)
                .ok_or(BackwardSearchError::MissingSourceRound { desc, round })?;
            let row_count = *rows
                .get(&round)
                .ok_or(BackwardSearchError::MissingSourceRound { desc, round })?;
            if source_use.origin == SourceOriginKind::VirtualSetup {
                if binding.state == FoldState::Materialized || binding.store_for_next_round {
                    return Err(BackwardSearchError::VirtualSetupMaterialized { desc, round });
                }
                continue;
            }
            total = total.checked_add(read_cost(source_use, row_count, binding.state)?)?;
        }
    }

    Ok(total)
}

fn validate_rounds(rounds: &[RoundProfile]) -> Result<(), BackwardSearchError> {
    for profiles in rounds.windows(2) {
        if profiles[0].round.checked_add(1) != Some(profiles[1].round) {
            return Err(BackwardSearchError::MalformedRoundSequence);
        }
    }
    Ok(())
}

fn index_uses(
    uses: &[SourceRoundUse],
    rounds: &[RoundProfile],
) -> Result<BTreeMap<u16, BTreeMap<u8, SourceRoundUse>>, BackwardSearchError> {
    let known_rounds = round_rows(rounds);
    let mut by_desc = BTreeMap::<u16, BTreeMap<u8, SourceRoundUse>>::new();
    for &source_use in uses {
        if !known_rounds.contains_key(&source_use.round) {
            return Err(BackwardSearchError::MissingSourceRound {
                desc: source_use.desc,
                round: source_use.round,
            });
        }
        if by_desc
            .entry(source_use.desc)
            .or_default()
            .insert(source_use.round, source_use)
            .is_some()
        {
            return Err(BackwardSearchError::DuplicateSourceRound {
                desc: source_use.desc,
                round: source_use.round,
            });
        }
    }
    Ok(by_desc)
}

fn round_rows(rounds: &[RoundProfile]) -> BTreeMap<u8, u64> {
    rounds
        .iter()
        .map(|profile| (profile.round, profile.rows))
        .collect()
}

fn should_store_early(
    desc: u16,
    round: u8,
    _source_use: SourceRoundUse,
    uses: &BTreeMap<u8, SourceRoundUse>,
    rounds: &[RoundProfile],
) -> Result<bool, BackwardSearchError> {
    let Some(next_round) = round.checked_add(1) else {
        return Ok(false);
    };
    let Some(next_use) = uses.get(&next_round).copied() else {
        return Ok(false);
    };
    let Some(next_profile) = rounds.iter().find(|profile| profile.round == next_round) else {
        return Ok(false);
    };
    let current_profile = rounds
        .iter()
        .find(|profile| profile.round == round)
        .ok_or(BackwardSearchError::MissingSourceRound { desc, round })?;
    let write = SourceCost {
        materialization_write_bytes: (current_profile.rows as u128)
            .checked_mul(EXT_BYTES as u128)
            .ok_or(BackwardSearchError::CostOverflow)?,
        ..SourceCost::default()
    };
    let stored = write.checked_add(read_cost(
        next_use,
        next_profile.rows,
        FoldState::Materialized,
    )?)?;
    let lazy = read_cost(
        next_use,
        next_profile.rows,
        FoldState::LazyFromOriginals { depth: next_round },
    )?;
    Ok(cost_key(stored)? < cost_key(lazy)?)
}

fn cost_key(cost: SourceCost) -> Result<(u128, u128), BackwardSearchError> {
    Ok((cost.dram_bytes()?, cost.ops.primitive_equivalents()?))
}

fn read_cost(
    source_use: SourceRoundUse,
    rows: u64,
    state: FoldState,
) -> Result<SourceCost, BackwardSearchError> {
    let SourceOriginKind::Read { field } = source_use.origin else {
        return Ok(SourceCost::default());
    };
    let occurrences = source_use.structural_occurrences as u128;
    let rows = rows as u128;
    let role_elements = occurrences
        .checked_mul(rows)
        .and_then(|count| count.checked_mul(3))
        .ok_or(BackwardSearchError::CostOverflow)?;
    let t2_occurrences = occurrences
        .checked_mul(rows)
        .ok_or(BackwardSearchError::CostOverflow)?;
    let mut cost = SourceCost::default();

    match state {
        FoldState::Materialized => {
            cost.materialized_read_bytes = role_elements
                .checked_mul(EXT_BYTES as u128)
                .ok_or(BackwardSearchError::CostOverflow)?;
        }
        FoldState::LazyFromOriginals { depth } => {
            let origin_width_cells = match field {
                FieldKind::Base => 1u128,
                FieldKind::Ext => (EXT_BYTES / CELL_BYTES) as u128,
            };
            let leaves = 1u128
                .checked_shl(depth as u32)
                .ok_or(BackwardSearchError::CostOverflow)?;
            cost.lazy_read_bytes = role_elements
                .checked_mul(origin_width_cells)
                .and_then(|bytes| bytes.checked_mul(CELL_BYTES as u128))
                .and_then(|bytes| bytes.checked_mul(leaves))
                .ok_or(BackwardSearchError::CostOverflow)?;
            cost.ops = fold_element_ops(field, depth)?.checked_scale(role_elements)?;
        }
    }
    cost.ops.ext_add = cost
        .ops
        .ext_add
        .checked_add(
            t2_occurrences
                .checked_mul(2)
                .ok_or(BackwardSearchError::CostOverflow)?,
        )
        .ok_or(BackwardSearchError::CostOverflow)?;
    Ok(cost)
}

fn fold_element_ops(origin: FieldKind, depth: u8) -> Result<SourceOpCost, BackwardSearchError> {
    let mut out = SourceOpCost::default();
    for level in 0..depth {
        let nodes = 1u128
            .checked_shl((depth - level - 1) as u32)
            .ok_or(BackwardSearchError::CostOverflow)?;
        if level == 0 && origin == FieldKind::Base {
            out.bf_add = out
                .bf_add
                .checked_add(nodes)
                .ok_or(BackwardSearchError::CostOverflow)?;
            out.mixed_mul = out
                .mixed_mul
                .checked_add(nodes)
                .ok_or(BackwardSearchError::CostOverflow)?;
            out.ext_add = out
                .ext_add
                .checked_add(nodes)
                .ok_or(BackwardSearchError::CostOverflow)?;
        } else {
            out.ext_add = out
                .ext_add
                .checked_add(
                    nodes
                        .checked_mul(2)
                        .ok_or(BackwardSearchError::CostOverflow)?,
                )
                .ok_or(BackwardSearchError::CostOverflow)?;
            out.ext_mul = out
                .ext_mul
                .checked_add(nodes)
                .ok_or(BackwardSearchError::CostOverflow)?;
        }
    }
    Ok(out)
}

fn lazy_fold_cost(
    origin_width_cells: usize,
    depth: u8,
    rows: u64,
) -> Result<SourceCost, BackwardSearchError> {
    let field = match origin_width_cells {
        1 => FieldKind::Base,
        width if width == EXT_BYTES / CELL_BYTES => FieldKind::Ext,
        _ => return Err(BackwardSearchError::CostOverflow),
    };
    read_cost(
        SourceRoundUse {
            desc: 0,
            round: depth,
            structural_occurrences: 1,
            origin: SourceOriginKind::Read { field },
        },
        rows,
        FoldState::LazyFromOriginals { depth },
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn round(round: u8, rows: u64) -> RoundProfile {
        RoundProfile { round, rows }
    }

    fn synthetic_base_uses(rounds: &[(u8, u32)]) -> Vec<SourceRoundUse> {
        rounds
            .iter()
            .map(|&(round, structural_occurrences)| SourceRoundUse {
                desc: 0,
                round,
                structural_occurrences,
                origin: SourceOriginKind::Read {
                    field: FieldKind::Base,
                },
            })
            .collect()
    }

    fn synthetic_ext_and_vs_uses(rounds: &[(u8, u32)]) -> Vec<SourceRoundUse> {
        rounds
            .iter()
            .flat_map(|&(round, structural_occurrences)| {
                [
                    SourceRoundUse {
                        desc: 0,
                        round,
                        structural_occurrences,
                        origin: SourceOriginKind::Read {
                            field: FieldKind::Ext,
                        },
                    },
                    SourceRoundUse {
                        desc: 1,
                        round,
                        structural_occurrences,
                        origin: SourceOriginKind::VirtualSetup,
                    },
                ]
            })
            .collect()
    }

    #[test]
    fn early_store_wins_only_on_strict_lexicographic_cost() {
        let uses = synthetic_base_uses(&[(2, 1), (3, 8)]);
        let policy = build_static_materialization(&uses, &[round(2, 16), round(3, 8)])
            .expect("valid materialization census");
        assert!(policy.binding(0, 2).unwrap().store_for_next_round);

        let tied = synthetic_base_uses(&[(1, 1), (2, 1)]);
        let policy = build_static_materialization(&tied, &[round(1, 4), round(2, 1)])
            .expect("valid materialization census");
        assert!(!policy.binding(0, 1).unwrap().store_for_next_round);
    }

    #[test]
    fn missing_next_round_use_defers_and_gap_breaks_materialized_chain() {
        let uses = synthetic_base_uses(&[(0, 2), (2, 2)]);
        let policy =
            build_static_materialization(&uses, &[round(0, 64), round(1, 32), round(2, 16)])
                .expect("valid materialization census");
        assert!(!policy.binding(0, 0).unwrap().store_for_next_round);
        assert_eq!(
            policy.binding(0, 2).unwrap().state,
            FoldState::LazyFromOriginals { depth: 2 }
        );
    }

    #[test]
    fn all_ext_suffix_is_sticky_but_virtual_setup_never_stores() {
        let uses = synthetic_ext_and_vs_uses(&[(0, 1), (1, 1), (3, 1)]);
        let policy = build_static_materialization(
            &uses,
            &[round(0, 64), round(1, 32), round(2, 16), round(3, 8)],
        )
        .expect("valid materialization census");
        assert_eq!(policy.all_ext_from, Some(0));
        assert!(policy.binding(0, 0).unwrap().store_for_next_round);
        assert_eq!(
            policy.binding(0, 3).unwrap().state,
            FoldState::LazyFromOriginals { depth: 3 }
        );
        assert!(policy.binding(0, 3).unwrap().store_for_next_round);
        assert!(!policy.binding(1, 3).unwrap().store_for_next_round);
    }

    #[test]
    fn fold_cost_counts_base_mixed_ext_and_role_combine_operations() {
        let cost = lazy_fold_cost(1, 1, 10).expect("cost fits");
        assert_eq!(cost.ops.bf_add, 30);
        assert_eq!(cost.ops.mixed_mul, 30);
        assert_eq!(cost.ops.ext_add, 50);
        assert_eq!(cost.ops.ext_mul, 0);
        assert_eq!(cost.lazy_read_bytes, 240);
    }
}
