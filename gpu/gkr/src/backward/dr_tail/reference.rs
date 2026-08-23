use gpu_core::primitives::field::{BF, E4};

use crate::upstream::{
    commit_field_els, draw_random_field_els, evaluate_eq_poly, evaluate_small_univariate_poly,
    output_univariate_monomial_form_max_quadratic, Blake2sTranscript, Field, Seed,
};

use super::super::kernels::{make_eq_sizes, GKR_EQ_GROUP_TABLE_LEN};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DrTailSlotKind {
    Pairwise,
    Lookup,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct DrTailReferenceSlot {
    pub(super) kind: DrTailSlotKind,
    pub(super) source_indices: [usize; 2],
    pub(super) batch_weights: [E4; 2],
}

#[derive(Clone, Debug)]
pub(super) struct DrTailReferenceInput {
    pub(super) folding_steps: usize,
    pub(super) entry_round: usize,
    pub(super) canonical_sources: Vec<Vec<E4>>,
    pub(super) slots: [Option<DrTailReferenceSlot>; 5],
    pub(super) entry_challenges: [E4; 3],
    pub(super) tau: Vec<E4>,
    pub(super) seed: Seed,
    pub(super) initial_claim: E4,
    pub(super) initial_eq_prefactor: E4,
    pub(super) raw_address_canonical_lookup: Vec<usize>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum DrTailMutation {
    #[default]
    None,
    ReverseEntryChallengeOrder,
    GateMajorInsteadOfTwoYPlusB,
    FlipFirstSlotKind,
    SkipFirstSlot,
    FoldEqAfterFinalRound,
    ReverseCanonicalPublication,
    DirectCanonicalEpilogue,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct DrTailEqSnapshot {
    pub(super) sizes: [u32; 3],
    pub(super) group_tables: Vec<Vec<E4>>,
    pub(super) per_row_values: Vec<E4>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct DrTailRoundTransition {
    pub(super) absolute_round: usize,
    pub(super) coefficients: [E4; 4],
    pub(super) challenge: E4,
    pub(super) claim: E4,
    pub(super) eq_prefactor: E4,
    pub(super) eq_before: DrTailEqSnapshot,
    pub(super) eq_after: Option<DrTailEqSnapshot>,
    pub(super) source_level_after: Vec<Vec<E4>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct DrTailReferenceOutput {
    pub(super) seed: Seed,
    pub(super) initial_normalized_claim: E4,
    pub(super) entry_source_levels: Vec<Vec<Vec<E4>>>,
    pub(super) rounds: Vec<DrTailRoundTransition>,
    pub(super) final_canonical_cells: Vec<[E4; 4]>,
    pub(super) epilogue_raw_cells: Vec<[E4; 2]>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DrTailReferenceError {
    InvalidBoundary,
    InvalidTauLength,
    InvalidSourceCount,
    InvalidSourceLength,
    InvalidSlotSource,
    InvalidRawLookup,
    NonInvertibleEqPrefactor,
    FinalEqFoldAfterDrain,
}

#[derive(Clone, Debug)]
struct FactoredEq {
    sizes: super::super::kernels::GkrEqSizes,
    groups: Vec<Vec<E4>>,
}

impl FactoredEq {
    fn build(challenges: &[E4]) -> Self {
        let sizes = make_eq_sizes(challenges.len());
        let group_count = challenges.len().div_ceil(8);
        let mut groups = Vec::with_capacity(group_count);
        for group_idx in 0..group_count {
            let group_start = group_idx * 8;
            let group_size = (challenges.len() - group_start).min(8);
            let mut table = Vec::with_capacity(1 << group_size);
            for local_index in 0..1usize << group_size {
                let mut value = E4::ONE;
                for local_variable in 0..group_size {
                    let variable_idx = group_start + local_variable;
                    let challenge = challenges[challenges.len() - 1 - variable_idx];
                    let bit = (local_index >> (group_size - 1 - local_variable)) & 1;
                    value.mul_assign(&eq_bit(bit, challenge));
                }
                table.push(value);
            }
            groups.push(table);
        }
        Self { sizes, groups }
    }

    fn snapshot(&self) -> DrTailEqSnapshot {
        DrTailEqSnapshot {
            sizes: [self.sizes.high[0], self.sizes.high[1], self.sizes.low],
            group_tables: self.groups.clone(),
            per_row_values: self.dense_values(),
        }
    }

    fn dense_values(&self) -> Vec<E4> {
        let slot_sizes = [self.sizes.high[0], self.sizes.high[1], self.sizes.low];
        let active_sizes: Vec<usize> = slot_sizes
            .into_iter()
            .filter(|size| *size != 0)
            .map(|size| size as usize)
            .collect();
        let total_bits: usize = active_sizes.iter().sum();
        if total_bits == 0 {
            return vec![E4::ONE];
        }
        let mut dense = Vec::with_capacity(1 << total_bits);
        for row in 0..1usize << total_bits {
            let mut value = E4::ONE;
            let mut consumed = 0;
            for (group, group_size) in self.groups.iter().zip(active_sizes.iter().copied()) {
                let shift = total_bits - consumed - group_size;
                let local = (row >> shift) & ((1 << group_size) - 1);
                value.mul_assign(&group[local]);
                consumed += group_size;
            }
            dense.push(value);
        }
        dense
    }

    fn fold_active(&mut self) -> Result<(), DrTailReferenceError> {
        let active_group = if self.sizes.low > 0 {
            self.groups.len().checked_sub(1)
        } else if self.sizes.high[1] > 0 {
            Some(1)
        } else if self.sizes.high[0] > 0 {
            Some(0)
        } else {
            None
        }
        .ok_or(DrTailReferenceError::FinalEqFoldAfterDrain)?;
        let table = &mut self.groups[active_group];
        let next_len = table.len() / 2;
        for index in 0..next_len {
            let mut value = table[2 * index];
            value.add_assign(&table[2 * index + 1]);
            table[index] = value;
        }
        table.truncate(next_len);
        if self.sizes.low > 0 {
            self.sizes.low -= 1;
        } else if self.sizes.high[1] > 0 {
            self.sizes.high[1] -= 1;
        } else {
            self.sizes.high[0] -= 1;
        }
        Ok(())
    }
}

fn eq_bit(bit: usize, challenge: E4) -> E4 {
    if bit == 0 {
        let mut result = E4::ONE;
        result.sub_assign(&challenge);
        result
    } else {
        challenge
    }
}

fn eq_row(point: &[E4], row: usize) -> E4 {
    point
        .iter()
        .enumerate()
        .fold(E4::ONE, |mut value, (bit, challenge)| {
            value.mul_assign(&eq_bit((row >> bit) & 1, *challenge));
            value
        })
}

fn source_index(source_len: usize, y: usize, b: usize, mutation: DrTailMutation) -> usize {
    if mutation == DrTailMutation::GateMajorInsteadOfTwoYPlusB {
        b * (source_len / 2) + y
    } else {
        2 * y + b
    }
}

fn slot_kind(
    slot: DrTailReferenceSlot,
    enabled_slot_idx: usize,
    mutation: DrTailMutation,
) -> DrTailSlotKind {
    if mutation == DrTailMutation::FlipFirstSlotKind && enabled_slot_idx == 0 {
        match slot.kind {
            DrTailSlotKind::Pairwise => DrTailSlotKind::Lookup,
            DrTailSlotKind::Lookup => DrTailSlotKind::Pairwise,
        }
    } else {
        slot.kind
    }
}

fn gate_batch(
    sources: &[Vec<E4>],
    slots: &[Option<DrTailReferenceSlot>; 5],
    y0: usize,
    y1: Option<usize>,
    mutation: DrTailMutation,
) -> E4 {
    let mut total = E4::ZERO;
    for (slot_idx, slot) in slots.iter().flatten().enumerate() {
        if mutation == DrTailMutation::SkipFirstSlot && slot_idx == 0 {
            continue;
        }
        let at = |source: usize, b: usize| {
            let lo = sources[source][source_index(sources[source].len(), y0, b, mutation)];
            if let Some(y1) = y1 {
                let hi = sources[source][source_index(sources[source].len(), y1, b, mutation)];
                let mut difference = hi;
                difference.sub_assign(&lo);
                difference
            } else {
                lo
            }
        };
        match slot_kind(*slot, slot_idx, mutation) {
            DrTailSlotKind::Pairwise => {
                for (source, weight) in slot.source_indices.iter().zip(slot.batch_weights) {
                    let mut value = at(*source, 0);
                    value.mul_assign(&at(*source, 1));
                    value.mul_assign(&weight);
                    total.add_assign(&value);
                }
            }
            DrTailSlotKind::Lookup => {
                let [num, den] = slot.source_indices;
                let (n0, n1) = (at(num, 0), at(num, 1));
                let (d0, d1) = (at(den, 0), at(den, 1));
                let mut numerator = n0;
                numerator.mul_assign(&d1);
                let mut cross = n1;
                cross.mul_assign(&d0);
                numerator.add_assign(&cross);
                numerator.mul_assign(&slot.batch_weights[0]);
                total.add_assign(&numerator);
                let mut denominator = d0;
                denominator.mul_assign(&d1);
                denominator.mul_assign(&slot.batch_weights[1]);
                total.add_assign(&denominator);
            }
        }
    }
    total
}

fn fold_source(source: &[E4], challenge: E4) -> Vec<E4> {
    let destination_rows = source.len() / 4;
    let mut destination = vec![E4::ZERO; source.len() / 2];
    for y in 0..destination_rows {
        for b in 0..2 {
            let lo = source[4 * y + b];
            let mut value = source[4 * y + 2 + b];
            value.sub_assign(&lo);
            value.mul_assign(&challenge);
            value.add_assign(&lo);
            destination[2 * y + b] = value;
        }
    }
    destination
}

fn fold_sources(sources: &[Vec<E4>], challenge: E4) -> Vec<Vec<E4>> {
    sources
        .iter()
        .map(|source| fold_source(source, challenge))
        .collect()
}

pub(super) fn run_reference(
    input: &DrTailReferenceInput,
    mutation: DrTailMutation,
) -> Result<DrTailReferenceOutput, DrTailReferenceError> {
    if input.entry_round < 3
        || input.entry_round % 3 != 0
        || input.entry_round >= input.folding_steps
    {
        return Err(DrTailReferenceError::InvalidBoundary);
    }
    if input.tau.len() != input.folding_steps {
        return Err(DrTailReferenceError::InvalidTauLength);
    }
    if input.canonical_sources.is_empty() || input.canonical_sources.len() > 10 {
        return Err(DrTailReferenceError::InvalidSourceCount);
    }
    for slot in input.slots.iter().flatten() {
        if slot
            .source_indices
            .iter()
            .any(|source| *source >= input.canonical_sources.len())
        {
            return Err(DrTailReferenceError::InvalidSlotSource);
        }
    }
    if input
        .raw_address_canonical_lookup
        .iter()
        .any(|source| *source >= input.canonical_sources.len())
    {
        return Err(DrTailReferenceError::InvalidRawLookup);
    }

    let remaining_rounds = input.folding_steps - input.entry_round;
    let pre_entry_len = 1usize
        .checked_shl((remaining_rounds + 4) as u32)
        .ok_or(DrTailReferenceError::InvalidSourceLength)?;
    if input
        .canonical_sources
        .iter()
        .any(|source| source.len() != pre_entry_len)
    {
        return Err(DrTailReferenceError::InvalidSourceLength);
    }

    let mut sources = input.canonical_sources.clone();
    let mut entry_source_levels = Vec::with_capacity(3);
    let mut entry_challenges = input.entry_challenges;
    if mutation == DrTailMutation::ReverseEntryChallengeOrder {
        entry_challenges.reverse();
    }
    for challenge in entry_challenges {
        sources = fold_sources(&sources, challenge);
        entry_source_levels.push(sources.clone());
    }

    let inverse = input
        .initial_eq_prefactor
        .inverse()
        .ok_or(DrTailReferenceError::NonInvertibleEqPrefactor)?;
    let mut initial_normalized_claim = input.initial_claim;
    initial_normalized_claim.mul_assign(&inverse);
    let mut claim = input.initial_claim;
    let mut eq_prefactor = input.initial_eq_prefactor;
    let mut seed = input.seed;
    let mut factored_eq = FactoredEq::build(&input.tau[input.entry_round + 1..]);
    let mut rounds = Vec::with_capacity(remaining_rounds);

    for round_index in 0..remaining_rounds {
        let absolute_round = input.entry_round + round_index;
        let pairs = 1usize << (remaining_rounds - round_index - 1);
        let eq_before = factored_eq.snapshot();
        if eq_before.per_row_values.len() != pairs {
            return Err(DrTailReferenceError::InvalidSourceLength);
        }
        let mut h0 = E4::ZERO;
        let mut hinf = E4::ZERO;
        for pair in 0..pairs {
            let weight = eq_before.per_row_values[pair];
            let mut at_zero = gate_batch(&sources, &input.slots, 2 * pair, None, mutation);
            at_zero.mul_assign(&weight);
            h0.add_assign(&at_zero);
            let mut at_infinity = gate_batch(
                &sources,
                &input.slots,
                2 * pair,
                Some(2 * pair + 1),
                mutation,
            );
            at_infinity.mul_assign(&weight);
            hinf.add_assign(&at_infinity);
        }
        let inverse = eq_prefactor
            .inverse()
            .ok_or(DrTailReferenceError::NonInvertibleEqPrefactor)?;
        let mut normalized_claim = claim;
        normalized_claim.mul_assign(&inverse);
        let coefficients = output_univariate_monomial_form_max_quadratic::<BF, E4>(
            input.tau[absolute_round],
            normalized_claim,
            h0,
            hinf,
        );
        commit_field_els::<BF, E4, Blake2sTranscript>(&mut seed, &coefficients);
        let challenge = draw_random_field_els::<BF, E4, Blake2sTranscript>(&mut seed, 1)[0];
        claim = evaluate_small_univariate_poly::<BF, E4, 4>(&coefficients, &challenge);
        eq_prefactor = evaluate_eq_poly::<BF, E4>(&challenge, &input.tau[absolute_round]);

        let non_final = round_index + 1 < remaining_rounds;
        let eq_after = if non_final {
            factored_eq.fold_active()?;
            sources = fold_sources(&sources, challenge);
            Some(factored_eq.snapshot())
        } else {
            if mutation == DrTailMutation::FoldEqAfterFinalRound {
                factored_eq.fold_active()?;
            }
            None
        };
        rounds.push(DrTailRoundTransition {
            absolute_round,
            coefficients,
            challenge,
            claim,
            eq_prefactor,
            eq_before,
            eq_after,
            source_level_after: sources.clone(),
        });
    }

    let mut final_canonical_cells: Vec<[E4; 4]> = sources
        .iter()
        .map(|source| {
            source
                .as_slice()
                .try_into()
                .map_err(|_| DrTailReferenceError::InvalidSourceLength)
        })
        .collect::<Result<_, _>>()?;
    if mutation == DrTailMutation::ReverseCanonicalPublication {
        final_canonical_cells.reverse();
    }
    let final_challenge = rounds
        .last()
        .ok_or(DrTailReferenceError::InvalidBoundary)?
        .challenge;
    let raw_lookup: Vec<usize> = if mutation == DrTailMutation::DirectCanonicalEpilogue {
        (0..input.raw_address_canonical_lookup.len()).collect()
    } else {
        input.raw_address_canonical_lookup.clone()
    };
    let epilogue_raw_cells = raw_lookup
        .into_iter()
        .map(|source| {
            let cells = final_canonical_cells
                .get(source)
                .ok_or(DrTailReferenceError::InvalidRawLookup)?;
            Ok([
                fold_pair(cells[0], cells[2], final_challenge),
                fold_pair(cells[1], cells[3], final_challenge),
            ])
        })
        .collect::<Result<_, _>>()?;

    Ok(DrTailReferenceOutput {
        seed,
        initial_normalized_claim,
        entry_source_levels,
        rounds,
        final_canonical_cells,
        epilogue_raw_cells,
    })
}

pub(super) fn set_consistent_initial_claim(input: &mut DrTailReferenceInput) {
    let mut sources = input.canonical_sources.clone();
    for challenge in input.entry_challenges {
        sources = fold_sources(&sources, challenge);
    }
    let remaining_rounds = input.folding_steps - input.entry_round;
    let rows = 1usize << remaining_rounds;
    let mut normalized_claim = E4::ZERO;
    for row in 0..rows {
        let mut term = gate_batch(&sources, &input.slots, row, None, DrTailMutation::None);
        term.mul_assign(&eq_row(&input.tau[input.entry_round..], row));
        normalized_claim.add_assign(&term);
    }
    normalized_claim.mul_assign(&input.initial_eq_prefactor);
    input.initial_claim = normalized_claim;
}

fn fold_pair(lo: E4, hi: E4, challenge: E4) -> E4 {
    let mut value = hi;
    value.sub_assign(&lo);
    value.mul_assign(&challenge);
    value.add_assign(&lo);
    value
}

pub(super) fn synthetic_two_group_eq(challenges: &[E4]) -> Vec<DrTailEqSnapshot> {
    assert!(challenges.len() > 8 && challenges.len() <= 16);
    let mut eq = FactoredEq::build(challenges);
    let mut snapshots = vec![eq.snapshot()];
    while eq.sizes.low > 0 || eq.sizes.high[1] > 0 || eq.sizes.high[0] > 0 {
        eq.fold_active().unwrap();
        snapshots.push(eq.snapshot());
    }
    snapshots
}

const _: () = assert!(GKR_EQ_GROUP_TABLE_LEN == 256);
