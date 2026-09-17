//! Pointer-free lowering for dimension-reducing width-3 R0 programs.

use std::collections::{BTreeMap, BTreeSet};

use cs::definitions::{GKRAddress, OutputType};

const DR_WINDOW_INPUTS_PER_SLOT: usize = 2;
const DR_WINDOW_BATCH_EXPONENTS_PER_SLOT: usize = 2;

/// One enabled semantic slot in a dimension-reducing width-3 R0 program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DrWindowSlotPlan {
    slot: u8,
    source_ids: [u16; DR_WINDOW_INPUTS_PER_SLOT],
    batch_exponents: [u16; DR_WINDOW_BATCH_EXPONENTS_PER_SLOT],
}

impl DrWindowSlotPlan {
    pub const fn slot(&self) -> usize {
        self.slot as usize
    }

    /// Source ids in input order.
    pub const fn source_ids(&self) -> &[u16; DR_WINDOW_INPUTS_PER_SLOT] {
        &self.source_ids
    }

    pub const fn batch_exponents(&self) -> &[u16; DR_WINDOW_BATCH_EXPONENTS_PER_SLOT] {
        &self.batch_exponents
    }
}

/// One input occurrence and its canonical continuation publication.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DrWindowInputOccurrence {
    dense_slot: u16,
    input_operand: u8,
    publication_index: u16,
}

impl DrWindowInputOccurrence {
    pub const fn dense_slot(&self) -> usize {
        self.dense_slot as usize
    }

    pub const fn input_operand(&self) -> usize {
        self.input_operand as usize
    }

    pub const fn publication_index(&self) -> u16 {
        self.publication_index
    }
}

/// The input-only canonical publication view consumed by DR continuations.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DrWindowInputProjection {
    canonical_sources: Vec<GKRAddress>,
    occurrences: Vec<DrWindowInputOccurrence>,
}

impl DrWindowInputProjection {
    pub fn canonical_sources(&self) -> &[GKRAddress] {
        &self.canonical_sources
    }

    pub fn occurrences(&self) -> &[DrWindowInputOccurrence] {
        &self.occurrences
    }

    pub fn publication_index(&self, dense_slot: usize, input_operand: usize) -> Option<u16> {
        self.occurrences
            .iter()
            .find(|occurrence| {
                occurrence.dense_slot() == dense_slot && occurrence.input_operand() == input_operand
            })
            .map(DrWindowInputOccurrence::publication_index)
    }
}

/// Admit a projection for independently scheduled slot blocks.
/// Generic projection still permits cross-slot aliases; split publication does not.
pub fn validate_dr_window_split_ownership(
    projection: &DrWindowInputProjection,
) -> Result<(), DrWindowLoweringError> {
    let mut owners = BTreeMap::new();
    for occurrence in projection.occurrences() {
        let slot = occurrence.dense_slot();
        let publication_index = occurrence.publication_index();
        if let Some(first_slot) = owners.insert(publication_index, slot) {
            if first_slot != slot {
                return Err(DrWindowLoweringError::CrossSlotPublicationAlias {
                    publication_index,
                    first_slot,
                    second_slot: slot,
                });
            }
        }
    }
    Ok(())
}

/// A pointer-free dimension-reducing width-3 R0 program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DrWindowProgram {
    enabled_mask: u32,
    slots: Vec<DrWindowSlotPlan>,
    sources: Vec<GKRAddress>,
}

impl DrWindowProgram {
    pub const fn enabled_mask(&self) -> u32 {
        self.enabled_mask
    }

    pub fn slots(&self) -> &[DrWindowSlotPlan] {
        &self.slots
    }

    pub fn sources(&self) -> &[GKRAddress] {
        &self.sources
    }

    pub fn slot_count(&self) -> usize {
        self.slots.len()
    }

    pub fn source_count(&self) -> usize {
        self.sources.len()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DrWindowLoweringError {
    CrossSlotPublicationAlias {
        publication_index: u16,
        first_slot: usize,
        second_slot: usize,
    },
    ZeroMask,
}

impl core::fmt::Display for DrWindowLoweringError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for DrWindowLoweringError {}

pub fn lower_dr_window_program(
    rows: &BTreeMap<OutputType, [GKRAddress; DR_WINDOW_INPUTS_PER_SLOT]>,
) -> Result<DrWindowProgram, DrWindowLoweringError> {
    if rows.is_empty() {
        return Err(DrWindowLoweringError::ZeroMask);
    }

    let mut enabled_mask = 0u32;
    let mut slots = Vec::with_capacity(rows.len());
    let mut sources = Vec::with_capacity(rows.len() * DR_WINDOW_INPUTS_PER_SLOT);
    let mut source_ids = BTreeMap::<GKRAddress, u16>::new();

    for (output_type, inputs) in rows {
        let slot = output_type_slot(*output_type);
        enabled_mask |= 1 << slot;

        let dense_slot = slots.len();
        let mut operand_source_ids = [0u16; DR_WINDOW_INPUTS_PER_SLOT];

        for (operand, address) in inputs.iter().copied().enumerate() {
            let next_id = sources.len() as u16;
            operand_source_ids[operand] = *source_ids.entry(address).or_insert_with(|| {
                sources.push(address);
                next_id
            });
        }

        // Five output types have two inputs and two batch exponents each.
        let batch_base = (dense_slot * DR_WINDOW_BATCH_EXPONENTS_PER_SLOT) as u16;
        slots.push(DrWindowSlotPlan {
            slot: slot as u8,
            source_ids: operand_source_ids,
            batch_exponents: [batch_base, batch_base + 1],
        });
    }

    Ok(DrWindowProgram {
        enabled_mask,
        slots,
        sources,
    })
}

pub fn project_dr_window_inputs(
    program: &DrWindowProgram,
    aliases: &BTreeMap<GKRAddress, GKRAddress>,
) -> DrWindowInputProjection {
    let input_occurrences =
        program
            .slots
            .iter()
            .enumerate()
            .flat_map(|(dense_slot, slot)| {
                slot.source_ids.iter().copied().enumerate().map(
                    move |(input_operand, source_id)| {
                        let source = program.sources[usize::from(source_id)];
                        let canonical_source = aliases.get(&source).copied().unwrap_or(source);
                        (dense_slot, input_operand, canonical_source)
                    },
                )
            });
    let canonical_sources = input_occurrences
        .clone()
        .map(|(_, _, source)| source)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let publication_indices = canonical_sources
        .iter()
        .copied()
        .enumerate()
        .map(|(index, source)| {
            (
                source,
                u16::try_from(index).expect("validated DR source count fits u16"),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let occurrences = input_occurrences
        .map(
            |(dense_slot, input_operand, canonical_source)| DrWindowInputOccurrence {
                dense_slot: u16::try_from(dense_slot)
                    .expect("validated DR dense slot count fits u16"),
                input_operand: input_operand as u8,
                publication_index: publication_indices[&canonical_source],
            },
        )
        .collect();

    DrWindowInputProjection {
        canonical_sources,
        occurrences,
    }
}

fn output_type_slot(output_type: OutputType) -> usize {
    match output_type {
        OutputType::PermutationProduct => 0,
        OutputType::Lookup16Bits => 1,
        OutputType::LookupTimestamps => 2,
        OutputType::GenericLookup => 3,
        OutputType::InitsAndTeardownsProduct => 4,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const OUTPUT_TYPES: [OutputType; 5] = [
        OutputType::PermutationProduct,
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
        OutputType::InitsAndTeardownsProduct,
    ];

    fn address(offset: usize) -> GKRAddress {
        GKRAddress::InnerLayer { layer: 1, offset }
    }

    fn rows_for_mask(mask: u32) -> BTreeMap<OutputType, [GKRAddress; DR_WINDOW_INPUTS_PER_SLOT]> {
        OUTPUT_TYPES
            .into_iter()
            .enumerate()
            .filter(|(slot, _)| mask & (1 << slot) != 0)
            .map(|(slot, output_type)| {
                let base = slot * DR_WINDOW_INPUTS_PER_SLOT;
                (output_type, [address(base), address(base + 1)])
            })
            .collect()
    }

    #[test]
    fn all_masks_preserve_operands_and_dense_batch_exponents() {
        for mask in 1..=0x1f {
            let rows = rows_for_mask(mask);
            let program = lower_dr_window_program(&rows).unwrap();

            assert_eq!(program.enabled_mask(), mask);
            assert_eq!(program.slot_count(), mask.count_ones() as usize);
            assert_eq!(program.source_count(), program.slot_count() * 2);

            for (dense_slot, slot) in program.slots().iter().enumerate() {
                let output_type = OUTPUT_TYPES[slot.slot()];
                let row = rows[&output_type];
                let observed_operands = slot
                    .source_ids()
                    .iter()
                    .map(|source_id| program.sources()[usize::from(*source_id)])
                    .collect::<Vec<_>>();
                assert_eq!(observed_operands, row);
                assert_eq!(
                    slot.batch_exponents(),
                    &[2 * dense_slot as u16, 2 * dense_slot as u16 + 1]
                );
            }
        }
    }

    #[test]
    fn lowers_dense_slots_in_protocol_order() {
        let rows = BTreeMap::from([
            (OutputType::PermutationProduct, [address(4), address(2)]),
            (OutputType::GenericLookup, [address(10), address(11)]),
        ]);

        let program = lower_dr_window_program(&rows).unwrap();
        assert_eq!(program.enabled_mask(), 0b0_1001);
        assert_eq!(
            program
                .slots()
                .iter()
                .map(DrWindowSlotPlan::slot)
                .collect::<Vec<_>>(),
            [0, 3]
        );
        assert_eq!(program.slots()[0].source_ids(), &[0, 1]);
        assert_eq!(program.slots()[1].batch_exponents(), &[2, 3]);
    }

    #[test]
    fn rejects_zero_mask() {
        assert_eq!(
            lower_dr_window_program(&BTreeMap::new()),
            Err(DrWindowLoweringError::ZeroMask)
        );
    }

    #[test]
    fn input_projection_is_sorted_aliased_and_deduplicated() {
        let rows = BTreeMap::from([
            (OutputType::PermutationProduct, [address(9), address(3)]),
            (OutputType::LookupTimestamps, [address(9), address(7)]),
        ]);
        let program = lower_dr_window_program(&rows).unwrap();
        let aliases = BTreeMap::from([(address(9), address(5)), (address(7), address(3))]);

        let projection = project_dr_window_inputs(&program, &aliases);

        assert_eq!(projection.canonical_sources(), &[address(3), address(5)]);
    }

    #[test]
    fn input_projection_maps_every_dense_input_occurrence() {
        let rows = BTreeMap::from([
            (OutputType::PermutationProduct, [address(9), address(3)]),
            (OutputType::LookupTimestamps, [address(9), address(7)]),
        ]);
        let program = lower_dr_window_program(&rows).unwrap();
        let aliases = BTreeMap::from([(address(9), address(5)), (address(7), address(3))]);

        let projection = project_dr_window_inputs(&program, &aliases);

        assert_eq!(projection.occurrences().len(), program.slot_count() * 2);
        assert_eq!(projection.publication_index(0, 0), Some(1));
        assert_eq!(projection.publication_index(0, 1), Some(0));
        assert_eq!(projection.publication_index(1, 0), Some(1));
        assert_eq!(projection.publication_index(1, 1), Some(0));
        assert_eq!(projection.publication_index(0, 2), None);
        assert_eq!(projection.publication_index(2, 0), None);
    }

    #[test]
    fn split_ownership_accepts_same_slot_aliases() {
        let rows = BTreeMap::from([
            (OutputType::PermutationProduct, [address(9), address(7)]),
            (OutputType::LookupTimestamps, [address(3), address(4)]),
        ]);
        let program = lower_dr_window_program(&rows).unwrap();
        let projection =
            project_dr_window_inputs(&program, &BTreeMap::from([(address(7), address(9))]));
        assert_eq!(projection.canonical_sources().len(), 3);
        assert_eq!(validate_dr_window_split_ownership(&projection), Ok(()));
    }

    #[test]
    fn split_ownership_rejects_cross_slot_aliases() {
        let rows = BTreeMap::from([
            (OutputType::PermutationProduct, [address(9), address(3)]),
            (OutputType::LookupTimestamps, [address(7), address(4)]),
        ]);
        let program = lower_dr_window_program(&rows).unwrap();
        let projection =
            project_dr_window_inputs(&program, &BTreeMap::from([(address(7), address(9))]));
        assert_eq!(
            validate_dr_window_split_ownership(&projection),
            Err(DrWindowLoweringError::CrossSlotPublicationAlias {
                publication_index: projection.publication_index(0, 0).unwrap(),
                first_slot: 0,
                second_slot: 1,
            })
        );
    }

    #[test]
    fn split_ownership_accepts_distinct_inputs_for_every_mask() {
        for mask in 1..=0x1f {
            let program = lower_dr_window_program(&rows_for_mask(mask)).unwrap();
            let projection = project_dr_window_inputs(&program, &BTreeMap::new());
            assert_eq!(validate_dr_window_split_ownership(&projection), Ok(()));
        }
    }
}
