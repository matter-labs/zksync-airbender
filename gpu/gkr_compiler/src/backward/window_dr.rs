//! Pointer-free lowering for dimension-reducing width-3 R0 programs.

use std::collections::{BTreeMap, BTreeSet};

use cs::definitions::{GKRAddress, OutputType};

const DR_WINDOW_SLOT_COUNT: usize = 5;
const DR_WINDOW_OPERANDS_PER_SLOT: usize = 4;
const DR_WINDOW_INPUTS_PER_SLOT: usize = 2;
const DR_WINDOW_BATCH_EXPONENTS_PER_SLOT: usize = 2;
const U16_INDEX_CAPACITY: usize = u16::MAX as usize + 1;

/// One compiler-owned, fixed-arity dimension-reducing input/output row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DrWindowInputOutput {
    inputs: [GKRAddress; DR_WINDOW_INPUTS_PER_SLOT],
    outputs: [GKRAddress; DR_WINDOW_INPUTS_PER_SLOT],
}

impl DrWindowInputOutput {
    pub const fn new(inputs: [GKRAddress; 2], outputs: [GKRAddress; 2]) -> Self {
        Self { inputs, outputs }
    }

    pub const fn inputs(&self) -> &[GKRAddress; 2] {
        &self.inputs
    }

    pub const fn outputs(&self) -> &[GKRAddress; 2] {
        &self.outputs
    }
}

/// One enabled semantic slot in a dimension-reducing width-3 R0 program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DrWindowSlotPlan {
    slot: u8,
    source_ids: [u16; DR_WINDOW_OPERANDS_PER_SLOT],
    batch_exponents: [u16; DR_WINDOW_BATCH_EXPONENTS_PER_SLOT],
}

impl DrWindowSlotPlan {
    pub const fn slot(&self) -> usize {
        self.slot as usize
    }

    /// Source ids in input/input/output/output operand order.
    pub const fn source_ids(&self) -> &[u16; DR_WINDOW_OPERANDS_PER_SLOT] {
        &self.source_ids
    }

    pub fn source_id(&self, operand: usize) -> Option<u16> {
        self.source_ids.get(operand).copied()
    }

    pub const fn batch_exponents(&self) -> &[u16; DR_WINDOW_BATCH_EXPONENTS_PER_SLOT] {
        &self.batch_exponents
    }
}

/// One lane-bearing operand in the dense slot table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DrWindowSourceLane {
    dense_slot: u16,
    operand: u8,
    source_id: u16,
}

impl DrWindowSourceLane {
    pub const fn dense_slot(&self) -> usize {
        self.dense_slot as usize
    }

    pub const fn operand(&self) -> usize {
        self.operand as usize
    }

    pub const fn source_id(&self) -> u16 {
        self.source_id
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

/// A pointer-free dimension-reducing width-3 R0 program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DrWindowProgram {
    enabled_mask: u32,
    section_endpoints: [u32; DR_WINDOW_SLOT_COUNT],
    slots: Vec<DrWindowSlotPlan>,
    sources: Vec<GKRAddress>,
    source_lanes: Vec<DrWindowSourceLane>,
}

impl DrWindowProgram {
    pub const fn enabled_mask(&self) -> u32 {
        self.enabled_mask
    }

    pub const fn section_endpoints(&self) -> &[u32; DR_WINDOW_SLOT_COUNT] {
        &self.section_endpoints
    }

    pub fn slots(&self) -> &[DrWindowSlotPlan] {
        &self.slots
    }

    pub fn sources(&self) -> &[GKRAddress] {
        &self.sources
    }

    pub fn source_lanes(&self) -> &[DrWindowSourceLane] {
        &self.source_lanes
    }

    pub fn slot_count(&self) -> usize {
        self.slots.len()
    }

    pub fn source_count(&self) -> usize {
        self.sources.len()
    }

    pub fn source_lane_count(&self) -> usize {
        self.source_lanes.len()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DrWindowLoweringError {
    ZeroMask,
    SourceCountOverflow {
        required: usize,
        capacity: usize,
    },
    SourceLaneCountOverflow {
        required: usize,
        capacity: usize,
    },
    InvalidOperandReference {
        dense_slot: usize,
        operand: usize,
        source_id: u16,
        source_count: usize,
    },
    InconsistentSourceLaneWalk {
        lane: usize,
        expected: Option<(usize, usize, u16)>,
        observed: Option<(usize, usize, u16)>,
    },
}

impl core::fmt::Display for DrWindowLoweringError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for DrWindowLoweringError {}

pub fn lower_dr_window_program(
    rows: &BTreeMap<OutputType, DrWindowInputOutput>,
) -> Result<DrWindowProgram, DrWindowLoweringError> {
    if rows.is_empty() {
        return Err(DrWindowLoweringError::ZeroMask);
    }

    let mut enabled_mask = 0u32;
    let mut slots = Vec::with_capacity(rows.len());
    let mut sources = Vec::with_capacity(rows.len() * DR_WINDOW_OPERANDS_PER_SLOT);
    let mut source_ids = BTreeMap::<GKRAddress, u16>::new();
    let mut source_lanes = Vec::with_capacity(rows.len() * DR_WINDOW_OPERANDS_PER_SLOT);

    for (output_type, row) in rows {
        let slot = output_type_slot(*output_type);
        enabled_mask |= 1 << slot;

        let dense_slot = slots.len();
        let dense_slot_u16 = u16::try_from(dense_slot).map_err(|_| {
            DrWindowLoweringError::SourceLaneCountOverflow {
                required: dense_slot + 1,
                capacity: U16_INDEX_CAPACITY,
            }
        })?;
        let operands = [
            row.inputs()[0],
            row.inputs()[1],
            row.outputs()[0],
            row.outputs()[1],
        ];
        let mut operand_source_ids = [0u16; DR_WINDOW_OPERANDS_PER_SLOT];

        for (operand, address) in operands.into_iter().enumerate() {
            let source_id = intern_source(address, &mut sources, &mut source_ids)?;
            operand_source_ids[operand] = source_id;

            if source_lanes.len() == U16_INDEX_CAPACITY {
                return Err(DrWindowLoweringError::SourceLaneCountOverflow {
                    required: source_lanes.len() + 1,
                    capacity: U16_INDEX_CAPACITY,
                });
            }
            source_lanes.push(DrWindowSourceLane {
                dense_slot: dense_slot_u16,
                operand: operand as u8,
                source_id,
            });
        }

        let batch_base =
            u16::try_from(dense_slot * DR_WINDOW_BATCH_EXPONENTS_PER_SLOT).map_err(|_| {
                DrWindowLoweringError::SourceLaneCountOverflow {
                    required: dense_slot + 1,
                    capacity: U16_INDEX_CAPACITY / DR_WINDOW_BATCH_EXPONENTS_PER_SLOT,
                }
            })?;
        slots.push(DrWindowSlotPlan {
            slot: slot as u8,
            source_ids: operand_source_ids,
            batch_exponents: [batch_base, batch_base + 1],
        });
    }

    let mut section_endpoints = [0u32; DR_WINDOW_SLOT_COUNT];
    let mut dense_cursor = 0usize;
    for (section, endpoint) in section_endpoints.iter_mut().enumerate() {
        while dense_cursor < slots.len() && slots[dense_cursor].slot() <= section {
            dense_cursor += 1;
        }
        *endpoint = dense_cursor as u32;
    }

    let program = DrWindowProgram {
        enabled_mask,
        section_endpoints,
        slots,
        sources,
        source_lanes,
    };
    validate_dr_window_program(&program)?;
    Ok(program)
}

pub fn project_dr_window_inputs(
    program: &DrWindowProgram,
    aliases: &BTreeMap<GKRAddress, GKRAddress>,
) -> DrWindowInputProjection {
    let input_occurrences = program
        .slots
        .iter()
        .enumerate()
        .flat_map(|(dense_slot, slot)| {
            slot.source_ids[..DR_WINDOW_INPUTS_PER_SLOT]
                .iter()
                .copied()
                .enumerate()
                .map(move |(input_operand, source_id)| {
                    let source = program.sources[usize::from(source_id)];
                    let canonical_source = aliases.get(&source).copied().unwrap_or(source);
                    (dense_slot, input_operand, canonical_source)
                })
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

fn intern_source(
    address: GKRAddress,
    sources: &mut Vec<GKRAddress>,
    source_ids: &mut BTreeMap<GKRAddress, u16>,
) -> Result<u16, DrWindowLoweringError> {
    if let Some(source_id) = source_ids.get(&address) {
        return Ok(*source_id);
    }
    let source_id =
        u16::try_from(sources.len()).map_err(|_| DrWindowLoweringError::SourceCountOverflow {
            required: sources.len() + 1,
            capacity: U16_INDEX_CAPACITY,
        })?;
    sources.push(address);
    source_ids.insert(address, source_id);
    Ok(source_id)
}

fn validate_dr_window_program(program: &DrWindowProgram) -> Result<(), DrWindowLoweringError> {
    if program.enabled_mask == 0 {
        return Err(DrWindowLoweringError::ZeroMask);
    }
    if program.sources.len() > U16_INDEX_CAPACITY {
        return Err(DrWindowLoweringError::SourceCountOverflow {
            required: program.sources.len(),
            capacity: U16_INDEX_CAPACITY,
        });
    }
    if program.source_lanes.len() > U16_INDEX_CAPACITY {
        return Err(DrWindowLoweringError::SourceLaneCountOverflow {
            required: program.source_lanes.len(),
            capacity: U16_INDEX_CAPACITY,
        });
    }

    for (dense_slot, slot) in program.slots.iter().enumerate() {
        for (operand, source_id) in slot.source_ids.iter().copied().enumerate() {
            if usize::from(source_id) >= program.sources.len() {
                return Err(DrWindowLoweringError::InvalidOperandReference {
                    dense_slot,
                    operand,
                    source_id,
                    source_count: program.sources.len(),
                });
            }
        }
    }

    let expected_lanes = program
        .slots
        .iter()
        .enumerate()
        .flat_map(|(dense_slot, slot)| {
            slot.source_ids
                .iter()
                .copied()
                .enumerate()
                .map(move |(operand, source_id)| (dense_slot, operand, source_id))
        });
    let observed_lanes = program
        .source_lanes
        .iter()
        .map(|lane| (lane.dense_slot(), lane.operand(), lane.source_id()));
    let expected_len = program.slots.len() * DR_WINDOW_OPERANDS_PER_SLOT;
    let walk_len = expected_len.max(program.source_lanes.len());
    for (lane, (expected, observed)) in expected_lanes
        .map(Some)
        .chain(std::iter::repeat(None))
        .zip(observed_lanes.map(Some).chain(std::iter::repeat(None)))
        .take(walk_len)
        .enumerate()
    {
        if expected != observed {
            return Err(DrWindowLoweringError::InconsistentSourceLaneWalk {
                lane,
                expected,
                observed,
            });
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const OUTPUT_TYPES: [OutputType; DR_WINDOW_SLOT_COUNT] = [
        OutputType::PermutationProduct,
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
        OutputType::InitsAndTeardownsProduct,
    ];

    #[derive(Debug, PartialEq, Eq)]
    struct ProgramObservation {
        slots: Vec<usize>,
        endpoints: [u32; DR_WINDOW_SLOT_COUNT],
        lanes: Vec<(usize, usize, u16)>,
        batch_exponents: Vec<[u16; DR_WINDOW_BATCH_EXPONENTS_PER_SLOT]>,
    }

    fn address(offset: usize) -> GKRAddress {
        GKRAddress::InnerLayer { layer: 1, offset }
    }

    fn sample_program() -> DrWindowProgram {
        lower_dr_window_program(&BTreeMap::from([(
            OutputType::PermutationProduct,
            DrWindowInputOutput::new([address(0), address(1)], [address(2), address(3)]),
        )]))
        .unwrap()
    }

    fn rows_for_mask(mask: u32) -> BTreeMap<OutputType, DrWindowInputOutput> {
        OUTPUT_TYPES
            .into_iter()
            .enumerate()
            .filter(|(slot, _)| mask & (1 << slot) != 0)
            .map(|(slot, output_type)| {
                let base = slot * DR_WINDOW_OPERANDS_PER_SLOT;
                (
                    output_type,
                    DrWindowInputOutput::new(
                        [address(base), address(base + 1)],
                        [address(base + 2), address(base + 3)],
                    ),
                )
            })
            .collect()
    }

    fn observe_program(program: &DrWindowProgram) -> ProgramObservation {
        ProgramObservation {
            slots: program.slots().iter().map(DrWindowSlotPlan::slot).collect(),
            endpoints: *program.section_endpoints(),
            lanes: program
                .source_lanes()
                .iter()
                .map(|lane| (lane.dense_slot(), lane.operand(), lane.source_id()))
                .collect(),
            batch_exponents: program
                .slots()
                .iter()
                .map(|slot| *slot.batch_exponents())
                .collect(),
        }
    }

    #[test]
    fn fixed_array_input_output_accessors_preserve_constructor_order() {
        let inputs = [address(7), address(3)];
        let outputs = [address(11), address(5)];
        let row = DrWindowInputOutput::new(inputs, outputs);

        assert_eq!(row.inputs(), &inputs);
        assert_eq!(row.outputs(), &outputs);
    }

    #[test]
    fn observed_masks_have_exact_sections_operands_and_dense_batch_exponents() {
        let cases = [
            (0x01, [1, 1, 1, 1, 1]),
            (0x0d, [1, 1, 2, 3, 3]),
            (0x0f, [1, 2, 3, 4, 4]),
            (0x1f, [1, 2, 3, 4, 5]),
        ];

        for (mask, endpoints) in cases {
            let rows = rows_for_mask(mask);
            let program = lower_dr_window_program(&rows).unwrap();

            assert_eq!(program.enabled_mask(), mask);
            assert_eq!(program.section_endpoints(), &endpoints);
            assert_eq!(program.slot_count(), mask.count_ones() as usize);
            assert_eq!(program.source_count(), program.slot_count() * 4);
            assert_eq!(program.source_lane_count(), program.slot_count() * 4);

            for (dense_slot, slot) in program.slots().iter().enumerate() {
                let output_type = OUTPUT_TYPES[slot.slot()];
                let row = rows[&output_type];
                let observed_operands = slot
                    .source_ids()
                    .iter()
                    .map(|source_id| program.sources()[usize::from(*source_id)])
                    .collect::<Vec<_>>();
                assert_eq!(
                    observed_operands,
                    [
                        row.inputs()[0],
                        row.inputs()[1],
                        row.outputs()[0],
                        row.outputs()[1],
                    ]
                );
                assert_eq!(
                    slot.batch_exponents(),
                    &[2 * dense_slot as u16, 2 * dense_slot as u16 + 1]
                );
                assert_eq!(slot.source_id(4), None);
            }
        }
    }

    #[test]
    fn unobserved_lookup16_only_mask_is_well_formed() {
        let program = lower_dr_window_program(&rows_for_mask(0x02)).unwrap();

        assert_eq!(program.enabled_mask(), 0x02);
        assert_eq!(program.section_endpoints(), &[0, 1, 1, 1, 1]);
        assert_eq!(observe_program(&program).slots, [1]);
        assert_eq!(program.slots()[0].batch_exponents(), &[0, 1]);
    }

    #[test]
    fn lowers_dense_slots_in_protocol_order() {
        let rows = BTreeMap::from([
            (
                OutputType::PermutationProduct,
                DrWindowInputOutput::new([address(4), address(2)], [address(8), address(9)]),
            ),
            (
                OutputType::GenericLookup,
                DrWindowInputOutput::new([address(10), address(11)], [address(12), address(13)]),
            ),
        ]);

        let program = lower_dr_window_program(&rows).unwrap();
        assert_eq!(program.enabled_mask(), 0b0_1001);
        assert_eq!(program.section_endpoints(), &[1, 1, 1, 2, 2]);
        assert_eq!(
            program
                .slots()
                .iter()
                .map(DrWindowSlotPlan::slot)
                .collect::<Vec<_>>(),
            [0, 3]
        );
        assert_eq!(program.slots()[0].source_ids(), &[0, 1, 2, 3]);
        assert_eq!(program.slots()[1].batch_exponents(), &[2, 3]);
        assert_eq!(program.source_lane_count(), 8);
    }

    #[test]
    fn rejects_zero_mask() {
        assert_eq!(
            lower_dr_window_program(&BTreeMap::new()),
            Err(DrWindowLoweringError::ZeroMask)
        );

        let mut program = sample_program();
        program.enabled_mask = 0;
        assert_eq!(
            validate_dr_window_program(&program),
            Err(DrWindowLoweringError::ZeroMask)
        );
    }

    #[test]
    fn rejects_source_count_overflow() {
        let mut program = sample_program();
        program
            .sources
            .resize(U16_INDEX_CAPACITY + 1, GKRAddress::placeholder());

        assert_eq!(
            validate_dr_window_program(&program),
            Err(DrWindowLoweringError::SourceCountOverflow {
                required: U16_INDEX_CAPACITY + 1,
                capacity: U16_INDEX_CAPACITY,
            })
        );
    }

    #[test]
    fn rejects_source_lane_count_overflow() {
        let mut program = sample_program();
        program
            .source_lanes
            .resize(U16_INDEX_CAPACITY + 1, program.source_lanes[0]);

        assert_eq!(
            validate_dr_window_program(&program),
            Err(DrWindowLoweringError::SourceLaneCountOverflow {
                required: U16_INDEX_CAPACITY + 1,
                capacity: U16_INDEX_CAPACITY,
            })
        );
    }

    #[test]
    fn rejects_invalid_operand_reference() {
        let mut program = sample_program();
        program.slots[0].source_ids[2] = program.sources.len() as u16;

        assert_eq!(
            validate_dr_window_program(&program),
            Err(DrWindowLoweringError::InvalidOperandReference {
                dense_slot: 0,
                operand: 2,
                source_id: 4,
                source_count: 4,
            })
        );
    }

    #[test]
    fn rejects_inconsistent_source_lane_walk() {
        let mut program = sample_program();
        program.source_lanes[1].operand = 3;

        assert_eq!(
            validate_dr_window_program(&program),
            Err(DrWindowLoweringError::InconsistentSourceLaneWalk {
                lane: 1,
                expected: Some((0, 1, 1)),
                observed: Some((0, 3, 1)),
            })
        );
    }

    #[test]
    fn input_projection_is_sorted_aliased_deduplicated_and_input_only() {
        let rows = BTreeMap::from([
            (
                OutputType::PermutationProduct,
                DrWindowInputOutput::new([address(9), address(3)], [address(0), address(1)]),
            ),
            (
                OutputType::LookupTimestamps,
                DrWindowInputOutput::new([address(9), address(7)], [address(2), address(4)]),
            ),
        ]);
        let program = lower_dr_window_program(&rows).unwrap();
        let aliases = BTreeMap::from([(address(9), address(5)), (address(7), address(3))]);

        let projection = project_dr_window_inputs(&program, &aliases);

        assert_eq!(projection.canonical_sources(), &[address(3), address(5)]);
        for output_only in [address(0), address(1), address(2), address(4)] {
            assert!(!projection.canonical_sources().contains(&output_only));
        }
    }

    #[test]
    fn input_projection_maps_every_dense_input_occurrence() {
        let rows = BTreeMap::from([
            (
                OutputType::PermutationProduct,
                DrWindowInputOutput::new([address(9), address(3)], [address(0), address(1)]),
            ),
            (
                OutputType::LookupTimestamps,
                DrWindowInputOutput::new([address(9), address(7)], [address(2), address(4)]),
            ),
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
    fn program_observation_is_sensitive_to_each_lowered_table() {
        let program = lower_dr_window_program(&rows_for_mask(0x1f)).unwrap();
        let baseline = observe_program(&program);

        let mut slot_mutation = program.clone();
        slot_mutation.slots[0].slot = 1;
        assert_ne!(observe_program(&slot_mutation).slots, baseline.slots);

        let mut endpoint_mutation = program.clone();
        endpoint_mutation.section_endpoints[2] -= 1;
        assert_ne!(
            observe_program(&endpoint_mutation).endpoints,
            baseline.endpoints
        );

        let mut lane_mutation = program.clone();
        lane_mutation.source_lanes[3].operand = 0;
        assert_ne!(observe_program(&lane_mutation).lanes, baseline.lanes);
        assert!(matches!(
            validate_dr_window_program(&lane_mutation),
            Err(DrWindowLoweringError::InconsistentSourceLaneWalk { lane: 3, .. })
        ));

        let mut batch_mutation = program;
        batch_mutation.slots[2].batch_exponents[1] += 1;
        assert_ne!(
            observe_program(&batch_mutation).batch_exponents,
            baseline.batch_exponents
        );
    }
}
