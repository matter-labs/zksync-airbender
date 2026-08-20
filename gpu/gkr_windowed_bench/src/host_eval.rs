use field::{Field, FieldExtension};
use gkr_eval_ir::FieldKind;
use gpu_gkr_compiler::backward::{
    decode_continuation_program, decode_r0_program, interpret_coefficient_layer,
    interpret_continuation_program, interpret_r0_program, CoeffLayer, CoeffResolver,
    CoefficientRecipeId, ContinuationLayerProgram, ImmediateId, LeanAtom, LeanSourceBinding,
    LeanTerm, R0LayerProgram, SourceId,
};

use crate::abi::{BF, E4};
use crate::artifact::{
    decode_program, FrozenArtifact, FrozenField, WindowAtom, WindowClass, WindowTerm,
};
use crate::compact::{decode_compact_program, CompactProgramV1, DecodedCompactAtom};
use crate::geometry::{build_allocation_plan, build_lean_allocation_plan, make_eq_sizes};
use crate::r0_input::resolve_normalized_coefficients_for_seed;

pub const PINNED_LOG8_CHECKSUM: u64 = 0xcfeca7094d6c4b25;
pub const PINNED_LOG20_CHECKSUM: u64 = 0x57f0a731d658ac7c;
pub const PINNED_LOG24_CHECKSUM: u64 = 0xae1bdb657d25b249;

const FNV_OFFSET_BASIS: u64 = 0xcbf29ce484222325;
const FNV_MULTIPLIER: u64 = 0x100000001b3;
const SOURCE_COLUMN_BITS: u16 = 7;
const SOURCE_COLUMN_MASK: u16 = (1 << SOURCE_COLUMN_BITS) - 1;

pub enum HostProgram<'a> {
    R0(&'a R0LayerProgram),
    Ext(&'a ContinuationLayerProgram),
    Legacy(&'a FrozenArtifact),
    Compact(&'a CompactProgramV1, &'a FrozenArtifact),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HostEvalError {
    InvalidLogTrace(u32),
    Artifact(String),
    Compact(String),
    Lean(String),
    Source(String),
    LeanMismatch { row: usize, selector: u8, cell: u8 },
}

impl core::fmt::Display for HostEvalError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for HostEvalError {}

pub fn output_checksum(output: &[E4; 27]) -> u64 {
    output.iter().fold(FNV_OFFSET_BASIS, |hash, value| {
        [
            value.c0.c0.raw_u32_value(),
            value.c0.c1.raw_u32_value(),
            value.c1.c0.raw_u32_value(),
            value.c1.c1.raw_u32_value(),
        ]
        .into_iter()
        .fold(hash, |hash, limb| {
            (hash ^ u64::from(limb)).wrapping_mul(FNV_MULTIPLIER)
        })
    })
}

#[derive(Clone, Copy)]
struct Selector {
    x0: u8,
    x1: u8,
}

impl Selector {
    fn from_id(id: u8) -> Self {
        Self {
            x0: id / 3,
            x1: id % 3,
        }
    }

    fn at_infinity(self) -> bool {
        self.x0 == 2 || self.x1 == 2
    }
}

fn bf_add(mut lhs: BF, rhs: BF) -> BF {
    lhs.add_assign(&rhs);
    lhs
}

fn bf_sub(mut lhs: BF, rhs: BF) -> BF {
    lhs.sub_assign(&rhs);
    lhs
}

fn bf_mul(mut lhs: BF, rhs: BF) -> BF {
    lhs.mul_assign(&rhs);
    lhs
}

fn e4_add(mut lhs: E4, rhs: E4) -> E4 {
    lhs.add_assign(&rhs);
    lhs
}

fn e4_sub(mut lhs: E4, rhs: E4) -> E4 {
    lhs.sub_assign(&rhs);
    lhs
}

fn e4_mul(mut lhs: E4, rhs: E4) -> E4 {
    lhs.mul_assign(&rhs);
    lhs
}

fn e4_mul_bf(mut lhs: E4, rhs: BF) -> E4 {
    lhs.mul_assign_by_base(&rhs);
    lhs
}

fn lift(value: BF) -> E4 {
    <E4 as FieldExtension<BF>>::from_base(value)
}

fn initialized_bf(index: usize, seed: u32, component: u32) -> BF {
    let mixed = u64::from(seed)
        .wrapping_add((index as u64).wrapping_mul(17))
        .wrapping_add(u64::from(component).wrapping_mul(0x101));
    let canonical = (mixed % u64::from(BF::ORDER - 1)) as u32 + 1;
    BF::new(canonical)
}

fn initialized_e4(index: usize, seed: u32) -> E4 {
    E4::from_array_of_base([
        initialized_bf(index, seed, 0),
        initialized_bf(index, seed, 1),
        initialized_bf(index, seed, 2),
        initialized_bf(index, seed, 3),
    ])
}

fn procedural_raw(kind: u8, index: usize) -> u32 {
    let index = index as u32;
    match kind {
        0 => u32::from(index < (1 << 16)) * index,
        1 => u32::from(index < (1 << 19)) * index,
        2 => (index << 2) & 0xffff,
        3 => index >> 14,
        _ => 0,
    }
}

enum HostBacking {
    Base(Vec<BF>),
    Ext(Vec<E4>),
}

struct HostWindow {
    field: FrozenField,
    backing: Option<usize>,
    base_element: usize,
    procedural_kind: Option<u8>,
}

struct HostSources {
    trace_len: usize,
    windows: Vec<HostWindow>,
    backings: Vec<HostBacking>,
}

impl HostSources {
    fn from_artifact(
        artifact: &FrozenArtifact,
        log_trace: u32,
        seed_offset: u32,
    ) -> Result<Self, HostEvalError> {
        let plan = build_allocation_plan(artifact, log_trace)
            .map_err(|error| HostEvalError::Artifact(error.to_string()))?;
        let backings = plan
            .backings
            .iter()
            .enumerate()
            .map(|(index, backing)| {
                let seed = 0x1000u32
                    .wrapping_add(index as u32 * 0x101)
                    .wrapping_add(seed_offset);
                let elements = match backing.field {
                    FrozenField::Base => backing.bytes / core::mem::size_of::<BF>(),
                    FrozenField::Ext => backing.bytes / core::mem::size_of::<E4>(),
                };
                match backing.field {
                    FrozenField::Base => HostBacking::Base(
                        (0..elements)
                            .map(|element| initialized_bf(element, seed, 0))
                            .collect(),
                    ),
                    FrozenField::Ext => HostBacking::Ext(
                        (0..elements)
                            .map(|element| initialized_e4(element, seed))
                            .collect(),
                    ),
                }
            })
            .collect();
        let windows = plan
            .windows
            .iter()
            .map(|window| HostWindow {
                field: window.field,
                backing: window.backing,
                base_element: window.base_offset_bytes
                    / match window.field {
                        FrozenField::Base => core::mem::size_of::<BF>(),
                        FrozenField::Ext => core::mem::size_of::<E4>(),
                    },
                procedural_kind: (window.procedural_kind != u8::MAX)
                    .then_some(window.procedural_kind),
            })
            .collect();
        Ok(Self {
            trace_len: plan.trace_len,
            windows,
            backings,
        })
    }

    fn from_binding(
        binding: &LeanSourceBinding,
        log_trace: u32,
        seed_offset: u32,
    ) -> Result<Self, HostEvalError> {
        let plan = build_lean_allocation_plan(binding, log_trace).map_err(|error| match error {
            crate::geometry::GeometryError::UnsupportedLogTrace { log_trace } => {
                HostEvalError::InvalidLogTrace(log_trace)
            }
            error => HostEvalError::Source(error.to_string()),
        })?;
        let backings = plan
            .backings
            .iter()
            .enumerate()
            .map(|(index, backing)| {
                let seed = 0x1000u32
                    .wrapping_add(index as u32 * 0x101)
                    .wrapping_add(seed_offset);
                let elements = backing
                    .columns
                    .checked_mul(plan.trace_len)
                    .ok_or_else(|| HostEvalError::Source("backing size overflow".to_owned()))?;
                Ok(match backing.field {
                    FieldKind::Base => HostBacking::Base(
                        (0..elements)
                            .map(|element| initialized_bf(element, seed, 0))
                            .collect(),
                    ),
                    FieldKind::Ext => HostBacking::Ext(
                        (0..elements)
                            .map(|element| initialized_e4(element, seed))
                            .collect(),
                    ),
                })
            })
            .collect::<Result<Vec<_>, HostEvalError>>()?;
        let windows = plan
            .windows
            .iter()
            .map(|window| {
                let field = match window.field {
                    FieldKind::Base => FrozenField::Base,
                    FieldKind::Ext => FrozenField::Ext,
                };
                HostWindow {
                    field,
                    backing: window.backing,
                    base_element: window.base_element,
                    procedural_kind: window.procedural_kind,
                }
            })
            .collect();
        Ok(Self {
            trace_len: plan.trace_len,
            windows,
            backings,
        })
    }

    fn corner_index(row: usize, bit0: u8, bit1: u8, bit2: u8) -> usize {
        (row << 3) | usize::from(bit2 | (bit1 << 1) | (bit0 << 2))
    }

    fn bf_value(&self, window: usize, column: usize, index: usize) -> Result<BF, HostEvalError> {
        let window = self
            .windows
            .get(window)
            .ok_or_else(|| HostEvalError::Source("BF window out of range".to_owned()))?;
        if let Some(kind) = window.procedural_kind {
            return Ok(BF::new(procedural_raw(kind, index)));
        }
        let backing = window
            .backing
            .and_then(|index| self.backings.get(index))
            .ok_or_else(|| HostEvalError::Source("BF backing missing".to_owned()))?;
        let element = window.base_element + column * self.trace_len + index;
        match backing {
            HostBacking::Base(values) => values
                .get(element)
                .copied()
                .ok_or_else(|| HostEvalError::Source("BF element out of range".to_owned())),
            HostBacking::Ext(_) => Err(HostEvalError::Source(
                "BF coordinate names E4 backing".to_owned(),
            )),
        }
    }

    fn e4_value(&self, window: usize, column: usize, index: usize) -> Result<E4, HostEvalError> {
        let window = self
            .windows
            .get(window)
            .ok_or_else(|| HostEvalError::Source("E4 window out of range".to_owned()))?;
        let backing = window
            .backing
            .and_then(|index| self.backings.get(index))
            .ok_or_else(|| HostEvalError::Source("E4 backing missing".to_owned()))?;
        let element = window.base_element + column * self.trace_len + index;
        match backing {
            HostBacking::Ext(values) => values
                .get(element)
                .copied()
                .ok_or_else(|| HostEvalError::Source("E4 element out of range".to_owned())),
            HostBacking::Base(_) => Err(HostEvalError::Source(
                "E4 coordinate names BF backing".to_owned(),
            )),
        }
    }

    fn bf_triplet(
        &self,
        window: usize,
        column: usize,
        row: usize,
        selector: Selector,
    ) -> Result<[BF; 3], HostEvalError> {
        let endpoint = |bit2| -> Result<BF, HostEvalError> {
            let bit0 = if selector.x0 == 2 { 0 } else { selector.x0 };
            let bit1 = if selector.x1 == 2 { 0 } else { selector.x1 };
            let corner00 =
                self.bf_value(window, column, Self::corner_index(row, bit0, bit1, bit2))?;
            let at_x1_zero = if selector.x0 == 2 {
                bf_sub(
                    self.bf_value(window, column, Self::corner_index(row, 1, bit1, bit2))?,
                    corner00,
                )
            } else {
                corner00
            };
            if selector.x1 != 2 {
                return Ok(at_x1_zero);
            }
            let corner01 = self.bf_value(window, column, Self::corner_index(row, bit0, 1, bit2))?;
            let at_x1_one = if selector.x0 == 2 {
                bf_sub(
                    self.bf_value(window, column, Self::corner_index(row, 1, 1, bit2))?,
                    corner01,
                )
            } else {
                corner01
            };
            Ok(bf_sub(at_x1_one, at_x1_zero))
        };
        let endpoint0 = endpoint(0)?;
        let endpoint1 = endpoint(1)?;
        Ok([endpoint0, endpoint1, bf_sub(endpoint1, endpoint0)])
    }

    fn e4_triplet(
        &self,
        window: usize,
        column: usize,
        row: usize,
        selector: Selector,
    ) -> Result<[E4; 3], HostEvalError> {
        let endpoint = |bit2| -> Result<E4, HostEvalError> {
            let bit0 = if selector.x0 == 2 { 0 } else { selector.x0 };
            let bit1 = if selector.x1 == 2 { 0 } else { selector.x1 };
            let corner00 =
                self.e4_value(window, column, Self::corner_index(row, bit0, bit1, bit2))?;
            let at_x1_zero = if selector.x0 == 2 {
                e4_sub(
                    self.e4_value(window, column, Self::corner_index(row, 1, bit1, bit2))?,
                    corner00,
                )
            } else {
                corner00
            };
            if selector.x1 != 2 {
                return Ok(at_x1_zero);
            }
            let corner01 = self.e4_value(window, column, Self::corner_index(row, bit0, 1, bit2))?;
            let at_x1_one = if selector.x0 == 2 {
                e4_sub(
                    self.e4_value(window, column, Self::corner_index(row, 1, 1, bit2))?,
                    corner01,
                )
            } else {
                corner01
            };
            Ok(e4_sub(at_x1_one, at_x1_zero))
        };
        let endpoint0 = endpoint(0)?;
        let endpoint1 = endpoint(1)?;
        Ok([endpoint0, endpoint1, e4_sub(endpoint1, endpoint0)])
    }

    fn coordinate_parts(coordinate: u16) -> (usize, usize) {
        (
            usize::from(coordinate >> SOURCE_COLUMN_BITS),
            usize::from(coordinate & SOURCE_COLUMN_MASK),
        )
    }

    fn coordinate_field(&self, coordinate: u16) -> Result<FrozenField, HostEvalError> {
        let (window, _) = Self::coordinate_parts(coordinate);
        self.windows
            .get(window)
            .map(|window| window.field)
            .ok_or_else(|| HostEvalError::Source("coordinate window out of range".to_owned()))
    }

    fn coordinate_triplet_e4(
        &self,
        coordinate: u16,
        row: usize,
        selector: Selector,
    ) -> Result<[E4; 3], HostEvalError> {
        let (window, column) = Self::coordinate_parts(coordinate);
        match self.coordinate_field(coordinate)? {
            FrozenField::Base => Ok(self.bf_triplet(window, column, row, selector)?.map(lift)),
            FrozenField::Ext => self.e4_triplet(window, column, row, selector),
        }
    }
}

fn coefficient(id: u32, seed_offset: u32) -> E4 {
    let id = CoefficientRecipeId(id);
    id.literal()
        .unwrap_or_else(|| initialized_e4(id.0 as usize, 0x6000u32.wrapping_add(seed_offset)))
}

fn gpu_coefficient(id: u16, seed_offset: u32) -> E4 {
    coefficient(u32::from(id), seed_offset)
}

fn equality_value(row: usize, log_trace: u32, seed_offset: u32) -> Result<E4, HostEvalError> {
    let sizes = make_eq_sizes(log_trace).map_err(|_| HostEvalError::InvalidLogTrace(log_trace))?;
    let hi0 = (row >> (sizes.low + sizes.high[1])) & ((1usize << sizes.high[0]) - 1);
    let hi1 = (row >> sizes.low) & ((1usize << sizes.high[1]) - 1);
    let low = row & ((1usize << sizes.low) - 1);
    let mut value = initialized_e4(hi0, 0x6000u32.wrapping_add(seed_offset));
    value = e4_mul(
        value,
        initialized_e4(256 + hi1, 0x6000u32.wrapping_add(seed_offset)),
    );
    Ok(e4_mul(
        value,
        initialized_e4(low, 0x4000u32.wrapping_add(seed_offset)),
    ))
}

fn fold_rows(
    log_trace: u32,
    seed_offset: u32,
    mut row_values: impl FnMut(usize, Selector) -> Result<[E4; 3], HostEvalError>,
) -> Result<[E4; 27], HostEvalError> {
    if !(3..=27).contains(&log_trace) {
        return Err(HostEvalError::InvalidLogTrace(log_trace));
    }
    let rows = 1usize << (log_trace - 3);
    let mut output = [E4::ZERO; 27];
    for row in 0..rows {
        let eq = equality_value(row, log_trace, seed_offset)?;
        for selector_id in 0..9u8 {
            let values = row_values(row, Selector::from_id(selector_id))?;
            for cell in 0..3 {
                let index = 3 * usize::from(selector_id) + cell;
                output[index] = e4_add(output[index], e4_mul(eq, values[cell]));
            }
        }
    }
    Ok(output)
}

enum TermTriplet {
    Base([BF; 3]),
    Ext([E4; 3]),
}

fn zero_base() -> [BF; 3] {
    [BF::ZERO; 3]
}

fn zero_ext() -> [E4; 3] {
    [E4::ZERO; 3]
}

fn procedural_triplet(kind: u8, row: usize, selector: Selector) -> [BF; 3] {
    let endpoints = [0, 1].map(|bit2| {
        let endpoint = |bit0, bit1| {
            BF::new(procedural_raw(
                kind,
                HostSources::corner_index(row, bit0, bit1, bit2),
            ))
        };
        let bit0 = if selector.x0 == 2 { 0 } else { selector.x0 };
        let bit1 = if selector.x1 == 2 { 0 } else { selector.x1 };
        let zero = if selector.x0 == 2 {
            bf_sub(endpoint(1, bit1), endpoint(0, bit1))
        } else {
            endpoint(bit0, bit1)
        };
        if selector.x1 == 2 {
            let one = if selector.x0 == 2 {
                bf_sub(endpoint(1, 1), endpoint(0, 1))
            } else {
                endpoint(bit0, 1)
            };
            bf_sub(one, zero)
        } else {
            zero
        }
    });
    [
        endpoints[0],
        endpoints[1],
        bf_sub(endpoints[1], endpoints[0]),
    ]
}

fn eval_window_term(
    term: WindowTerm,
    sources: &HostSources,
    row: usize,
    selector: Selector,
) -> Result<TermTriplet, HostEvalError> {
    let bf_direct = |coordinate| {
        let (window, column) = HostSources::coordinate_parts(coordinate);
        sources.bf_triplet(window, column, row, selector)
    };
    let e4_direct = |coordinate| {
        let (window, column) = HostSources::coordinate_parts(coordinate);
        sources.e4_triplet(window, column, row, selector)
    };
    match term.class {
        WindowClass::LinearBf => {
            if selector.at_infinity() {
                return Ok(TermTriplet::Base(zero_base()));
            }
            let a = bf_direct(term.source_a)?;
            Ok(TermTriplet::Base([a[0], a[1], BF::ZERO]))
        }
        WindowClass::LinearBfProceduralA => {
            if selector.at_infinity() {
                return Ok(TermTriplet::Base(zero_base()));
            }
            let a = procedural_triplet(term.source_a as u8, row, selector);
            Ok(TermTriplet::Base([a[0], a[1], BF::ZERO]))
        }
        WindowClass::ProductBfBf => {
            let a = bf_direct(term.source_a)?;
            let b = bf_direct(term.source_b)?;
            Ok(TermTriplet::Base([
                bf_mul(a[0], b[0]),
                bf_mul(a[1], b[1]),
                bf_mul(a[2], b[2]),
            ]))
        }
        WindowClass::ProductBfBfProceduralB => {
            let a = bf_direct(term.source_a)?;
            let b = procedural_triplet(term.source_b as u8, row, selector);
            Ok(TermTriplet::Base([
                bf_mul(a[0], b[0]),
                bf_mul(a[1], b[1]),
                bf_mul(a[2], b[2]),
            ]))
        }
        WindowClass::LinearE4 => {
            if selector.at_infinity() {
                return Ok(TermTriplet::Ext(zero_ext()));
            }
            let a = e4_direct(term.source_a)?;
            Ok(TermTriplet::Ext([a[0], a[1], E4::ZERO]))
        }
        WindowClass::ProductBfE4 => {
            let a = bf_direct(term.source_a)?;
            let b = e4_direct(term.source_b)?;
            Ok(TermTriplet::Ext([
                e4_mul_bf(b[0], a[0]),
                e4_mul_bf(b[1], a[1]),
                e4_mul_bf(b[2], a[2]),
            ]))
        }
        WindowClass::ProductE4E4 => {
            let a = e4_direct(term.source_a)?;
            let b = e4_direct(term.source_b)?;
            Ok(TermTriplet::Ext([
                e4_mul(a[0], b[0]),
                e4_mul(a[1], b[1]),
                e4_mul(a[2], b[2]),
            ]))
        }
        WindowClass::GroupBf | WindowClass::GroupE4 => Err(HostEvalError::Artifact(
            "group class appeared as a member".to_owned(),
        )),
    }
}

fn apply_bf_immediate(
    sum: &mut [BF; 3],
    value: [BF; 3],
    immediate: u16,
    artifact: &FrozenArtifact,
) -> Result<(), HostEvalError> {
    let scale = if immediate >= 2 {
        Some(BF::from_raw_u32(
            *artifact
                .immediates
                .get(usize::from(immediate - 2))
                .ok_or_else(|| HostEvalError::Artifact("immediate out of range".to_owned()))?,
        ))
    } else {
        None
    };
    for cell in 0..3 {
        sum[cell] = match immediate {
            0 => bf_add(sum[cell], value[cell]),
            1 => bf_sub(sum[cell], value[cell]),
            _ => bf_add(sum[cell], bf_mul(scale.unwrap(), value[cell])),
        };
    }
    Ok(())
}

fn apply_e4_immediate(sum: &mut [E4; 3], value: [E4; 3], immediate: u16) {
    for cell in 0..3 {
        sum[cell] = if immediate == 0 {
            e4_add(sum[cell], value[cell])
        } else {
            e4_sub(sum[cell], value[cell])
        };
    }
}

fn accumulate_decoded_atom(
    core: u16,
    grouped: bool,
    members: &[WindowTerm],
    artifact: &FrozenArtifact,
    sources: &HostSources,
    row: usize,
    selector: Selector,
    accumulators: &mut [E4; 3],
    seed_offset: u32,
) -> Result<(), HostEvalError> {
    let core = gpu_coefficient(core, seed_offset);
    if members.first().is_some_and(|member| {
        matches!(
            member.class,
            WindowClass::LinearBf
                | WindowClass::ProductBfBf
                | WindowClass::LinearBfProceduralA
                | WindowClass::ProductBfBfProceduralB
        )
    }) {
        let mut sum = zero_base();
        for member in members {
            let value = match eval_window_term(*member, sources, row, selector)? {
                TermTriplet::Base(value) => value,
                TermTriplet::Ext(_) => {
                    return Err(HostEvalError::Artifact("mixed BF/E4 atom".to_owned()));
                }
            };
            if grouped {
                apply_bf_immediate(&mut sum, value, member.coefficient, artifact)?;
            } else {
                sum = value;
            }
        }
        for cell in 0..3 {
            accumulators[cell] = e4_add(accumulators[cell], e4_mul_bf(core, sum[cell]));
        }
    } else {
        let mut sum = zero_ext();
        for member in members {
            let value = match eval_window_term(*member, sources, row, selector)? {
                TermTriplet::Ext(value) => value,
                TermTriplet::Base(_) => {
                    return Err(HostEvalError::Artifact("mixed BF/E4 atom".to_owned()));
                }
            };
            if grouped {
                apply_e4_immediate(&mut sum, value, member.coefficient);
            } else {
                sum = value;
            }
        }
        for cell in 0..3 {
            accumulators[cell] = e4_add(accumulators[cell], e4_mul(core, sum[cell]));
        }
    }
    Ok(())
}

fn legacy_row(
    atoms: &[WindowAtom],
    artifact: &FrozenArtifact,
    sources: &HostSources,
    row: usize,
    selector: Selector,
    seed_offset: u32,
) -> Result<[E4; 3], HostEvalError> {
    let mut accumulators = zero_ext();
    for atom in atoms {
        match atom {
            WindowAtom::Term(term) => accumulate_decoded_atom(
                term.coefficient,
                false,
                core::slice::from_ref(term),
                artifact,
                sources,
                row,
                selector,
                &mut accumulators,
                seed_offset,
            )?,
            WindowAtom::GroupBf { core, members, .. } | WindowAtom::GroupE4 { core, members } => {
                accumulate_decoded_atom(
                    *core,
                    true,
                    members,
                    artifact,
                    sources,
                    row,
                    selector,
                    &mut accumulators,
                    seed_offset,
                )?
            }
        }
    }
    if !selector.at_infinity() {
        if let Some(c_init) = artifact.c_init_coeff {
            let c_init = gpu_coefficient(c_init as u16, seed_offset);
            accumulators[0] = e4_add(accumulators[0], c_init);
            accumulators[1] = e4_add(accumulators[1], c_init);
        }
    }
    Ok(accumulators)
}

fn compact_row(
    atoms: &[DecodedCompactAtom],
    artifact: &FrozenArtifact,
    sources: &HostSources,
    row: usize,
    selector: Selector,
    seed_offset: u32,
) -> Result<[E4; 3], HostEvalError> {
    let mut accumulators = zero_ext();
    for atom in atoms {
        accumulate_decoded_atom(
            atom.core,
            atom.canonical_records.len() > 1,
            &atom.members,
            artifact,
            sources,
            row,
            selector,
            &mut accumulators,
            seed_offset,
        )?;
    }
    if !selector.at_infinity() {
        if let Some(c_init) = artifact.c_init_coeff {
            let c_init = gpu_coefficient(c_init as u16, seed_offset);
            accumulators[0] = e4_add(accumulators[0], c_init);
            accumulators[1] = e4_add(accumulators[1], c_init);
        }
    }
    Ok(accumulators)
}

#[derive(Clone, Copy)]
enum LeanRegime {
    R0,
    Ext,
}

#[derive(Clone, Copy)]
struct LeanParts3 {
    c0: [E4; 2],
    c2: E4,
}

impl LeanParts3 {
    fn zero() -> Self {
        Self {
            c0: [E4::ZERO; 2],
            c2: E4::ZERO,
        }
    }

    fn add_assign(&mut self, other: Self) {
        self.c0[0] = e4_add(self.c0[0], other.c0[0]);
        self.c0[1] = e4_add(self.c0[1], other.c0[1]);
        self.c2 = e4_add(self.c2, other.c2);
    }

    fn sub_assign(&mut self, other: Self) {
        self.c0[0] = e4_sub(self.c0[0], other.c0[0]);
        self.c0[1] = e4_sub(self.c0[1], other.c0[1]);
        self.c2 = e4_sub(self.c2, other.c2);
    }

    fn scale_assign(&mut self, scale: E4) {
        self.c0[0] = e4_mul(scale, self.c0[0]);
        self.c0[1] = e4_mul(scale, self.c0[1]);
        self.c2 = e4_mul(scale, self.c2);
    }

    fn cells(self, regime: LeanRegime) -> [E4; 3] {
        let at_one = match regime {
            LeanRegime::R0 => e4_add(self.c0[1], self.c2),
            LeanRegime::Ext => self.c0[1],
        };
        [self.c0[0], at_one, self.c2]
    }
}

struct LeanSourceResolver<'a> {
    binding: &'a LeanSourceBinding,
    sources: &'a HostSources,
    row: usize,
    selector: Selector,
    shifted: bool,
    seed_offset: u32,
}

impl LeanSourceResolver<'_> {
    fn triplet(&self, source: SourceId) -> Result<[E4; 3], HostEvalError> {
        let slot = self
            .binding
            .source_slots
            .get(source.0 as usize)
            .ok_or_else(|| HostEvalError::Source("lean source slot out of range".to_owned()))?;
        let coordinate = (u16::from(slot.window) << SOURCE_COLUMN_BITS) | slot.column;
        self.sources
            .coordinate_triplet_e4(coordinate, self.row, self.selector)
    }
}

impl CoeffResolver for LeanSourceResolver<'_> {
    fn coefficient(&self, id: CoefficientRecipeId) -> E4 {
        coefficient(id.0, self.seed_offset)
    }

    fn source_pair(&self, id: SourceId, _row: usize) -> (E4, E4) {
        let values = self
            .triplet(id)
            .expect("validated lean source binding must resolve");
        (values[usize::from(self.shifted)], values[2])
    }
}

struct ScheduleSourceResolver<'a> {
    source: LeanSourceResolver<'a>,
    coefficient_bank: &'a [E4],
}

impl CoeffResolver for ScheduleSourceResolver<'_> {
    fn coefficient(&self, id: CoefficientRecipeId) -> E4 {
        self.coefficient_bank[id
            .bank_index()
            .expect("reserved literals are resolved by the coefficient interpreter")]
    }

    fn source_pair(&self, id: SourceId, row: usize) -> (E4, E4) {
        self.source.source_pair(id, row)
    }
}

pub fn evaluate_continuation_coeff_schedule(
    coefficients: &CoeffLayer,
    binding: &LeanSourceBinding,
    log_trace: u32,
    seed: u64,
) -> Result<[E4; 27], HostEvalError> {
    let seed_offset = seed as u32;
    let sources = HostSources::from_binding(binding, log_trace, seed_offset)?;
    let coefficient_bank =
        resolve_normalized_coefficients_for_seed(&coefficients.coefficients, seed)
            .map_err(|error| HostEvalError::Lean(error.to_string()))?;
    fold_rows(log_trace, seed_offset, |row, selector| {
        let current = ScheduleSourceResolver {
            source: LeanSourceResolver {
                binding,
                sources: &sources,
                row,
                selector,
                shifted: false,
                seed_offset,
            },
            coefficient_bank: &coefficient_bank,
        };
        let shifted = ScheduleSourceResolver {
            source: LeanSourceResolver {
                binding,
                sources: &sources,
                row,
                selector,
                shifted: true,
                seed_offset,
            },
            coefficient_bank: &coefficient_bank,
        };
        let (c0, c2) = interpret_coefficient_layer(coefficients, row, &current)
            .map_err(|error| HostEvalError::Lean(format!("{error:?}")))?;
        let (at_one, _) = interpret_coefficient_layer(coefficients, row, &shifted)
            .map_err(|error| HostEvalError::Lean(format!("{error:?}")))?;
        Ok([c0, at_one, c2])
    })
}

fn lean_term_parts(
    regime: LeanRegime,
    term: LeanTerm,
    resolver: &LeanSourceResolver<'_>,
) -> Result<LeanParts3, HostEvalError> {
    let a = resolver.triplet(SourceId(u32::from(term.source_a)))?;
    let b = || resolver.triplet(SourceId(u32::from(term.source_b)));
    let linear = |a: [E4; 3]| {
        if resolver.selector.at_infinity() {
            LeanParts3::zero()
        } else {
            LeanParts3 {
                c0: [a[0], a[1]],
                c2: E4::ZERO,
            }
        }
    };
    match (regime, term.class) {
        (LeanRegime::R0, 0 | 1) | (LeanRegime::Ext, 0) => Ok(linear(a)),
        (LeanRegime::R0, 2..=4) => {
            let b = b()?;
            let c2 = e4_mul(a[2], b[2]);
            Ok(LeanParts3 {
                c0: [E4::ZERO; 2],
                c2,
            })
        }
        (LeanRegime::Ext, 1) => {
            let b = b()?;
            Ok(LeanParts3 {
                c0: [e4_mul(a[0], b[0]), e4_mul(a[1], b[1])],
                c2: e4_mul(a[2], b[2]),
            })
        }
        _ => Err(HostEvalError::Lean(format!(
            "class {} is invalid for selected regime",
            term.class
        ))),
    }
}

fn lean_immediate(id: u16, table: &[u32]) -> Result<Option<E4>, HostEvalError> {
    if id < ImmediateId::RESERVED {
        return Ok(None);
    }
    let raw = *table
        .get(usize::from(id - ImmediateId::RESERVED))
        .ok_or_else(|| HostEvalError::Lean("immediate out of range".to_owned()))?;
    Ok(Some(lift(BF::from_raw_u32(raw))))
}

fn lean_row(
    regime: LeanRegime,
    atoms: &[LeanAtom],
    binding: &LeanSourceBinding,
    immediates: &[u32],
    c_init: Option<CoefficientRecipeId>,
    sources: &HostSources,
    row: usize,
    selector: Selector,
    seed_offset: u32,
) -> Result<[E4; 3], HostEvalError> {
    let resolver = LeanSourceResolver {
        binding,
        sources,
        row,
        selector,
        shifted: false,
        seed_offset,
    };
    let mut accumulator = LeanParts3::zero();
    for atom in atoms {
        match atom {
            LeanAtom::Term(term) => {
                let mut parts = lean_term_parts(regime, *term, &resolver)?;
                parts.scale_assign(coefficient(u32::from(term.coeff), seed_offset));
                accumulator.add_assign(parts);
            }
            LeanAtom::Group {
                core,
                has_c0,
                has_c2,
                members,
            } => {
                let mut sum = LeanParts3::zero();
                for member in members {
                    let parts = lean_term_parts(regime, *member, &resolver)?;
                    match member.coeff {
                        0 => sum.add_assign(parts),
                        1 => sum.sub_assign(parts),
                        id => {
                            let mut parts = parts;
                            parts.scale_assign(lean_immediate(id, immediates)?.unwrap());
                            sum.add_assign(parts);
                        }
                    }
                }
                if !has_c0 {
                    sum.c0 = [E4::ZERO; 2];
                }
                if !has_c2 {
                    sum.c2 = E4::ZERO;
                }
                sum.scale_assign(coefficient(u32::from(*core), seed_offset));
                accumulator.add_assign(sum);
            }
        }
    }
    if !selector.at_infinity() {
        if let Some(c_init) = c_init {
            let value = coefficient(c_init.0, seed_offset);
            accumulator.c0[0] = e4_add(accumulator.c0[0], value);
            accumulator.c0[1] = e4_add(accumulator.c0[1], value);
        }
    }
    Ok(accumulator.cells(regime))
}

fn normalized_immediate(value: u32) -> u32 {
    BF::from_raw_u32(value).to_u32()
}

fn verify_upstream_r0(
    layer: &R0LayerProgram,
    sources: &HostSources,
    row: usize,
    selector_id: u8,
    seed_offset: u32,
    expected: [E4; 3],
) -> Result<(), HostEvalError> {
    let selector = Selector::from_id(selector_id);
    if selector.at_infinity() {
        return Ok(());
    }
    let mut normalized = layer.clone();
    normalized
        .coefficients
        .immediates
        .iter_mut()
        .for_each(|value| *value = normalized_immediate(*value));
    let resolver = LeanSourceResolver {
        binding: &normalized.binding,
        sources,
        row,
        selector,
        shifted: false,
        seed_offset,
    };
    let shifted = LeanSourceResolver {
        shifted: true,
        ..resolver
    };
    let (c0, c2) = interpret_r0_program(&normalized, row, &resolver, 1)
        .map_err(|error| HostEvalError::Lean(format!("{error:?}")))?;
    let (at_one, _) = interpret_r0_program(&normalized, row, &shifted, 1)
        .map_err(|error| HostEvalError::Lean(format!("{error:?}")))?;
    let observed = [c0, e4_add(at_one, c2), c2];
    for cell in 0..3 {
        if observed[cell] != expected[cell] {
            return Err(HostEvalError::LeanMismatch {
                row,
                selector: selector_id,
                cell: cell as u8,
            });
        }
    }
    Ok(())
}

fn verify_upstream_ext(
    layer: &ContinuationLayerProgram,
    sources: &HostSources,
    row: usize,
    selector_id: u8,
    seed_offset: u32,
    expected: [E4; 3],
) -> Result<(), HostEvalError> {
    let selector = Selector::from_id(selector_id);
    if selector.at_infinity() {
        return Ok(());
    }
    let mut normalized = layer.clone();
    normalized
        .coefficients
        .immediates
        .iter_mut()
        .for_each(|value| *value = normalized_immediate(*value));
    let resolver = LeanSourceResolver {
        binding: &normalized.binding,
        sources,
        row,
        selector,
        shifted: false,
        seed_offset,
    };
    let shifted = LeanSourceResolver {
        shifted: true,
        ..resolver
    };
    let (c0, c2) = interpret_continuation_program(&normalized, row, &resolver, 1)
        .map_err(|error| HostEvalError::Lean(format!("{error:?}")))?;
    let (at_one, _) = interpret_continuation_program(&normalized, row, &shifted, 1)
        .map_err(|error| HostEvalError::Lean(format!("{error:?}")))?;
    let observed = [c0, at_one, c2];
    for cell in 0..3 {
        if observed[cell] != expected[cell] {
            return Err(HostEvalError::LeanMismatch {
                row,
                selector: selector_id,
                cell: cell as u8,
            });
        }
    }
    Ok(())
}

pub fn evaluate_windowed(
    program: HostProgram<'_>,
    log_trace: u32,
    seed: u64,
) -> Result<[E4; 27], HostEvalError> {
    let seed_offset = seed as u32;
    match program {
        HostProgram::Legacy(artifact) => {
            let sources = HostSources::from_artifact(artifact, log_trace, seed_offset)?;
            let atoms = decode_program(artifact)
                .map_err(|error| HostEvalError::Artifact(error.to_string()))?
                .0;
            fold_rows(log_trace, seed_offset, |row, selector| {
                legacy_row(&atoms, artifact, &sources, row, selector, seed_offset)
            })
        }
        HostProgram::Compact(program, artifact) => {
            let sources = HostSources::from_artifact(artifact, log_trace, seed_offset)?;
            let atoms = decode_compact_program(program)
                .map_err(|error| HostEvalError::Compact(error.to_string()))?;
            fold_rows(log_trace, seed_offset, |row, selector| {
                compact_row(&atoms, artifact, &sources, row, selector, seed_offset)
            })
        }
        HostProgram::R0(layer) => {
            let sources = HostSources::from_binding(&layer.binding, log_trace, seed_offset)?;
            let atoms = decode_r0_program(&layer.program)
                .map_err(|error| HostEvalError::Lean(format!("{error:?}")))?;
            fold_rows(log_trace, seed_offset, |row, selector| {
                let values = lean_row(
                    LeanRegime::R0,
                    &atoms,
                    &layer.binding,
                    &layer.coefficients.immediates,
                    layer.coefficients.c_init,
                    &sources,
                    row,
                    selector,
                    seed_offset,
                )?;
                let selector_id = selector.x0 * 3 + selector.x1;
                verify_upstream_r0(layer, &sources, row, selector_id, seed_offset, values)?;
                Ok(values)
            })
        }
        HostProgram::Ext(layer) => {
            let sources = HostSources::from_binding(&layer.binding, log_trace, seed_offset)?;
            let atoms = decode_continuation_program(&layer.program)
                .map_err(|error| HostEvalError::Lean(format!("{error:?}")))?;
            fold_rows(log_trace, seed_offset, |row, selector| {
                let values = lean_row(
                    LeanRegime::Ext,
                    &atoms,
                    &layer.binding,
                    &layer.coefficients.immediates,
                    layer.coefficients.c_init,
                    &sources,
                    row,
                    selector,
                    seed_offset,
                )?;
                let selector_id = selector.x0 * 3 + selector.x1;
                verify_upstream_ext(layer, &sources, row, selector_id, seed_offset, values)?;
                Ok(values)
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use cs::gkr_compiler::GKRCircuitArtifact;
    use gkr_eval_ir::{lower_dag, validate};
    use gpu_gkr_compiler::{compile_continuations, compile_r0, GpuResourceProfile};

    use crate::artifact::{decode_artifact, ADD_SUB_LAYER0_BYTES};
    use crate::compact::{encode_compact_program, CompactPolicy};
    use crate::r0_artifact::{decode_r0_bundle, R0_CORPUS_BYTES};
    use crate::r0_input::build_r0_input_with_layer;
    use crate::r0_reference::{evaluate_compiled_r0_tensor, tensor_index};

    use super::*;

    fn retained_layer() -> ContinuationLayerProgram {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json");
        let circuit: GKRCircuitArtifact<BF> =
            serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        let dag = lower_dag(&circuit).unwrap();
        validate(&dag).unwrap();
        compile_continuations(&dag)
            .unwrap()
            .layers
            .into_iter()
            .find(|layer| layer.layer == 0)
            .unwrap()
    }

    #[test]
    fn checksum_contract_pins_main_literals_and_limb_order() {
        assert_eq!(FNV_OFFSET_BASIS, 0xcbf29ce484222325);
        assert_eq!(FNV_MULTIPLIER, 0x100000001b3);
        assert_eq!(PINNED_LOG8_CHECKSUM, 0xcfeca7094d6c4b25);
        assert_eq!(PINNED_LOG20_CHECKSUM, 0x57f0a731d658ac7c);
        assert_eq!(PINNED_LOG24_CHECKSUM, 0xae1bdb657d25b249);
        let value = E4::from_array_of_base([
            BF::from_raw_u32(1),
            BF::from_raw_u32(2),
            BF::from_raw_u32(3),
            BF::from_raw_u32(4),
        ]);
        let mut output = [E4::ZERO; 27];
        output[0] = value;
        assert_eq!(output_checksum(&output), 0x4f1ff0994100e17d);
    }

    #[test]
    fn cpu_compiled_r0_reference_owns_infinity_coverage() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json");
        let circuit: GKRCircuitArtifact<BF> =
            serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        let dag = lower_dag(&circuit).unwrap();
        validate(&dag).unwrap();
        let program = compile_r0(&dag).unwrap().layers.remove(0);

        // The retained per-row verifier deliberately returns before checking an
        // infinity selector, even when handed an impossible expected value.
        let legacy_sources = HostSources::from_binding(&program.binding, 3, 0).unwrap();
        assert!(verify_upstream_r0(&program, &legacy_sources, 0, 6, 0, [E4::ONE; 3],).is_ok());

        // The new compiler-R0 reference evaluates those cells rather than
        // delegating to the historical verifier's finite-selector fast path.
        let coordinate = decode_r0_bundle(R0_CORPUS_BYTES)
            .unwrap()
            .coordinates
            .into_iter()
            .find(|coordinate| {
                coordinate.circuit == "add_sub_lui_auipc_mop" && coordinate.layer == 0
            })
            .unwrap();
        let input = build_r0_input_with_layer(&coordinate, &dag.layers[0], 3, 0).unwrap();
        let output = evaluate_compiled_r0_tensor(&program, &input).unwrap();
        assert!((0..3).any(|x2| !output[tensor_index(2, 0, x2)].is_zero()));
        assert!((0..3).any(|x2| !output[tensor_index(0, 2, x2)].is_zero()));
    }

    #[test]
    fn add_sub_log8_lean_legacy_and_all_measured_compact_policies_match_gpu() {
        let layer = retained_layer();
        let artifact = decode_artifact(ADD_SUB_LAYER0_BYTES).unwrap();
        let atoms = decode_program(&artifact).unwrap().0;
        let lean = evaluate_windowed(HostProgram::Ext(&layer), 8, 0).unwrap();
        let legacy = evaluate_windowed(HostProgram::Legacy(&artifact), 8, 0).unwrap();
        assert_eq!(lean, legacy);
        for policy in [
            CompactPolicy::DIRECT_PREFIX,
            CompactPolicy {
                same_window_product_prefix: true,
                ..CompactPolicy::DIRECT_PREFIX
            },
            CompactPolicy {
                permute_within_segment: true,
                ..CompactPolicy::DIRECT_PREFIX
            },
            CompactPolicy {
                same_window_product_prefix: true,
                permute_within_segment: true,
                ..CompactPolicy::DIRECT_PREFIX
            },
        ] {
            let compact = encode_compact_program(&atoms, &artifact, policy).unwrap();
            let compact =
                evaluate_windowed(HostProgram::Compact(&compact, &artifact), 8, 0).unwrap();
            assert_eq!(compact, legacy, "policy={policy:?}");
        }
        assert_eq!(output_checksum(&legacy), PINNED_LOG8_CHECKSUM);
    }

    #[test]
    fn full_corpus_lean_front_ends_match_upstream_for_every_layer() {
        const CORPUS: [&str; 12] = [
            "add_sub_lui_auipc_mop_layout_gkr.json",
            "bigint_with_extended_control_layout_gkr.json",
            "blake2_g_function_layout_gkr.json",
            "blake2_with_extended_control_layout_gkr.json",
            "inits_and_teardowns_layout_gkr.json",
            "jump_branch_slt_layout_gkr.json",
            "keccak_special5_layout_gkr.json",
            "mem_subword_only_layout_gkr.json",
            "mem_word_only_layout_gkr.json",
            "shift_binop_layout_gkr.json",
            "unified_reduced_machine_layout_gkr.json",
            "unsigned_mul_div_layout_gkr.json",
        ];
        let directory =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
        let profile = GpuResourceProfile::production();
        let mut coordinates = 0usize;
        for layout in CORPUS {
            let circuit: GKRCircuitArtifact<BF> =
                serde_json::from_slice(&std::fs::read(directory.join(layout)).unwrap()).unwrap();
            let dag = lower_dag(&circuit).unwrap();
            validate(&dag).unwrap();
            let r0 = compile_r0(&dag).unwrap();
            let ext = compile_continuations(&dag).unwrap();
            for layer in &r0.layers {
                evaluate_windowed(HostProgram::R0(layer), 3, 0)
                    .unwrap_or_else(|error| panic!("{layout} R0 L{}: {error}", layer.layer));
                coordinates += 1;
            }
            for layer in &ext.layers {
                evaluate_windowed(HostProgram::Ext(layer), 3, 0)
                    .unwrap_or_else(|error| panic!("{layout} Ext L{}: {error}", layer.layer));
                coordinates += 1;
            }
        }
        assert_eq!(coordinates, 114);
    }

    #[test]
    fn census_structural_bounds_hold_for_every_coordinate() {
        let weights: crate::census::WorkloadWeightsV1 = serde_json::from_slice(include_bytes!(
            "../artifacts/windowed_workload_weights_v1.json"
        ))
        .unwrap();
        let census = crate::census::generate_corpus_census(weights).unwrap();
        let p = crate::wide_model::P;
        for coordinate in &census.coordinates {
            for (prefix, ends) in coordinate
                .semantic
                .product_prefix_lengths
                .iter()
                .zip(&coordinate.semantic.inner_segment_ends)
            {
                let mut start = 0u16;
                for end in ends {
                    assert!(*end > start && *end - start <= 4, "{:?}", coordinate.id);
                    start = *end;
                }
                assert_eq!(start, *prefix, "{:?}", coordinate.id);
            }
            let outer = u128::from(coordinate.semantic.bf_atoms) * (p - 1) * (p - 1);
            assert!(outer < (1u128 << 96), "{:?}", coordinate.id);
        }
        let retained = census
            .coordinates
            .iter()
            .find(|coordinate| {
                coordinate.id.circuit == "add_sub_lui_auipc_mop"
                    && coordinate.id.layer == 0
                    && coordinate.id.regime == crate::census::BackwardRegime::Ext
            })
            .unwrap();
        let retained_outer = u128::from(retained.semantic.bf_atoms) * (p - 1) * (p - 1);
        assert_eq!(retained.semantic.bf_atoms, 65);
        assert_eq!(retained_outer >> 64, 14);
    }

    #[test]
    fn encodable_continuation_corpus_matches_lean_legacy_and_compact() {
        const CORPUS: [&str; 12] = [
            "add_sub_lui_auipc_mop_layout_gkr.json",
            "bigint_with_extended_control_layout_gkr.json",
            "blake2_g_function_layout_gkr.json",
            "blake2_with_extended_control_layout_gkr.json",
            "inits_and_teardowns_layout_gkr.json",
            "jump_branch_slt_layout_gkr.json",
            "keccak_special5_layout_gkr.json",
            "mem_subword_only_layout_gkr.json",
            "mem_word_only_layout_gkr.json",
            "shift_binop_layout_gkr.json",
            "unified_reduced_machine_layout_gkr.json",
            "unsigned_mul_div_layout_gkr.json",
        ];
        let census: crate::census::CorpusCensusV1 = serde_json::from_slice(include_bytes!(
            "../artifacts/windowed_corpus_census_v1.json"
        ))
        .unwrap();
        let directory =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
        let profile = GpuResourceProfile::production();
        let mut compared = 0usize;
        for layout in CORPUS {
            let circuit_name = layout.strip_suffix("_layout_gkr.json").unwrap();
            let circuit: GKRCircuitArtifact<BF> =
                serde_json::from_slice(&std::fs::read(directory.join(layout)).unwrap()).unwrap();
            let dag = lower_dag(&circuit).unwrap();
            validate(&dag).unwrap();
            let ext = compile_continuations(&dag).unwrap();
            for layer in &ext.layers {
                let coordinate = census
                    .coordinates
                    .iter()
                    .find(|coordinate| {
                        coordinate.id.circuit == circuit_name
                            && coordinate.id.layer == layer.layer as u32
                            && coordinate.id.regime == crate::census::BackwardRegime::Ext
                    })
                    .unwrap();
                if coordinate.benchmark_encoding.is_err() {
                    continue;
                }
                let artifact = crate::generator::frozen_artifact_from_continuation_layer(
                    layer,
                    crate::generator::ProgramSchedule::Source,
                    true,
                )
                .unwrap_or_else(|error| panic!("{layout} Ext L{}: {error}", layer.layer));
                let atoms = decode_program(&artifact).unwrap().0;
                let compact =
                    encode_compact_program(&atoms, &artifact, CompactPolicy::DIRECT_PREFIX)
                        .unwrap_or_else(|error| {
                            panic!("{layout} Ext L{} compact: {error}", layer.layer)
                        });
                for seed in [0, 0x5a5a, u64::from(u32::MAX)] {
                    let lean = evaluate_windowed(HostProgram::Ext(layer), 3, seed).unwrap();
                    let legacy =
                        evaluate_windowed(HostProgram::Legacy(&artifact), 3, seed).unwrap();
                    let compact =
                        evaluate_windowed(HostProgram::Compact(&compact, &artifact), 3, seed)
                            .unwrap();
                    assert_eq!(lean, legacy, "{layout} Ext L{} seed={seed}", layer.layer);
                    assert_eq!(compact, legacy, "{layout} Ext L{} seed={seed}", layer.layer);
                }
                compared += 1;
            }
        }
        let expected = census
            .coordinates
            .iter()
            .filter(|coordinate| {
                coordinate.id.regime == crate::census::BackwardRegime::Ext
                    && coordinate.benchmark_encoding.is_ok()
            })
            .count();
        assert_eq!(compared, expected);
    }

    #[test]
    fn r0_c2_only_products_are_typed_as_not_benchmark_encodable() {
        let census: crate::census::CorpusCensusV1 = serde_json::from_slice(include_bytes!(
            "../artifacts/windowed_corpus_census_v1.json"
        ))
        .unwrap();
        let rows = census
            .coordinates
            .iter()
            .filter(|coordinate| coordinate.id.regime == crate::census::BackwardRegime::R0)
            .collect::<Vec<_>>();
        assert_eq!(rows.len(), 57);
        assert!(rows.iter().all(|coordinate| matches!(
            &coordinate.benchmark_encoding,
            Err(crate::census::CensusFailure { kind, .. })
                if kind == "r0_c2_only_semantics"
        )));
    }
}
