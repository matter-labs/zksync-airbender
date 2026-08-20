use std::collections::BTreeMap;

use field::{Field, PrimeField};

use crate::abi::{BF, E4};
use crate::accumulator_bounds::{outer_fold_bounds, CapacityDisposition};
use crate::accumulator_schedule::{SemanticSourceKey, SourceProjection};
use crate::r0_artifact::FrozenR0Coordinate;
use crate::r0_input::{factored_eq_weight, resolve_r0_coefficients, R0InputError, ResolvedR0Input};
use crate::r0_prototype_abi::{
    DedicatedSectionedProgram, R0_DEDICATED_GROUP_BF, R0_DEDICATED_GROUP_E4,
    R0_DEDICATED_HAS_PRODUCT, R0_DEDICATED_LINEAR_BF_PROCEDURAL, R0_DEDICATED_LINEAR_E4_WIDE,
    R0_DEDICATED_NEGATE_COEFFICIENT, R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_AB,
    R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_B, R0_DEDICATED_PRODUCT_E4_E4, R0_DEDICATED_REDUCE_AFTER,
};
use crate::r0_prototype_encoding::{
    GroupedAtom, R0EncodedProgram, R0Phase, R0PrototypeOp, R0PrototypeProgramEntry,
};
use crate::r0_prototype_manifest::{R0InnerFold, R0OuterFold, R0ProgramEncoding};
use crate::r0_reference::{quadratic_tensor_transform, tensor_index, R0ReferenceError};
use crate::wide_model::{red_wide_model, reduce_u96_raw, U96};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct R0AccumulatorPolicy {
    pub inner: R0InnerFold,
    pub outer: R0OuterFold,
}

impl R0AccumulatorPolicy {
    pub fn checked(
        encoding: R0ProgramEncoding,
        inner: R0InnerFold,
        outer: R0OuterFold,
    ) -> Result<Self, R0PrototypeAccumulatorError> {
        if inner == R0InnerFold::U64 && !encoding.grouped() {
            return Err(R0PrototypeAccumulatorError::InnerU64RequiresGroupedEncoding(encoding));
        }
        Ok(Self { inner, outer })
    }

    pub fn legal_for_encoding(encoding: R0ProgramEncoding) -> Vec<Self> {
        let inners: &[R0InnerFold] = if encoding.grouped() {
            &[R0InnerFold::Canonical, R0InnerFold::U64]
        } else {
            &[R0InnerFold::Canonical]
        };
        inners
            .iter()
            .flat_map(|&inner| {
                R0OuterFold::ALL
                    .into_iter()
                    .map(move |outer| Self { inner, outer })
            })
            .collect()
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct R0AccumulatorAudit {
    pub bf_wide_contributions: u64,
    pub e4_wide_contributions: u64,
    pub bf_boundary_reductions: u64,
    pub outer_intermediate_rebases: u64,
    pub inner_group_reductions: u64,
    pub inner_intermediate_rebases: u64,
    pub max_u96_high_word: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0PrototypeEvaluation {
    pub cells: [E4; 27],
    pub audit: R0AccumulatorAudit,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0PrototypeAccumulatorError {
    InnerU64RequiresGroupedEncoding(R0ProgramEncoding),
    InvalidProgram(String),
    InvalidField { class: u8 },
    InvalidCoefficient(u32),
    Capacity(String),
    Input(String),
    Reference(String),
}

impl core::fmt::Display for R0PrototypeAccumulatorError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for R0PrototypeAccumulatorError {}

impl From<R0InputError> for R0PrototypeAccumulatorError {
    fn from(error: R0InputError) -> Self {
        Self::Input(error.to_string())
    }
}

impl From<R0ReferenceError> for R0PrototypeAccumulatorError {
    fn from(error: R0ReferenceError) -> Self {
        Self::Reference(error.to_string())
    }
}

#[derive(Clone, Copy)]
enum TermValue {
    Bf(BF),
    E4(E4),
}

impl TermValue {
    fn into_e4(self) -> E4 {
        match self {
            Self::Bf(value) => E4::from_array_of_base([value, BF::ZERO, BF::ZERO, BF::ZERO]),
            Self::E4(value) => value,
        }
    }

    fn into_bf(self, class: u8) -> Result<BF, R0PrototypeAccumulatorError> {
        match self {
            Self::Bf(value) => Ok(value),
            Self::E4(_) => Err(R0PrototypeAccumulatorError::InvalidField { class }),
        }
    }
}

fn finite_point(value: usize) -> E4 {
    E4::from_array_of_base([
        BF::from_u32_with_reduction(value as u32),
        BF::ZERO,
        BF::ZERO,
        BF::ZERO,
    ])
}

fn affine(mut zero: E4, mut one: E4, point: E4) -> E4 {
    one.sub_assign(&zero);
    one.mul_assign(&point);
    zero.add_assign(&one);
    zero
}

fn source_at(
    coordinate: &FrozenR0Coordinate,
    input: &ResolvedR0Input,
    source: u32,
    row: usize,
    point: [E4; 3],
) -> Result<(E4, E4), R0PrototypeAccumulatorError> {
    let mut after_x2 = [E4::ZERO; 4];
    for bit0 in 0..2 {
        for bit1 in 0..2 {
            let corner = |bit2| {
                input.sources.read_bound_source(
                    &coordinate.binding,
                    source as usize,
                    (row << 3) | bit2 | (bit1 << 1) | (bit0 << 2),
                )
            };
            let zero = corner(0)?;
            let one = corner(1)?;
            after_x2[2 * bit0 + bit1] = affine(zero, one, point[2]);
        }
    }
    let at_point = affine(
        affine(after_x2[0], after_x2[1], point[1]),
        affine(after_x2[2], after_x2[3], point[1]),
        point[0],
    );

    let mut deltas = [E4::ZERO; 4];
    for bit0 in 0..2 {
        for bit1 in 0..2 {
            let zero = input.sources.read_bound_source(
                &coordinate.binding,
                source as usize,
                (row << 3) | (bit1 << 1) | (bit0 << 2),
            )?;
            let mut one = input.sources.read_bound_source(
                &coordinate.binding,
                source as usize,
                (row << 3) | 1 | (bit1 << 1) | (bit0 << 2),
            )?;
            one.sub_assign(&zero);
            deltas[2 * bit0 + bit1] = one;
        }
    }
    let delta = affine(
        affine(deltas[0], deltas[1], point[1]),
        affine(deltas[2], deltas[3], point[1]),
        point[0],
    );
    Ok((at_point, delta))
}

fn as_base(value: E4, class: u8) -> Result<BF, R0PrototypeAccumulatorError> {
    if value.c0.c1 != BF::ZERO || value.c1.c0 != BF::ZERO || value.c1.c1 != BF::ZERO {
        return Err(R0PrototypeAccumulatorError::InvalidField { class });
    }
    Ok(value.c0.c0)
}

fn source_value(
    coordinate: &FrozenR0Coordinate,
    input: &ResolvedR0Input,
    key: SemanticSourceKey,
    row: usize,
    point: [E4; 3],
) -> Result<E4, R0PrototypeAccumulatorError> {
    let (endpoint, delta) = source_at(coordinate, input, key.source, row, point)?;
    Ok(match key.projection {
        SourceProjection::Endpoint0 => endpoint,
        SourceProjection::Delta => delta,
    })
}

fn term_value(
    coordinate: &FrozenR0Coordinate,
    input: &ResolvedR0Input,
    operation: &R0PrototypeOp,
    row: usize,
    point: [E4; 3],
) -> Result<TermValue, R0PrototypeAccumulatorError> {
    let a = source_value(coordinate, input, operation.source_a, row, point)?;
    let b = operation
        .source_b
        .map(|source| source_value(coordinate, input, source, row, point))
        .transpose()?;
    match operation.term_class {
        0 => Ok(TermValue::Bf(as_base(a, 0)?)),
        1 => Ok(TermValue::E4(a)),
        2 => {
            let mut value = as_base(a, 2)?;
            value.mul_assign(&as_base(
                b.ok_or_else(|| {
                    R0PrototypeAccumulatorError::InvalidProgram(
                        "BF product is missing its second source".into(),
                    )
                })?,
                2,
            )?);
            let x2 = as_base(point[2], 2)?;
            value.mul_assign(&x2);
            value.mul_assign(&x2);
            Ok(TermValue::Bf(value))
        }
        3 => {
            let mut value = b.ok_or_else(|| {
                R0PrototypeAccumulatorError::InvalidProgram(
                    "BF/E4 product is missing its second source".into(),
                )
            })?;
            value.mul_assign(&E4::from_array_of_base([
                as_base(a, 3)?,
                BF::ZERO,
                BF::ZERO,
                BF::ZERO,
            ]));
            value.mul_assign(&point[2]);
            value.mul_assign(&point[2]);
            Ok(TermValue::E4(value))
        }
        4 => {
            let mut value = a;
            value.mul_assign(&b.ok_or_else(|| {
                R0PrototypeAccumulatorError::InvalidProgram(
                    "E4 product is missing its second source".into(),
                )
            })?);
            value.mul_assign(&point[2]);
            value.mul_assign(&point[2]);
            Ok(TermValue::E4(value))
        }
        class => Err(R0PrototypeAccumulatorError::InvalidProgram(format!(
            "invalid term class {class}"
        ))),
    }
}

fn coefficient(input: &ResolvedR0Input, id: u32) -> Result<E4, R0PrototypeAccumulatorError> {
    match id {
        0 => Ok(E4::ONE),
        1 => {
            let mut value = E4::ZERO;
            value.sub_assign(&E4::ONE);
            Ok(value)
        }
        _ => input
            .coefficient_bank
            .get((id - 2) as usize)
            .copied()
            .ok_or(R0PrototypeAccumulatorError::InvalidCoefficient(id)),
    }
}

fn raw_limbs(value: E4) -> [u32; 4] {
    [
        value.c0.c0.raw_u32_value(),
        value.c0.c1.raw_u32_value(),
        value.c1.c0.raw_u32_value(),
        value.c1.c1.raw_u32_value(),
    ]
}

fn e4_from_raw(limbs: [u32; 4]) -> E4 {
    E4::from_array_of_base(limbs.map(BF::from_reduced_raw_repr))
}

fn evaluate_linear_basis_wide(basis: [E4; 4], source: E4) -> E4 {
    let source = raw_limbs(source);
    let mut output = [U96::default(); 4];
    for (basis, scalar) in basis.into_iter().zip(source) {
        for (accumulator, coefficient) in output.iter_mut().zip(raw_limbs(basis)) {
            accumulator.add_product(coefficient, scalar);
        }
    }
    e4_from_raw(output.map(reduce_u96_raw))
}

struct U64Fold {
    values: [u64; 4],
    segment_len: u8,
}

impl U64Fold {
    fn new() -> Self {
        Self {
            values: [0; 4],
            segment_len: 0,
        }
    }

    fn add_product(&mut self, core: E4, value: BF) -> Result<bool, R0PrototypeAccumulatorError> {
        let rebased = if self.segment_len == 4 {
            let mont_r = u64::from(BF::ONE.raw_u32_value());
            for sum in &mut self.values {
                *sum = u64::from(red_wide_model(*sum))
                    .checked_mul(mont_r)
                    .ok_or_else(|| {
                        R0PrototypeAccumulatorError::Capacity("u64 rebase overflow".into())
                    })?;
            }
            self.segment_len = 0;
            true
        } else {
            false
        };
        let value = u64::from(value.raw_u32_value());
        for (sum, core) in self.values.iter_mut().zip(raw_limbs(core)) {
            *sum = sum
                .checked_add(u64::from(core) * value)
                .ok_or_else(|| R0PrototypeAccumulatorError::Capacity("u64 fold overflow".into()))?;
        }
        self.segment_len += 1;
        Ok(rebased)
    }

    fn reduce(self) -> E4 {
        e4_from_raw(self.values.map(red_wide_model))
    }
}

struct U96Fold {
    values: [U96; 4],
}

impl U96Fold {
    fn new() -> Self {
        Self {
            values: [U96::default(); 4],
        }
    }

    fn add_product(&mut self, core: E4, value: BF) -> u32 {
        let value = value.raw_u32_value();
        let mut high = 0;
        for (sum, core) in self.values.iter_mut().zip(raw_limbs(core)) {
            sum.add_product(core, value);
            high = high.max(sum.high_word());
        }
        high
    }

    fn reduce(self) -> E4 {
        e4_from_raw(self.values.map(reduce_u96_raw))
    }
}

enum OuterFold {
    Canonical(E4),
    U64(U64Fold),
    U96(U96Fold),
}

impl OuterFold {
    fn new(policy: R0OuterFold) -> Self {
        match policy {
            R0OuterFold::Canonical => Self::Canonical(E4::ZERO),
            R0OuterFold::U64 => Self::U64(U64Fold::new()),
            R0OuterFold::U96 => Self::U96(U96Fold::new()),
        }
    }

    fn add_bf(&mut self, core: E4, value: BF) -> Result<(bool, u32), R0PrototypeAccumulatorError> {
        Ok(match self {
            Self::Canonical(sum) => {
                let mut contribution = core;
                contribution.mul_assign(&E4::from_array_of_base([
                    value,
                    BF::ZERO,
                    BF::ZERO,
                    BF::ZERO,
                ]));
                sum.add_assign(&contribution);
                (false, 0)
            }
            Self::U64(sum) => (sum.add_product(core, value)?, 0),
            Self::U96(sum) => (false, sum.add_product(core, value)),
        })
    }

    fn finish(self) -> E4 {
        match self {
            Self::Canonical(sum) => sum,
            Self::U64(sum) => sum.reduce(),
            Self::U96(sum) => sum.reduce(),
        }
    }
}

fn grouped_atoms(entry: &R0PrototypeProgramEntry) -> Option<&[GroupedAtom]> {
    match &entry.encoded {
        R0EncodedProgram::GroupedSlot(program) => Some(&program.atoms),
        R0EncodedProgram::GroupedDirect(program) => Some(&program.atoms),
        _ => None,
    }
}

fn grouped_cores(
    coordinate: &FrozenR0Coordinate,
    input: &ResolvedR0Input,
    entry: &R0PrototypeProgramEntry,
) -> Result<BTreeMap<u32, (E4, Vec<u32>)>, R0PrototypeAccumulatorError> {
    let mut result = BTreeMap::new();
    let Some(atoms) = grouped_atoms(entry) else {
        return Ok(result);
    };
    for atom in atoms {
        if let GroupedAtom::Group {
            group_id,
            core,
            members,
            ..
        } = atom
        {
            let core = resolve_r0_coefficients(
                core::slice::from_ref(core),
                &input.identity.challenge_bases,
            )?
            .into_iter()
            .next()
            .ok_or_else(|| {
                R0PrototypeAccumulatorError::InvalidProgram(format!(
                    "group {group_id} has no resolved core in {}:{}",
                    coordinate.circuit, coordinate.layer
                ))
            })?;
            if result
                .insert(
                    *group_id,
                    (
                        core,
                        members.iter().map(|member| member.immediate).collect(),
                    ),
                )
                .is_some()
            {
                return Err(R0PrototypeAccumulatorError::InvalidProgram(format!(
                    "duplicate group {group_id}"
                )));
            }
        }
    }
    Ok(result)
}

fn static_audit(
    entry: &R0PrototypeProgramEntry,
    policy: R0AccumulatorPolicy,
) -> Result<R0AccumulatorAudit, R0PrototypeAccumulatorError> {
    let mut contributions = 0u64;
    let mut inner_groups = 0u64;
    let mut inner_rebases = 0u64;
    let mut cursor = 0;
    while cursor < entry.operations.len() && entry.operations[cursor].phase == R0Phase::Bf {
        let operation = &entry.operations[cursor];
        if policy.inner == R0InnerFold::U64 {
            if let Some(group) = operation.group_id {
                let start = cursor;
                while cursor < entry.operations.len()
                    && entry.operations[cursor].phase == R0Phase::Bf
                    && entry.operations[cursor].group_id == Some(group)
                {
                    cursor += 1;
                }
                let members = (cursor - start) as u64;
                if members < 2 {
                    return Err(R0PrototypeAccumulatorError::InvalidProgram(format!(
                        "inner-u64 group {group} has {members} member"
                    )));
                }
                contributions += 1;
                inner_groups += 1;
                inner_rebases += (members - 1) / 4;
                continue;
            }
        }
        contributions += 1;
        cursor += 1;
    }
    if entry.operations[cursor..]
        .iter()
        .any(|operation| operation.phase == R0Phase::Bf)
    {
        return Err(R0PrototypeAccumulatorError::InvalidProgram(
            "BF operation follows the E4 boundary".into(),
        ));
    }
    let [u64_bound, u96_bound] = outer_fold_bounds(contributions);
    let selected = match policy.outer {
        R0OuterFold::Canonical => None,
        R0OuterFold::U64 => Some(u64_bound),
        R0OuterFold::U96 => Some(u96_bound),
    };
    if let Some(bound) = selected {
        if !matches!(bound.disposition, CapacityDisposition::Feasible(_)) {
            return Err(R0PrototypeAccumulatorError::Capacity(format!(
                "outer {:?} bound is infeasible for {contributions} contributions",
                policy.outer
            )));
        }
    }
    Ok(R0AccumulatorAudit {
        bf_wide_contributions: if policy.outer == R0OuterFold::Canonical {
            0
        } else {
            contributions
        },
        e4_wide_contributions: 0,
        bf_boundary_reductions: u64::from(
            policy.outer != R0OuterFold::Canonical && contributions != 0,
        ),
        outer_intermediate_rebases: if policy.outer == R0OuterFold::U64 {
            contributions.saturating_sub(1) / 4
        } else {
            0
        },
        inner_group_reductions: inner_groups,
        inner_intermediate_rebases: inner_rebases,
        max_u96_high_word: 0,
    })
}

fn evaluate_point(
    coordinate: &FrozenR0Coordinate,
    entry: &R0PrototypeProgramEntry,
    input: &ResolvedR0Input,
    policy: R0AccumulatorPolicy,
    row: usize,
    point: [E4; 3],
    group_cores: &BTreeMap<u32, (E4, Vec<u32>)>,
) -> Result<(E4, u32), R0PrototypeAccumulatorError> {
    let mut outer = OuterFold::new(policy.outer);
    let mut max_u96_high_word = 0;
    let mut cursor = 0;
    while cursor < entry.operations.len() && entry.operations[cursor].phase == R0Phase::Bf {
        let operation = &entry.operations[cursor];
        if policy.inner == R0InnerFold::U64 {
            if let Some(group_id) = operation.group_id {
                let (core, immediates) = group_cores.get(&group_id).ok_or_else(|| {
                    R0PrototypeAccumulatorError::InvalidProgram(format!(
                        "missing core for group {group_id}"
                    ))
                })?;
                let mut inner = U64Fold::new();
                let mut member = 0usize;
                while cursor < entry.operations.len()
                    && entry.operations[cursor].phase == R0Phase::Bf
                    && entry.operations[cursor].group_id == Some(group_id)
                {
                    let operation = &entry.operations[cursor];
                    let term = term_value(coordinate, input, operation, row, point)?
                        .into_bf(operation.term_class)?;
                    let immediate =
                        BF::from_u32_with_reduction(*immediates.get(member).ok_or_else(|| {
                            R0PrototypeAccumulatorError::InvalidProgram(format!(
                                "group {group_id} member {member} has no immediate"
                            ))
                        })?);
                    inner.add_product(
                        E4::from_array_of_base([immediate, BF::ZERO, BF::ZERO, BF::ZERO]),
                        term,
                    )?;
                    cursor += 1;
                    member += 1;
                }
                if member != immediates.len() || member < 2 {
                    return Err(R0PrototypeAccumulatorError::InvalidProgram(format!(
                        "group {group_id} has {member} operations and {} immediates",
                        immediates.len()
                    )));
                }
                let value = inner.reduce().c0.c0;
                let (_, high) = outer.add_bf(*core, value)?;
                max_u96_high_word = max_u96_high_word.max(high);
                continue;
            }
        }
        let value =
            term_value(coordinate, input, operation, row, point)?.into_bf(operation.term_class)?;
        let (_, high) = outer.add_bf(coefficient(input, operation.coefficient_id)?, value)?;
        max_u96_high_word = max_u96_high_word.max(high);
        cursor += 1;
    }
    let mut result = outer.finish();
    for operation in &entry.operations[cursor..] {
        if operation.phase != R0Phase::E4 {
            return Err(R0PrototypeAccumulatorError::InvalidProgram(
                "BF operation follows the E4 boundary".into(),
            ));
        }
        let mut value = term_value(coordinate, input, operation, row, point)?.into_e4();
        value.mul_assign(&coefficient(input, operation.coefficient_id)?);
        result.add_assign(&value);
    }
    Ok((result, max_u96_high_word))
}

fn sectioned_source_key(
    coordinate: &FrozenR0Coordinate,
    packed: u16,
    projection: SourceProjection,
) -> Result<SemanticSourceKey, R0PrototypeAccumulatorError> {
    let window = packed >> 7;
    let column = packed & 0x7f;
    let source = coordinate
        .binding
        .source_slots
        .iter()
        .position(|source| u16::from(source.window) == window && u16::from(source.column) == column)
        .ok_or_else(|| {
            R0PrototypeAccumulatorError::InvalidProgram(format!(
                "sectioned packed source {packed:#06x} is absent"
            ))
        })?;
    Ok(SemanticSourceKey {
        source: source as u32,
        projection,
    })
}

fn sectioned_procedural_key(
    coordinate: &FrozenR0Coordinate,
    kind: u16,
    projection: SourceProjection,
) -> Result<SemanticSourceKey, R0PrototypeAccumulatorError> {
    let source = coordinate
        .binding
        .source_slots
        .iter()
        .position(|source| {
            coordinate.binding.windows[usize::from(source.window)].procedural_kind()
                == u8::try_from(kind).ok()
        })
        .ok_or_else(|| {
            R0PrototypeAccumulatorError::InvalidProgram(format!(
                "sectioned procedural source kind {kind} is absent"
            ))
        })?;
    Ok(SemanticSourceKey {
        source: source as u32,
        projection,
    })
}

fn sectioned_term(
    coordinate: &FrozenR0Coordinate,
    input: &ResolvedR0Input,
    class: u16,
    source_a: u16,
    source_b: u16,
    row: usize,
    point: [E4; 3],
) -> Result<TermValue, R0PrototypeAccumulatorError> {
    let packed = |source, projection| sectioned_source_key(coordinate, source, projection);
    let procedural = |kind, projection| sectioned_procedural_key(coordinate, kind, projection);
    let value = |key| source_value(coordinate, input, key, row, point);
    let x2 = as_base(point[2], class as u8)?;
    match class {
        0 => Ok(TermValue::Bf(as_base(
            value(packed(source_a, SourceProjection::Endpoint0)?)?,
            0,
        )?)),
        R0_DEDICATED_LINEAR_BF_PROCEDURAL => Ok(TermValue::Bf(as_base(
            value(procedural(source_a, SourceProjection::Endpoint0)?)?,
            0,
        )?)),
        2 | R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_B | R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_AB => {
            let keys = match class {
                2 => (
                    packed(source_a, SourceProjection::Delta)?,
                    packed(source_b, SourceProjection::Delta)?,
                ),
                R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_B => (
                    packed(source_a, SourceProjection::Delta)?,
                    procedural(source_b, SourceProjection::Delta)?,
                ),
                R0_DEDICATED_PRODUCT_BF_BF_PROCEDURAL_AB => (
                    procedural(source_a, SourceProjection::Delta)?,
                    procedural(source_b, SourceProjection::Delta)?,
                ),
                _ => unreachable!(),
            };
            let mut result = as_base(value(keys.0)?, 2)?;
            result.mul_assign(&as_base(value(keys.1)?, 2)?);
            result.mul_assign(&x2);
            result.mul_assign(&x2);
            Ok(TermValue::Bf(result))
        }
        3 => {
            let mut result = value(packed(source_b, SourceProjection::Delta)?)?;
            result.mul_assign(&E4::from_array_of_base([
                as_base(value(packed(source_a, SourceProjection::Delta)?)?, 3)?,
                BF::ZERO,
                BF::ZERO,
                BF::ZERO,
            ]));
            result.mul_assign(&point[2]);
            result.mul_assign(&point[2]);
            Ok(TermValue::E4(result))
        }
        R0_DEDICATED_PRODUCT_E4_E4 => {
            let mut result = value(packed(source_a, SourceProjection::Delta)?)?;
            result.mul_assign(&value(packed(source_b, SourceProjection::Delta)?)?);
            result.mul_assign(&point[2]);
            result.mul_assign(&point[2]);
            Ok(TermValue::E4(result))
        }
        _ => Err(R0PrototypeAccumulatorError::InvalidProgram(format!(
            "invalid sectioned term class {class}"
        ))),
    }
}

fn sectioned_coefficient(bank: &[E4], encoded: u16) -> Result<E4, R0PrototypeAccumulatorError> {
    let negate = encoded & R0_DEDICATED_NEGATE_COEFFICIENT != 0;
    let id = encoded & !R0_DEDICATED_NEGATE_COEFFICIENT;
    let mut value = match id {
        0 => E4::ONE,
        1 => {
            let mut value = E4::ONE;
            value.negate();
            value
        }
        _ => bank.get(usize::from(id - 2)).copied().ok_or(
            R0PrototypeAccumulatorError::InvalidCoefficient(u32::from(id)),
        )?,
    };
    if negate {
        value.negate();
    }
    Ok(value)
}

fn sectioned_factor(
    program: &DedicatedSectionedProgram,
    encoded: u16,
) -> Result<BF, R0PrototypeAccumulatorError> {
    let id = encoded & !R0_DEDICATED_REDUCE_AFTER;
    Ok(match id {
        0 => BF::ONE,
        1 => {
            let mut value = BF::ONE;
            value.negate();
            value
        }
        _ => BF::from_reduced_raw_repr(*program.immediates.get(usize::from(id - 2)).ok_or_else(
            || {
                R0PrototypeAccumulatorError::InvalidProgram(format!(
                    "sectioned immediate {id} is absent"
                ))
            },
        )?),
    })
}

fn evaluate_sectioned_point(
    coordinate: &FrozenR0Coordinate,
    input: &ResolvedR0Input,
    program: &DedicatedSectionedProgram,
    bank: &[E4],
    row: usize,
    point: [E4; 3],
) -> Result<E4, R0PrototypeAccumulatorError> {
    let record = |pc: usize| -> Result<&[u16], R0PrototypeAccumulatorError> {
        program.words.get(4 * pc..4 * pc + 4).ok_or_else(|| {
            R0PrototypeAccumulatorError::InvalidProgram(format!("sectioned record {pc} is absent"))
        })
    };
    let mut result = E4::ZERO;
    let mut pc = 0usize;
    let bf_end = program.sections[0] as usize;
    while pc < bf_end {
        let head = record(pc)?;
        pc += 1;
        if head[0] == R0_DEDICATED_GROUP_BF {
            let members = usize::from(head[2]);
            let product_prefix = usize::from(head[3] & !R0_DEDICATED_HAS_PRODUCT);
            if product_prefix == 0 || product_prefix > members || pc + members > bf_end {
                return Err(R0PrototypeAccumulatorError::InvalidProgram(
                    "invalid sectioned BF group bounds".to_owned(),
                ));
            }
            let mut inner = BF::ZERO;
            for _ in 0..members {
                let member = record(pc)?;
                let value = sectioned_term(
                    coordinate, input, member[0], member[2], member[3], row, point,
                )?
                .into_bf(member[0] as u8)?;
                let mut contribution = value;
                contribution.mul_assign(&sectioned_factor(program, member[1])?);
                inner.add_assign(&contribution);
                pc += 1;
            }
            let mut contribution = E4::from_array_of_base([inner, BF::ZERO, BF::ZERO, BF::ZERO]);
            contribution.mul_assign(&sectioned_coefficient(bank, head[1])?);
            result.add_assign(&contribution);
        } else {
            let value = sectioned_term(coordinate, input, head[0], head[2], head[3], row, point)?
                .into_bf(head[0] as u8)?;
            let mut contribution = E4::from_array_of_base([value, BF::ZERO, BF::ZERO, BF::ZERO]);
            contribution.mul_assign(&sectioned_coefficient(bank, head[1])?);
            result.add_assign(&contribution);
        }
    }

    let linear_end = program.sections[1] as usize;
    while pc < linear_end {
        let row_record = record(pc)?;
        if row_record[0] != R0_DEDICATED_LINEAR_E4_WIDE {
            return Err(R0PrototypeAccumulatorError::InvalidProgram(format!(
                "sectioned linear record has class {}",
                row_record[0]
            )));
        }
        let source = source_value(
            coordinate,
            input,
            sectioned_source_key(coordinate, row_record[2], SourceProjection::Endpoint0)?,
            row,
            point,
        )?;
        let limbs = [source.c0.c0, source.c0.c1, source.c1.c0, source.c1.c1];
        for (limb, scalar) in limbs.into_iter().enumerate() {
            let mut contribution = sectioned_coefficient(bank, row_record[1] + limb as u16)?;
            contribution.mul_assign(&E4::from_array_of_base([
                scalar,
                BF::ZERO,
                BF::ZERO,
                BF::ZERO,
            ]));
            result.add_assign(&contribution);
        }
        pc += 1;
    }

    let singleton_end = program.sections[2] as usize;
    while pc < singleton_end {
        let row_record = record(pc)?;
        if !matches!(row_record[0], 3 | R0_DEDICATED_PRODUCT_E4_E4) {
            return Err(R0PrototypeAccumulatorError::InvalidProgram(format!(
                "sectioned E4 singleton has class {}",
                row_record[0]
            )));
        }
        let mut contribution = sectioned_term(
            coordinate,
            input,
            row_record[0],
            row_record[2],
            row_record[3],
            row,
            point,
        )?
        .into_e4();
        contribution.mul_assign(&sectioned_coefficient(bank, row_record[1])?);
        result.add_assign(&contribution);
        pc += 1;
    }

    let pair_end = program.sections[3] as usize;
    while pc < pair_end {
        let head = record(pc)?;
        pc += 1;
        if head[0] != R0_DEDICATED_GROUP_E4 || pc + 2 > pair_end {
            return Err(R0PrototypeAccumulatorError::InvalidProgram(
                "invalid fixed E4 pair bounds".to_owned(),
            ));
        }
        let mut pair = E4::ZERO;
        for _ in 0..2 {
            let member = record(pc)?;
            let mut contribution = sectioned_term(
                coordinate, input, member[0], member[2], member[3], row, point,
            )?
            .into_e4();
            contribution.mul_assign(&E4::from_array_of_base([
                sectioned_factor(program, member[1])?,
                BF::ZERO,
                BF::ZERO,
                BF::ZERO,
            ]));
            pair.add_assign(&contribution);
            pc += 1;
        }
        pair.mul_assign(&sectioned_coefficient(bank, head[1])?);
        result.add_assign(&pair);
    }
    if pc != pair_end {
        return Err(R0PrototypeAccumulatorError::InvalidProgram(
            "sectioned program did not end at the pair boundary".to_owned(),
        ));
    }
    Ok(result)
}

pub(crate) fn evaluate_sectioned_program(
    coordinate: &FrozenR0Coordinate,
    input: &ResolvedR0Input,
    program: &DedicatedSectionedProgram,
    bank: &[E4],
) -> Result<R0PrototypeEvaluation, R0PrototypeAccumulatorError> {
    if coordinate.circuit != input.identity.circuit || coordinate.layer != input.identity.layer {
        return Err(R0PrototypeAccumulatorError::InvalidProgram(
            "coordinate and input identity differ".into(),
        ));
    }
    let rows = 1usize
        .checked_shl(input.identity.log_trace.checked_sub(3).ok_or_else(|| {
            R0PrototypeAccumulatorError::InvalidProgram("log trace is below R0 depth".into())
        })?)
        .ok_or_else(|| R0PrototypeAccumulatorError::Capacity("row count overflow".into()))?;
    let mut finite = [E4::ZERO; 27];
    for x0 in 0..3 {
        for x1 in 0..3 {
            for x2 in 0..3 {
                let point = [finite_point(x0), finite_point(x1), finite_point(x2)];
                let mut sum = E4::ZERO;
                for row in 0..rows {
                    let mut value =
                        evaluate_sectioned_point(coordinate, input, program, bank, row, point)?;
                    value.mul_assign(&factored_eq_weight(row, &input.eq_tables)?);
                    sum.add_assign(&value);
                }
                finite[tensor_index(x0, x1, x2)] = sum;
            }
        }
    }
    Ok(R0PrototypeEvaluation {
        cells: quadratic_tensor_transform(finite)?,
        audit: R0AccumulatorAudit::default(),
    })
}

pub fn evaluate_prototype_program(
    coordinate: &FrozenR0Coordinate,
    entry: &R0PrototypeProgramEntry,
    input: &ResolvedR0Input,
    policy: R0AccumulatorPolicy,
) -> Result<R0PrototypeEvaluation, R0PrototypeAccumulatorError> {
    R0AccumulatorPolicy::checked(entry.encoding, policy.inner, policy.outer)?;
    if coordinate.circuit != input.identity.circuit || coordinate.layer != input.identity.layer {
        return Err(R0PrototypeAccumulatorError::InvalidProgram(
            "coordinate and input identity differ".into(),
        ));
    }
    let rows = 1usize
        .checked_shl(input.identity.log_trace.checked_sub(3).ok_or_else(|| {
            R0PrototypeAccumulatorError::InvalidProgram("log trace is below R0 depth".into())
        })?)
        .ok_or_else(|| R0PrototypeAccumulatorError::Capacity("row count overflow".into()))?;
    let group_cores = grouped_cores(coordinate, input, entry)?;
    let mut audit = static_audit(entry, policy)?;
    let mut finite = [E4::ZERO; 27];
    for x0 in 0..3 {
        for x1 in 0..3 {
            for x2 in 0..3 {
                let point = [finite_point(x0), finite_point(x1), finite_point(x2)];
                let mut sum = E4::ZERO;
                for row in 0..rows {
                    let (mut value, high) =
                        evaluate_point(coordinate, entry, input, policy, row, point, &group_cores)?;
                    audit.max_u96_high_word = audit.max_u96_high_word.max(high);
                    value.mul_assign(&factored_eq_weight(row, &input.eq_tables)?);
                    sum.add_assign(&value);
                }
                finite[tensor_index(x0, x1, x2)] = sum;
            }
        }
    }
    if audit.max_u96_high_word >= BF::ORDER {
        return Err(R0PrototypeAccumulatorError::Capacity(format!(
            "u96 high word {} exceeds the reducer proof",
            audit.max_u96_high_word
        )));
    }
    Ok(R0PrototypeEvaluation {
        cells: quadratic_tensor_transform(finite)?,
        audit,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use field::{Field, PrimeField};
    use gpu_gkr_compiler::backward::analyze_coeff_grouping;

    use crate::abi::{BF, E4};
    use crate::accumulator_schedule::build_schedule_views;
    use crate::census::compile_corpus;
    use crate::r0_artifact::{decode_r0_bundle, R0_CORPUS_BYTES};
    use crate::r0_input::build_r0_input_with_layer;
    use crate::r0_prototype_encoding::build_r0_prototype_program_set;
    use crate::r0_prototype_manifest::{
        build_r0_prototype_manifest, R0InnerFold, R0OuterFold, R0ProgramEncoding,
    };
    use crate::r0_reference::evaluate_compiled_r0_tensor;

    use super::{evaluate_prototype_program, R0AccumulatorPolicy, R0PrototypeAccumulatorError};

    #[test]
    fn cpu_u64_fold_rebases_only_before_each_fifth_product() {
        let core = E4::from_array_of_base([
            BF::from_reduced_raw_repr(BF::ORDER - 1),
            BF::from_reduced_raw_repr(BF::ORDER - 2),
            BF::from_reduced_raw_repr(BF::ORDER - 3),
            BF::from_reduced_raw_repr(BF::ORDER - 4),
        ]);
        let mut fold = super::U64Fold::new();
        let mut canonical = E4::ZERO;
        let mut rebases = Vec::new();
        for index in 0..9 {
            let value = BF::from_reduced_raw_repr(BF::ORDER - 1 - index);
            if fold.add_product(core, value).unwrap() {
                rebases.push(index);
            }
            let mut contribution = core;
            contribution.mul_assign(&E4::from_array_of_base([
                value,
                BF::ZERO,
                BF::ZERO,
                BF::ZERO,
            ]));
            canonical.add_assign(&contribution);
        }
        assert_eq!(rebases, [4, 8]);
        assert_eq!(fold.reduce(), canonical);
    }

    #[test]
    fn cpu_sectioned_linear_wide_update_matches_e4_multiplication() {
        let cases = [
            (
                E4::from_array_of_base([
                    BF::from_u32_with_reduction(3),
                    BF::from_u32_with_reduction(5),
                    BF::from_u32_with_reduction(7),
                    BF::from_u32_with_reduction(11),
                ]),
                E4::from_array_of_base([
                    BF::from_u32_with_reduction(13),
                    BF::from_u32_with_reduction(17),
                    BF::from_u32_with_reduction(19),
                    BF::from_u32_with_reduction(23),
                ]),
            ),
            (
                E4::from_array_of_base([
                    BF::from_reduced_raw_repr(BF::ORDER - 1),
                    BF::from_reduced_raw_repr(BF::ORDER - 2),
                    BF::from_reduced_raw_repr(BF::ORDER - 3),
                    BF::from_reduced_raw_repr(BF::ORDER - 4),
                ]),
                E4::from_array_of_base([
                    BF::from_reduced_raw_repr(BF::ORDER - 5),
                    BF::from_reduced_raw_repr(BF::ORDER - 6),
                    BF::from_reduced_raw_repr(BF::ORDER - 7),
                    BF::from_reduced_raw_repr(BF::ORDER - 8),
                ]),
            ),
            (
                E4::from_array_of_base([
                    BF::ZERO,
                    BF::ONE,
                    BF::from_u32_with_reduction(29),
                    BF::from_u32_with_reduction(31),
                ]),
                E4::from_array_of_base([
                    BF::from_u32_with_reduction(37),
                    BF::ZERO,
                    BF::ONE,
                    BF::from_u32_with_reduction(41),
                ]),
            ),
        ];
        for (core, source) in cases {
            let basis = core::array::from_fn(|limb| {
                let mut element = [BF::ZERO; 4];
                element[limb] = BF::ONE;
                let mut value = core;
                value.mul_assign(&E4::from_array_of_base(element));
                value
            });
            let mut expected = core;
            expected.mul_assign(&source);
            assert_eq!(super::evaluate_linear_basis_wide(basis, source), expected);
        }
    }

    #[test]
    fn cpu_u96_fold_spans_the_full_bf_phase_without_an_intermediate_rebase() {
        let core = E4::from_array_of_base([
            BF::from_u32_with_reduction(13),
            BF::from_u32_with_reduction(17),
            BF::from_u32_with_reduction(19),
            BF::from_u32_with_reduction(23),
        ]);
        let mut fold = super::U96Fold::new();
        let mut canonical = E4::ZERO;
        let mut maximum_high = 0;
        for index in 0..1_442 {
            let value = BF::from_u32_with_reduction(1 + (index % 127));
            maximum_high = maximum_high.max(fold.add_product(core, value));
            let mut contribution = core;
            contribution.mul_assign(&E4::from_array_of_base([
                value,
                BF::ZERO,
                BF::ZERO,
                BF::ZERO,
            ]));
            canonical.add_assign(&contribution);
        }
        assert!(maximum_high < BF::ORDER);
        assert_eq!(fold.reduce(), canonical);
    }

    #[test]
    fn cpu_accumulator_policy_surface_matches_the_manifest_exactly() {
        let manifest = build_r0_prototype_manifest().unwrap();
        let modeled = R0ProgramEncoding::ALL
            .into_iter()
            .flat_map(|encoding| {
                R0AccumulatorPolicy::legal_for_encoding(encoding)
                    .into_iter()
                    .map(move |policy| (encoding, policy.inner, policy.outer))
            })
            .collect::<BTreeSet<_>>();
        let manifested = manifest
            .translation_units
            .into_iter()
            .map(|unit| (unit.encoding, unit.inner, unit.outer))
            .collect::<BTreeSet<_>>();
        assert_eq!(modeled, manifested);
        assert_eq!(modeled.len(), 30);

        assert!(matches!(
            R0AccumulatorPolicy::checked(
                R0ProgramEncoding::SplitFixedDirect,
                R0InnerFold::U64,
                R0OuterFold::Canonical,
            ),
            Err(
                R0PrototypeAccumulatorError::InnerU64RequiresGroupedEncoding(
                    R0ProgramEncoding::SplitFixedDirect
                )
            )
        ));
    }

    #[test]
    fn cpu_all_r0_accumulator_policies_match_compiled_r0_at_log3_three_seeds() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinates = bundle
            .coordinates
            .iter()
            .map(|coordinate| ((coordinate.circuit.as_str(), coordinate.layer), coordinate))
            .collect::<std::collections::BTreeMap<_, _>>();
        let corpus = compile_corpus().unwrap();
        let mut evaluated = 0usize;
        for layer in &corpus.layers {
            let coordinate = coordinates[&(layer.circuit.as_str(), layer.layer as u32)];
            let grouping = analyze_coeff_grouping(&layer.r0.coefficients).unwrap();
            let schedules =
                build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &grouping).unwrap();
            let programs = build_r0_prototype_program_set(
                coordinate,
                &layer.r0.coefficients,
                &schedules,
                &grouping,
            )
            .unwrap();
            for seed in [0, 1, 2] {
                let input =
                    build_r0_input_with_layer(coordinate, &layer.canonical, 3, seed).unwrap();
                let expected = evaluate_compiled_r0_tensor(&layer.r0, &input).unwrap();
                for entry in &programs.entries {
                    for policy in R0AccumulatorPolicy::legal_for_encoding(entry.encoding) {
                        let evaluation =
                            evaluate_prototype_program(coordinate, entry, &input, policy).unwrap();
                        assert_eq!(
                            evaluation.cells,
                            expected,
                            "{}:{} seed={seed} encoding={} inner={:?} outer={:?}",
                            layer.circuit,
                            layer.layer,
                            entry.encoding.as_str(),
                            policy.inner,
                            policy.outer,
                        );
                        assert_eq!(evaluation.audit.e4_wide_contributions, 0);
                        assert_eq!(
                            evaluation.audit.bf_boundary_reductions,
                            u64::from(
                                policy.outer != R0OuterFold::Canonical
                                    && evaluation.audit.bf_wide_contributions != 0
                            )
                        );
                        evaluated += 1;
                    }
                }
            }
        }
        assert_eq!(evaluated, 57 * 3 * 30);
    }

    #[test]
    fn cpu_sectioned_wire_matches_canonical_r0_all_coordinates() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinates = bundle
            .coordinates
            .iter()
            .map(|coordinate| ((coordinate.circuit.as_str(), coordinate.layer), coordinate))
            .collect::<std::collections::BTreeMap<_, _>>();
        let corpus = compile_corpus().unwrap();
        let mut evaluated = 0usize;
        for layer in &corpus.layers {
            let coordinate = coordinates[&(layer.circuit.as_str(), layer.layer as u32)];
            let grouping = analyze_coeff_grouping(&layer.r0.coefficients).unwrap();
            let schedules =
                build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &grouping).unwrap();
            let programs = build_r0_prototype_program_set(
                coordinate,
                &layer.r0.coefficients,
                &schedules,
                &grouping,
            )
            .unwrap();
            let crate::r0_prototype_encoding::R0EncodedProgram::GroupedSlot(grouped) = &programs
                .get(R0ProgramEncoding::GroupedSlot)
                .unwrap()
                .encoded
            else {
                unreachable!()
            };
            let sectioned =
                crate::r0_prototype_abi::lower_dedicated_sections(coordinate, grouped).unwrap();
            for log_trace in [3, 12] {
                for seed in [0, 1] {
                    let input =
                        build_r0_input_with_layer(coordinate, &layer.canonical, log_trace, seed)
                            .unwrap();
                    let bank = crate::r0_prototype_harness::resolve_dedicated_coefficient_plans(
                        &sectioned.coefficient_plans,
                        &input.identity.challenge_bases,
                    )
                    .unwrap();
                    let expected = crate::r0_reference::evaluate_canonical_r0_convention(
                        &layer.canonical,
                        &coordinate.binding,
                        &input,
                    )
                    .unwrap();
                    let actual =
                        super::evaluate_sectioned_program(coordinate, &input, &sectioned, &bank)
                            .unwrap();
                    assert_eq!(
                        actual.cells, expected,
                        "{}:{} log={log_trace} seed={seed}",
                        layer.circuit, layer.layer
                    );
                    evaluated += 1;
                }
            }
        }
        assert_eq!(evaluated, 57 * 2 * 2);
    }
}
