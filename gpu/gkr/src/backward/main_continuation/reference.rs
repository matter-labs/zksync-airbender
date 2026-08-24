//! CPU reference for one main-layer continuation window.
//!
//! This follows the production continuation descriptor rather than the
//! upstream prover's private window implementation. Source columns are dense
//! by semantic `SourceId`; each row supplies the eight Boolean corners in
//! low-bit-first order.

use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::{CoefficientRecipeId, ImmediateId, LeanTerm, MainContinuationWindowProgram};

use crate::upstream::{Field, FieldExtension, PrimeField};

/// Input-shape or descriptor inconsistency detected by the CPU continuation
/// reference before evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContinuationWindowReferenceError {
    SourceCount {
        expected: usize,
        actual: usize,
    },
    SourceRowCount {
        source: usize,
        expected: usize,
        actual: usize,
    },
    EmptySuffixEq,
    NonCanonicalPublication {
        source: usize,
        semantic_id: u32,
        publish_column: u16,
    },
    CoefficientOutOfRange {
        id: u32,
        bank_len: usize,
    },
    ImmediateOutOfRange {
        id: u16,
        table_len: usize,
    },
    SourceOutOfRange {
        id: u16,
        source_count: usize,
    },
    UnsupportedClass {
        class: u8,
    },
}

impl core::fmt::Display for ContinuationWindowReferenceError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for ContinuationWindowReferenceError {}

#[inline]
fn cell_index(x2_low: usize, x1: usize, x0_high: usize) -> usize {
    9 * x2_low + 3 * x1 + x0_high
}

#[inline]
fn boolean_cell(cell: usize) -> bool {
    cell / 9 < 2 && (cell / 3) % 3 < 2 && cell % 3 < 2
}

fn difference_extend(corners: [E4; 8]) -> [E4; 27] {
    let mut grid = [E4::ZERO; 27];
    for (corner, value) in corners.into_iter().enumerate() {
        grid[cell_index(corner & 1, (corner >> 1) & 1, (corner >> 2) & 1)] = value;
    }

    // x0_high has stride one, x1 stride three, and x2_low stride nine.
    for x2 in 0..2 {
        for x1 in 0..2 {
            let base = cell_index(x2, x1, 0);
            let mut delta = grid[base + 1];
            delta.sub_assign(&grid[base]);
            grid[base + 2] = delta;
        }
        for x0 in 0..3 {
            let base = cell_index(x2, 0, x0);
            let mut delta = grid[base + 3];
            delta.sub_assign(&grid[base]);
            grid[base + 6] = delta;
        }
    }
    for lower_cell in 0..9 {
        let mut delta = grid[9 + lower_cell];
        delta.sub_assign(&grid[lower_cell]);
        grid[18 + lower_cell] = delta;
    }
    grid
}

fn coefficient(
    bank: &[E4],
    id: CoefficientRecipeId,
) -> Result<E4, ContinuationWindowReferenceError> {
    bank.get(id.0 as usize).copied().ok_or(
        ContinuationWindowReferenceError::CoefficientOutOfRange {
            id: id.0,
            bank_len: bank.len(),
        },
    )
}

fn immediate(
    program: &MainContinuationWindowProgram,
    id: ImmediateId,
) -> Result<E4, ContinuationWindowReferenceError> {
    if id == ImmediateId::ONE {
        return Ok(E4::ONE);
    }
    if id == ImmediateId::NEG_ONE {
        let mut value = E4::ONE;
        value.negate();
        return Ok(value);
    }
    let value = *program
        .immediates
        .get(
            id.bank_index()
                .ok_or(ContinuationWindowReferenceError::ImmediateOutOfRange {
                    id: id.0,
                    table_len: program.immediates.len(),
                })?,
        )
        .ok_or(ContinuationWindowReferenceError::ImmediateOutOfRange {
            id: id.0,
            table_len: program.immediates.len(),
        })?;
    Ok(<E4 as FieldExtension<BF>>::from_base(
        BF::from_u32_with_reduction(value),
    ))
}

fn source_grid(grids: &[[E4; 27]], id: u16) -> Result<&[E4; 27], ContinuationWindowReferenceError> {
    grids
        .get(usize::from(id))
        .ok_or(ContinuationWindowReferenceError::SourceOutOfRange {
            id,
            source_count: grids.len(),
        })
}

fn unscaled_term(
    record: &LeanTerm,
    grids: &[[E4; 27]],
    cell: usize,
) -> Result<E4, ContinuationWindowReferenceError> {
    match record.class {
        0 => {
            if boolean_cell(cell) {
                Ok(source_grid(grids, record.source_a)?[cell])
            } else {
                Ok(E4::ZERO)
            }
        }
        1 => {
            let mut value = source_grid(grids, record.source_a)?[cell];
            value.mul_assign(&source_grid(grids, record.source_b)?[cell]);
            Ok(value)
        }
        class => Err(ContinuationWindowReferenceError::UnsupportedClass { class }),
    }
}

fn evaluate_cell(
    program: &MainContinuationWindowProgram,
    grids: &[[E4; 27]],
    coefficient_bank: &[E4],
    cell: usize,
) -> Result<E4, ContinuationWindowReferenceError> {
    let mut accumulator = if boolean_cell(cell) {
        match program.c_init {
            Some(id) => coefficient(coefficient_bank, id)?,
            None => E4::ZERO,
        }
    } else {
        E4::ZERO
    };

    for record in program
        .dual_products
        .iter()
        .chain(program.plain_linear.iter())
    {
        let mut value = unscaled_term(record, grids, cell)?;
        value.mul_assign(&coefficient(
            coefficient_bank,
            CoefficientRecipeId(u32::from(record.coeff)),
        )?);
        accumulator.add_assign(&value);
    }

    for group in &program.grouped_records {
        let mut group_sum = E4::ZERO;
        for member in &group.members {
            let mut value = unscaled_term(member, grids, cell)?;
            value.mul_assign(&immediate(program, ImmediateId(member.coeff))?);
            group_sum.add_assign(&value);
        }
        group_sum.mul_assign(&coefficient(
            coefficient_bank,
            CoefficientRecipeId(u32::from(group.core)),
        )?);
        accumulator.add_assign(&group_sum);
    }
    Ok(accumulator)
}

/// Evaluate one width-three continuation pass into the production-ordered
/// `{0, 1, infinity}^3` tensor.
///
/// `source_rows[source][row]` contains the eight Boolean values whose local
/// index bits are `(x2_low, x1, x0_high)`. The returned tensor uses
/// `9*x2_low + 3*x1 + x0_high`; the landed low axis is therefore stride nine
/// and is the first axis consumed by the round tail. `eq_suffix` is the fresh
/// pass-local table for the unbound logical rows.
#[doc(hidden)]
pub fn continuation_window_tensor_reference(
    program: &MainContinuationWindowProgram,
    source_rows: &[Vec<[E4; 8]>],
    coefficient_bank: &[E4],
    eq_suffix: &[E4],
) -> Result<[E4; 27], ContinuationWindowReferenceError> {
    if eq_suffix.is_empty() {
        return Err(ContinuationWindowReferenceError::EmptySuffixEq);
    }
    if source_rows.len() != program.sources.len() {
        return Err(ContinuationWindowReferenceError::SourceCount {
            expected: program.sources.len(),
            actual: source_rows.len(),
        });
    }
    for (index, source) in program.sources.iter().enumerate() {
        if source.id.0 != index as u32 || usize::from(source.publish_column) != index {
            return Err(ContinuationWindowReferenceError::NonCanonicalPublication {
                source: index,
                semantic_id: source.id.0,
                publish_column: source.publish_column,
            });
        }
        let actual = source_rows[index].len();
        if actual != eq_suffix.len() {
            return Err(ContinuationWindowReferenceError::SourceRowCount {
                source: index,
                expected: eq_suffix.len(),
                actual,
            });
        }
    }

    let mut tensor = [E4::ZERO; 27];
    let mut grids = vec![[E4::ZERO; 27]; source_rows.len()];
    for (row, eq_weight) in eq_suffix.iter().enumerate() {
        for (source, rows) in source_rows.iter().enumerate() {
            grids[source] = difference_extend(rows[row]);
        }
        for cell in 0..27 {
            let mut value = evaluate_cell(program, &grids, coefficient_bank, cell)?;
            value.mul_assign(eq_weight);
            tensor[cell].add_assign(&value);
        }
    }
    Ok(tensor)
}
