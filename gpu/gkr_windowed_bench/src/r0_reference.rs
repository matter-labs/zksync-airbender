use std::cell::RefCell;
use std::collections::HashMap;

use field::{Field, FieldExtension, PrimeField};
use gkr_eval_ir::eval::{
    ChallengeResolver, LookupResolver, ReadResolver, Resolvers, VirtualSetupResolver,
};
use gkr_eval_ir::{
    analyze_claim_cone, claim_roots, CacheBoundary, ChallengeKey, ChallengePower, ChallengeRef,
    ClaimCone, DagLayer, Expr, ExprId, LookupValueKind, ReadPlace, RootId, SinkKind, SourceKind,
    VirtualSetupKind,
};
use gpu_gkr_compiler::backward::{
    interpret_coefficient_layer, interpret_r0_program, CoeffLayer, CoeffResolver,
    CoefficientRecipeId, LeanSourceBinding, R0LayerProgram, SourceId as CompilerSourceId,
    WindowFamily,
};

use crate::abi::{BF, E4};
use crate::r0_input::{
    direct_eq_weight, factored_eq_weight, resolve_normalized_coefficients_for_seed, R0InputError,
    ResolvedR0Input,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0ReferenceError {
    MissingExpression(u32),
    MissingSource(u32),
    MissingRoot(u32),
    InvalidAxisOrder([usize; 3]),
    DegreeAboveTwo {
        axis: usize,
        fixed: [usize; 2],
        third_difference: E4,
    },
    MaterializedRoot(String),
    MaterializedRootMismatch {
        root: u32,
        row: usize,
        corner: usize,
    },
    Input(String),
    Program(String),
}

impl core::fmt::Display for R0ReferenceError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for R0ReferenceError {}

impl From<R0InputError> for R0ReferenceError {
    fn from(error: R0InputError) -> Self {
        Self::Input(error.to_string())
    }
}

pub const fn tensor_index(x0: usize, x1: usize, x2: usize) -> usize {
    9 * x0 + 3 * x1 + x2
}

const fn finite_index(x0: usize, x1: usize, x2: usize) -> usize {
    16 * x0 + 4 * x1 + x2
}

fn lift(value: BF) -> E4 {
    <E4 as FieldExtension<BF>>::from_base(value)
}

fn finite_point(value: usize) -> E4 {
    lift(BF::from_u32_with_reduction(value as u32))
}

fn e4_sub(mut lhs: E4, rhs: E4) -> E4 {
    lhs.sub_assign(&rhs);
    lhs
}

fn e4_mul(mut lhs: E4, rhs: E4) -> E4 {
    lhs.mul_assign(&rhs);
    lhs
}

fn affine(zero: E4, one: E4, point: E4) -> E4 {
    let mut delta = one;
    delta.sub_assign(&zero);
    delta.mul_assign(&point);
    delta.add_assign(&zero);
    delta
}

fn corner_index(row: usize, bit0: usize, bit1: usize, bit2: usize) -> usize {
    (row << 3) | bit2 | (bit1 << 1) | (bit0 << 2)
}

fn interpolate_cube(corners: &[E4; 8], point: [E4; 3]) -> E4 {
    let mut after_x2 = [E4::ZERO; 4];
    for bit0 in 0..2 {
        for bit1 in 0..2 {
            let offset = (bit0 << 2) | (bit1 << 1);
            after_x2[2 * bit0 + bit1] = affine(corners[offset], corners[offset | 1], point[2]);
        }
    }
    let after_x1 = [
        affine(after_x2[0], after_x2[1], point[1]),
        affine(after_x2[2], after_x2[3], point[1]),
    ];
    affine(after_x1[0], after_x1[1], point[0])
}

fn third_finite_difference(p0: E4, p1: E4, p2: E4, p3: E4) -> E4 {
    let mut difference = p3;
    for _ in 0..3 {
        difference.sub_assign(&p2);
    }
    for _ in 0..3 {
        difference.add_assign(&p1);
    }
    difference.sub_assign(&p0);
    difference
}

fn check_degree_two_line(
    axis: usize,
    fixed: [usize; 2],
    values: [E4; 4],
) -> Result<(), R0ReferenceError> {
    let third_difference = third_finite_difference(values[0], values[1], values[2], values[3]);
    if !third_difference.is_zero() {
        return Err(R0ReferenceError::DegreeAboveTwo {
            axis,
            fixed,
            third_difference,
        });
    }
    Ok(())
}

/// Check every peeled-axis line on `{0,1,2,3}^3` before infinity extraction.
pub fn assert_degree_two_at_three(values: &[E4; 64]) -> Result<(), R0ReferenceError> {
    for axis in 0..3 {
        for first in 0..4 {
            for second in 0..4 {
                let mut line = [E4::ZERO; 4];
                for coordinate in 0..4 {
                    let index = match axis {
                        0 => finite_index(coordinate, first, second),
                        1 => finite_index(first, coordinate, second),
                        2 => finite_index(first, second, coordinate),
                        _ => unreachable!(),
                    };
                    line[coordinate] = values[index];
                }
                check_degree_two_line(axis, [first, second], line)?;
            }
        }
    }
    Ok(())
}

fn quadratic_leading(p0: E4, p1: E4, p2: E4) -> E4 {
    let mut numerator = p2;
    numerator.sub_assign(&p1);
    numerator.sub_assign(&p1);
    numerator.add_assign(&p0);
    let inv_two = BF::from_u32_with_reduction(2).inverse().unwrap();
    numerator.mul_assign_by_base(&inv_two);
    numerator
}

fn transform_axis(values: &mut [E4; 27], axis: usize) {
    for first in 0..3 {
        for second in 0..3 {
            let index = |coordinate| match axis {
                0 => tensor_index(coordinate, first, second),
                1 => tensor_index(first, coordinate, second),
                2 => tensor_index(first, second, coordinate),
                _ => unreachable!(),
            };
            values[index(2)] =
                quadratic_leading(values[index(0)], values[index(1)], values[index(2)]);
        }
    }
}

fn quadratic_tensor_transform_with_order(
    mut finite: [E4; 27],
    order: [usize; 3],
) -> Result<[E4; 27], R0ReferenceError> {
    let mut sorted = order;
    sorted.sort_unstable();
    if sorted != [0, 1, 2] {
        return Err(R0ReferenceError::InvalidAxisOrder(order));
    }
    for axis in order {
        transform_axis(&mut finite, axis);
    }
    Ok(finite)
}

/// Convert a quadratic tensor sampled on `{0,1,2}^3` to the
/// `{0,1,infinity}^3` coefficient convention.
pub fn quadratic_tensor_transform(finite: [E4; 27]) -> Result<[E4; 27], R0ReferenceError> {
    quadratic_tensor_transform_with_order(finite, [2, 1, 0])
}

fn transform_checked_finite(values: &[E4; 64]) -> Result<[E4; 27], R0ReferenceError> {
    assert_degree_two_at_three(values)?;
    let mut finite = [E4::ZERO; 27];
    for x0 in 0..3 {
        for x1 in 0..3 {
            for x2 in 0..3 {
                finite[tensor_index(x0, x1, x2)] = values[finite_index(x0, x1, x2)];
            }
        }
    }
    quadratic_tensor_transform(finite)
}

/// Stable checksum used only to identify the 27-cell CPU diagnostics.
pub fn r0_output_checksum(output: &[E4; 27]) -> u64 {
    const OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    const MULTIPLIER: u64 = 0x0000_0100_0000_01b3;
    output.iter().fold(OFFSET, |hash, value| {
        [
            value.c0.c0.raw_u32_value(),
            value.c0.c1.raw_u32_value(),
            value.c1.c0.raw_u32_value(),
            value.c1.c1.raw_u32_value(),
        ]
        .into_iter()
        .fold(hash, |hash, limb| {
            (hash ^ u64::from(limb)).wrapping_mul(MULTIPLIER)
        })
    })
}

/// Evaluate a backward-claim expression after substituting each `LookupValue`
/// leaf with its canonical query expression.  The lookup resolver in `resolvers`
/// is deliberately never called.
pub fn eval_backward_claim_expr(
    layer: &DagLayer,
    expr: ExprId,
    row: usize,
    resolvers: &Resolvers<'_>,
) -> Result<E4, R0ReferenceError> {
    eval_expr_with_boundary_policy(
        layer,
        expr,
        row,
        resolvers,
        &mut HashMap::new(),
        &BoundaryPolicy::Inline,
    )
}

enum BoundaryPolicy<'a> {
    Inline,
    CanonicalFences {
        corners: &'a HashMap<ExprId, [E4; 8]>,
        point: [E4; 3],
    },
}

impl BoundaryPolicy<'_> {
    fn resolve(&self, expr: ExprId) -> Option<E4> {
        match self {
            Self::Inline => None,
            Self::CanonicalFences { corners, point } => corners
                .get(&expr)
                .map(|corners| interpolate_cube(corners, *point)),
        }
    }
}

fn eval_expr_with_boundary_policy(
    layer: &DagLayer,
    expr: ExprId,
    row: usize,
    resolvers: &Resolvers<'_>,
    cache: &mut HashMap<ExprId, E4>,
    boundary_policy: &BoundaryPolicy<'_>,
) -> Result<E4, R0ReferenceError> {
    if let Some(value) = cache.get(&expr) {
        return Ok(*value);
    }
    if let Some(value) = boundary_policy.resolve(expr) {
        cache.insert(expr, value);
        return Ok(value);
    }
    let value = match layer
        .exprs
        .get(expr.0 as usize)
        .ok_or(R0ReferenceError::MissingExpression(expr.0))?
    {
        Expr::Source(source) => {
            let kind = layer
                .sources
                .get(source.0 as usize)
                .ok_or(R0ReferenceError::MissingSource(source.0))?;
            match kind {
                SourceKind::Read { place } => resolvers.read.read(place, row),
                SourceKind::Constant { value } => {
                    <E4 as FieldExtension<BF>>::from_base(BF::from_u32_with_reduction(*value))
                }
                SourceKind::Challenge { reference } => resolvers.challenge.challenge(reference),
                SourceKind::VirtualSetup { kind } => <E4 as FieldExtension<BF>>::from_base(
                    resolvers.virtual_setup.virtual_setup(kind, row),
                ),
                SourceKind::InitsAndTeardownsTopBits { reference } => {
                    let value = (reference.set_index as u32)
                        .checked_shl(reference.shift)
                        .unwrap_or(0);
                    <E4 as FieldExtension<BF>>::from_base(BF::from_u32_with_reduction(value))
                }
                SourceKind::LookupValue { query, .. } => eval_expr_with_boundary_policy(
                    layer,
                    *query,
                    row,
                    resolvers,
                    cache,
                    boundary_policy,
                )?,
            }
        }
        Expr::Add(children) => {
            let mut sum = E4::ZERO;
            for child in children {
                sum.add_assign(&eval_expr_with_boundary_policy(
                    layer,
                    *child,
                    row,
                    resolvers,
                    cache,
                    boundary_policy,
                )?);
            }
            sum
        }
        Expr::Mul(children) => {
            let mut product = E4::ONE;
            for child in children {
                product.mul_assign(&eval_expr_with_boundary_policy(
                    layer,
                    *child,
                    row,
                    resolvers,
                    cache,
                    boundary_policy,
                )?);
            }
            product
        }
    };
    cache.insert(expr, value);
    Ok(value)
}

fn eval_query_substituted_root(
    layer: &DagLayer,
    root: RootId,
    row: usize,
    resolvers: &Resolvers<'_>,
    cache: &mut HashMap<ExprId, E4>,
) -> Result<E4, R0ReferenceError> {
    let expr = layer
        .roots
        .get(root.0 as usize)
        .ok_or(R0ReferenceError::MissingRoot(root.0))?
        .expr;
    eval_expr_with_boundary_policy(layer, expr, row, resolvers, cache, &BoundaryPolicy::Inline)
}

fn claim_batch_factor(input: &ResolvedR0Input, position: usize) -> Result<E4, R0ReferenceError> {
    if position == 0 {
        return Ok(E4::ONE);
    }
    let power = if position == 1 {
        ChallengePower::One
    } else {
        ChallengePower::Static(position as u32)
    };
    Ok(input.resolve_canonical_challenge(&ChallengeRef {
        key: ChallengeKey::ClaimBatching,
        power,
    })?)
}

fn eval_batched_claims_query_substituted(
    layer: &DagLayer,
    row: usize,
    resolvers: &Resolvers<'_>,
    input: &ResolvedR0Input,
) -> Result<E4, R0ReferenceError> {
    let mut cache = HashMap::new();
    let mut sum = E4::ZERO;
    for (position, root) in claim_roots(layer).iter().copied().enumerate() {
        let mut value = eval_query_substituted_root(layer, root, row, resolvers, &mut cache)?;
        value.mul_assign(&claim_batch_factor(input, position)?);
        sum.add_assign(&value);
    }
    Ok(sum)
}

struct CanonicalPointRead<'a> {
    binding: &'a LeanSourceBinding,
    input: &'a ResolvedR0Input,
    surviving_row: usize,
    point: [E4; 3],
}

impl CanonicalPointRead<'_> {
    fn try_read(&self, place: &ReadPlace) -> Result<E4, R0InputError> {
        let mut corners = [E4::ZERO; 8];
        for bit0 in 0..2 {
            for bit1 in 0..2 {
                for bit2 in 0..2 {
                    let offset = bit2 | (bit1 << 1) | (bit0 << 2);
                    corners[offset] = self.input.read_canonical_place(
                        self.binding,
                        place,
                        corner_index(self.surviving_row, bit0, bit1, bit2),
                    )?;
                }
            }
        }
        Ok(interpolate_cube(&corners, self.point))
    }
}

impl ReadResolver for CanonicalPointRead<'_> {
    fn read(&self, place: &ReadPlace, _row: usize) -> E4 {
        self.try_read(place)
            .expect("canonical reads are classified before reference evaluation")
    }
}

struct CanonicalPointVirtual<'a> {
    input: &'a ResolvedR0Input,
    surviving_row: usize,
    point: [E4; 3],
}

impl VirtualSetupResolver for CanonicalPointVirtual<'_> {
    fn virtual_setup(&self, kind: &VirtualSetupKind, _row: usize) -> BF {
        let value = self.virtual_setup_fold(kind, 0, &[]);
        assert!(value.c0.c1.is_zero() && value.c1.c0.is_zero() && value.c1.c1.is_zero());
        value.c0.c0
    }

    fn virtual_setup_fold(&self, kind: &VirtualSetupKind, _row: usize, _ch: &[E4]) -> E4 {
        let mut corners = [E4::ZERO; 8];
        for bit0 in 0..2 {
            for bit1 in 0..2 {
                for bit2 in 0..2 {
                    let offset = bit2 | (bit1 << 1) | (bit0 << 2);
                    corners[offset] =
                        lift(self.input.sources.virtual_setup(
                            kind,
                            corner_index(self.surviving_row, bit0, bit1, bit2),
                        ));
                }
            }
        }
        interpolate_cube(&corners, self.point)
    }
}

struct InputChallenges<'a>(&'a ResolvedR0Input);

impl ChallengeResolver for InputChallenges<'_> {
    fn challenge(&self, reference: &ChallengeRef) -> E4 {
        self.0
            .resolve_canonical_challenge(reference)
            .expect("Task 3 prevalidates every canonical challenge")
    }
}

struct PanicLookup;

impl LookupResolver for PanicLookup {
    fn lookup(
        &self,
        kind: &LookupValueKind,
        set_index: usize,
        _evaluated_query: E4,
        row: usize,
    ) -> BF {
        panic!("query-substituting reference called runtime lookup {kind:?}/{set_index} at {row}")
    }
}

fn with_canonical_point<T>(
    binding: &LeanSourceBinding,
    input: &ResolvedR0Input,
    surviving_row: usize,
    point: [E4; 3],
    evaluate: impl FnOnce(&Resolvers<'_>, &CanonicalPointRead<'_>) -> Result<T, R0ReferenceError>,
) -> Result<T, R0ReferenceError> {
    let read = CanonicalPointRead {
        binding,
        input,
        surviving_row,
        point,
    };
    let virtual_setup = CanonicalPointVirtual {
        input,
        surviving_row,
        point,
    };
    let challenges = InputChallenges(input);
    let lookup = PanicLookup;
    evaluate(
        &Resolvers {
            read: &read,
            lookup: &lookup,
            virtual_setup: &virtual_setup,
            challenge: &challenges,
        },
        &read,
    )
}

fn place_column_in_family(place: &ReadPlace, family: &WindowFamily) -> Option<usize> {
    match (place, family) {
        (ReadPlace::BaseLayerMemory { column }, WindowFamily::BaseLayerMemory)
        | (ReadPlace::BaseLayerWitness { column }, WindowFamily::BaseLayerWitness)
        | (ReadPlace::Setup { column }, WindowFamily::Setup) => Some(*column),
        (ReadPlace::Scratch { slot }, WindowFamily::Scratch) => Some(*slot),
        (
            ReadPlace::LayerOutput { layer, offset },
            WindowFamily::LayerOutput {
                layer: family_layer,
                ..
            },
        ) if layer == family_layer => Some(*offset),
        (
            ReadPlace::CacheOutput { layer, offset },
            WindowFamily::CacheOutput {
                layer: family_layer,
                ..
            },
        ) if layer == family_layer => Some(*offset),
        _ => None,
    }
}

fn cache_boundary_is_bound(
    binding: &LeanSourceBinding,
    boundary: &CacheBoundary,
) -> Result<bool, R0ReferenceError> {
    let mut found = false;
    for window in &binding.windows {
        let Some(column) = place_column_in_family(&boundary.place, &window.family) else {
            continue;
        };
        if window
            .columns
            .binary_search_by_key(&column, |entry| entry.column)
            .is_err()
        {
            continue;
        }
        if window.backing_field() != boundary.field {
            return Err(R0ReferenceError::Input(format!(
                "cache boundary {:?} has field {:?}, but its bound window has field {:?}",
                boundary.place,
                boundary.field,
                window.backing_field(),
            )));
        }
        if found {
            return Err(R0ReferenceError::Input(format!(
                "cache boundary {:?} has multiple bound coordinates",
                boundary.place,
            )));
        }
        found = true;
    }
    Ok(found)
}

fn read_bound_fence_corners(
    binding: &LeanSourceBinding,
    input: &ResolvedR0Input,
    surviving_row: usize,
    boundary: &CacheBoundary,
) -> Result<Option<[E4; 8]>, R0ReferenceError> {
    if !cache_boundary_is_bound(binding, boundary)? {
        return Ok(None);
    }
    let mut corners = [E4::ZERO; 8];
    for bit0 in 0..2 {
        for bit1 in 0..2 {
            for bit2 in 0..2 {
                let offset = bit2 | (bit1 << 1) | (bit0 << 2);
                corners[offset] = input.sources.read_place(
                    binding,
                    &boundary.place,
                    corner_index(surviving_row, bit0, bit1, bit2),
                )?;
            }
        }
    }
    Ok(Some(corners))
}

fn resolve_fence_corners(
    bound: Option<[E4; 8]>,
    evaluate_inline: impl FnOnce() -> Result<[E4; 8], R0ReferenceError>,
) -> Result<[E4; 8], R0ReferenceError> {
    match bound {
        Some(corners) => Ok(corners),
        None => evaluate_inline(),
    }
}

fn canonical_fence_corners_for_row(
    layer: &DagLayer,
    binding: &LeanSourceBinding,
    input: &ResolvedR0Input,
    surviving_row: usize,
    cone: &ClaimCone,
) -> Result<HashMap<ExprId, [E4; 8]>, R0ReferenceError> {
    let mut result = HashMap::new();
    for expr_index in 0..layer.exprs.len() {
        let expr = ExprId(expr_index as u32);
        if !cone.is_reachable(expr) {
            continue;
        }
        let Some(boundary) = cone.cache_boundary(expr) else {
            continue;
        };
        let bound = read_bound_fence_corners(binding, input, surviving_row, boundary)?;
        let corners = resolve_fence_corners(bound, || {
            let mut canonical = [E4::ZERO; 8];
            for bit0 in 0..2 {
                for bit1 in 0..2 {
                    for bit2 in 0..2 {
                        let offset = bit2 | (bit1 << 1) | (bit0 << 2);
                        canonical[offset] = with_canonical_point(
                            binding,
                            input,
                            surviving_row,
                            [finite_point(bit0), finite_point(bit1), finite_point(bit2)],
                            |resolvers, _point_read| {
                                eval_expr_with_boundary_policy(
                                    layer,
                                    expr,
                                    surviving_row,
                                    resolvers,
                                    &mut HashMap::new(),
                                    &BoundaryPolicy::Inline,
                                )
                            },
                        )?;
                    }
                }
            }
            Ok(canonical)
        })?;
        result.insert(expr, corners);
    }
    Ok(result)
}

fn evaluate_root_at_point(
    layer: &DagLayer,
    root: RootId,
    binding: &LeanSourceBinding,
    input: &ResolvedR0Input,
    surviving_row: usize,
    point: [E4; 3],
) -> Result<E4, R0ReferenceError> {
    with_canonical_point(
        binding,
        input,
        surviving_row,
        point,
        |resolvers, _point_read| {
            eval_query_substituted_root(layer, root, surviving_row, resolvers, &mut HashMap::new())
        },
    )
}

fn evaluate_compiler_convention_root_at_point(
    layer: &DagLayer,
    root: RootId,
    binding: &LeanSourceBinding,
    input: &ResolvedR0Input,
    surviving_row: usize,
    point: [E4; 3],
    fence_corners: &HashMap<ExprId, [E4; 8]>,
) -> Result<E4, R0ReferenceError> {
    let expr = layer
        .roots
        .get(root.0 as usize)
        .ok_or(R0ReferenceError::MissingRoot(root.0))?
        .expr;
    with_canonical_point(
        binding,
        input,
        surviving_row,
        point,
        |resolvers, _point_read| {
            eval_expr_with_boundary_policy(
                layer,
                expr,
                surviving_row,
                resolvers,
                &mut HashMap::new(),
                &BoundaryPolicy::CanonicalFences {
                    corners: fence_corners,
                    point,
                },
            )
        },
    )
}

fn reference_rows(input: &ResolvedR0Input) -> Result<usize, R0ReferenceError> {
    if input.sources.trace_len < 8 || input.sources.trace_len & 7 != 0 {
        return Err(R0ReferenceError::Input(format!(
            "R0 source length {} is not divisible by eight",
            input.sources.trace_len
        )));
    }
    Ok(input.sources.trace_len >> 3)
}

/// Evaluate the direct canonical polynomial `P` and convert its independently
/// checked finite samples to `{0,1,infinity}^3`.
///
/// This path deliberately uses canonical root order, query substitution,
/// canonical source reads, and direct equality.  It does not consume a lowered
/// coefficient program or any factored equality table.
pub fn evaluate_true_canonical_tensor(
    layer: &DagLayer,
    binding: &LeanSourceBinding,
    input: &ResolvedR0Input,
) -> Result<[E4; 27], R0ReferenceError> {
    let rows = reference_rows(input)?;
    let mut finite = [E4::ZERO; 64];
    for x0 in 0..4 {
        for x1 in 0..4 {
            for x2 in 0..4 {
                let point = [finite_point(x0), finite_point(x1), finite_point(x2)];
                let mut sum = E4::ZERO;
                for row in 0..rows {
                    let value = with_canonical_point(
                        binding,
                        input,
                        row,
                        point,
                        |resolvers, _point_read| {
                            eval_batched_claims_query_substituted(layer, row, resolvers, input)
                        },
                    )?;
                    sum.add_assign(&e4_mul(
                        direct_eq_weight(row, &input.identity.equality_point),
                        value,
                    ));
                }
                finite[finite_index(x0, x1, x2)] = sum;
            }
        }
    }
    transform_checked_finite(&finite)
}

fn sink_read_place(sink: &SinkKind) -> Option<ReadPlace> {
    match sink {
        SinkKind::Inner { layer, offset } => Some(ReadPlace::LayerOutput {
            layer: *layer,
            offset: *offset,
        }),
        SinkKind::Cache { layer, offset } => Some(ReadPlace::CacheOutput {
            layer: *layer,
            offset: *offset,
        }),
        SinkKind::Scratch { slot } => Some(ReadPlace::Scratch { slot: *slot }),
    }
}

fn materialized_root_corners(
    layer: &DagLayer,
    root: RootId,
    binding: &LeanSourceBinding,
    input: &ResolvedR0Input,
    surviving_row: usize,
) -> Result<[E4; 8], R0ReferenceError> {
    let root_info = layer
        .roots
        .get(root.0 as usize)
        .ok_or(R0ReferenceError::MissingRoot(root.0))?;
    root_info.claim.as_ref().ok_or_else(|| {
        R0ReferenceError::MaterializedRoot(format!("root {} has no claim", root.0))
    })?;
    let place = match &root_info.materialize {
        Some(sink) => Some(sink_read_place(&sink.kind).ok_or_else(|| {
            R0ReferenceError::MaterializedRoot(format!(
                "root {} has a non-readable output sink {:?}",
                root.0, sink.kind
            ))
        })?),
        None => None,
    };

    let mut corners = [E4::ZERO; 8];
    for bit0 in 0..2 {
        for bit1 in 0..2 {
            for bit2 in 0..2 {
                let offset = bit2 | (bit1 << 1) | (bit0 << 2);
                let original_row = corner_index(surviving_row, bit0, bit1, bit2);
                let actual = match &place {
                    Some(place) => input.sources.read_place(binding, place, original_row)?,
                    None => E4::ZERO,
                };
                if place.is_some() {
                    let expected = evaluate_root_at_point(
                        layer,
                        root,
                        binding,
                        input,
                        surviving_row,
                        [finite_point(bit0), finite_point(bit1), finite_point(bit2)],
                    )?;
                    if actual != expected {
                        return Err(R0ReferenceError::MaterializedRootMismatch {
                            root: root.0,
                            row: surviving_row,
                            corner: offset,
                        });
                    }
                }
                corners[offset] = actual;
            }
        }
    }
    Ok(corners)
}

/// Evaluate the canonical-derived compiler convention `Q = R_cube + x2^2*C2`.
/// Root-output Boolean corners come from Task 3's canonical materialization and
/// are revalidated against the query-substituting evaluator before use.
pub fn evaluate_canonical_r0_convention(
    layer: &DagLayer,
    binding: &LeanSourceBinding,
    input: &ResolvedR0Input,
) -> Result<[E4; 27], R0ReferenceError> {
    let rows = reference_rows(input)?;
    let cone = analyze_claim_cone(layer);
    let mut finite = [E4::ZERO; 64];
    for row in 0..rows {
        let fence_corners = canonical_fence_corners_for_row(layer, binding, input, row, &cone)?;
        let equality = direct_eq_weight(row, &input.identity.equality_point);
        for (position, root) in claim_roots(layer).iter().copied().enumerate() {
            let corners = materialized_root_corners(layer, root, binding, input, row)?;
            let mut scale = claim_batch_factor(input, position)?;
            scale.mul_assign(&equality);
            for x0 in 0..4 {
                for x1 in 0..4 {
                    let mut polynomial = [E4::ZERO; 4];
                    for x2 in 0..4 {
                        polynomial[x2] = evaluate_compiler_convention_root_at_point(
                            layer,
                            root,
                            binding,
                            input,
                            row,
                            [finite_point(x0), finite_point(x1), finite_point(x2)],
                            &fence_corners,
                        )?;
                    }
                    check_degree_two_line(2, [x0, x1], polynomial)?;
                    let c2 = quadratic_leading(polynomial[0], polynomial[1], polynomial[2]);
                    for x2 in 0..4 {
                        let point = [finite_point(x0), finite_point(x1), finite_point(x2)];
                        let mut value = interpolate_cube(&corners, point);
                        let mut correction = c2;
                        correction.mul_assign(&point[2]);
                        correction.mul_assign(&point[2]);
                        value.add_assign(&correction);
                        value.mul_assign(&scale);
                        finite[finite_index(x0, x1, x2)].add_assign(&value);
                    }
                }
            }
        }
    }
    transform_checked_finite(&finite)
}

struct CompiledPointResolver<'a> {
    program: &'a R0LayerProgram,
    input: &'a ResolvedR0Input,
    surviving_row: usize,
    point: [E4; 3],
    pairs: RefCell<HashMap<u32, (E4, E4)>>,
}

impl CompiledPointResolver<'_> {
    fn source_at(&self, id: CompilerSourceId, x2: E4) -> E4 {
        let mut corners = [E4::ZERO; 8];
        for bit0 in 0..2 {
            for bit1 in 0..2 {
                for bit2 in 0..2 {
                    let offset = bit2 | (bit1 << 1) | (bit0 << 2);
                    corners[offset] = self
                        .input
                        .sources
                        .read_bound_source(
                            &self.program.binding,
                            id.0 as usize,
                            corner_index(self.surviving_row, bit0, bit1, bit2),
                        )
                        .expect("the compiled interpreter validates bound source ids");
                }
            }
        }
        interpolate_cube(&corners, [self.point[0], self.point[1], x2])
    }
}

impl CoeffResolver for CompiledPointResolver<'_> {
    fn coefficient(&self, id: CoefficientRecipeId) -> E4 {
        self.input.coefficient_bank[id
            .bank_index()
            .expect("the interpreter resolves reserved literal coefficients internally")]
    }

    fn source_pair(&self, id: CompilerSourceId, _row: usize) -> (E4, E4) {
        if let Some(pair) = self.pairs.borrow().get(&id.0) {
            return *pair;
        }
        let at_zero = self.source_at(id, E4::ZERO);
        let at_one = self.source_at(id, E4::ONE);
        let at_point = affine(at_zero, at_one, self.point[2]);
        let pair = (at_point, e4_sub(at_one, at_zero));
        self.pairs.borrow_mut().insert(id.0, pair);
        pair
    }
}

struct SchedulePointResolver<'a> {
    binding: &'a LeanSourceBinding,
    coefficient_bank: &'a [E4],
    input: &'a ResolvedR0Input,
    surviving_row: usize,
    point: [E4; 3],
    pairs: RefCell<HashMap<u32, (E4, E4)>>,
}

impl SchedulePointResolver<'_> {
    fn source_at(&self, id: CompilerSourceId, x2: E4) -> E4 {
        let mut corners = [E4::ZERO; 8];
        for bit0 in 0..2 {
            for bit1 in 0..2 {
                for bit2 in 0..2 {
                    let offset = bit2 | (bit1 << 1) | (bit0 << 2);
                    corners[offset] = self
                        .input
                        .sources
                        .read_bound_source(
                            self.binding,
                            id.0 as usize,
                            corner_index(self.surviving_row, bit0, bit1, bit2),
                        )
                        .expect("the coefficient layer validates bound source ids");
                }
            }
        }
        interpolate_cube(&corners, [self.point[0], self.point[1], x2])
    }
}

impl CoeffResolver for SchedulePointResolver<'_> {
    fn coefficient(&self, id: CoefficientRecipeId) -> E4 {
        self.coefficient_bank[id
            .bank_index()
            .expect("reserved literal coefficients are resolved by the interpreter")]
    }

    fn source_pair(&self, id: CompilerSourceId, _row: usize) -> (E4, E4) {
        if let Some(pair) = self.pairs.borrow().get(&id.0) {
            return *pair;
        }
        let at_zero = self.source_at(id, E4::ZERO);
        let at_one = self.source_at(id, E4::ONE);
        let at_point = affine(at_zero, at_one, self.point[2]);
        let pair = (at_point, e4_sub(at_one, at_zero));
        self.pairs.borrow_mut().insert(id.0, pair);
        pair
    }
}

pub fn evaluate_r0_coeff_schedule(
    coefficients: &CoeffLayer,
    binding: &LeanSourceBinding,
    input: &ResolvedR0Input,
) -> Result<[E4; 27], R0ReferenceError> {
    let coefficient_bank =
        resolve_normalized_coefficients_for_seed(&coefficients.coefficients, input.identity.seed)?;
    let rows = reference_rows(input)?;
    let mut finite = [E4::ZERO; 64];
    for x0 in 0..4 {
        for x1 in 0..4 {
            for x2 in 0..4 {
                let point = [finite_point(x0), finite_point(x1), finite_point(x2)];
                let mut sum = E4::ZERO;
                for row in 0..rows {
                    let resolver = SchedulePointResolver {
                        binding,
                        coefficient_bank: &coefficient_bank,
                        input,
                        surviving_row: row,
                        point,
                        pairs: RefCell::new(HashMap::new()),
                    };
                    let (c0_at_t, c2) =
                        interpret_coefficient_layer(coefficients, row, &resolver)
                            .map_err(|error| R0ReferenceError::Program(format!("{error:?}")))?;
                    let mut correction = c2;
                    correction.mul_assign(&point[2]);
                    correction.mul_assign(&point[2]);
                    let mut value = c0_at_t;
                    value.add_assign(&correction);
                    value.mul_assign(&factored_eq_weight(row, &input.eq_tables)?);
                    sum.add_assign(&value);
                }
                finite[finite_index(x0, x1, x2)] = sum;
            }
        }
    }
    transform_checked_finite(&finite)
}

/// Evaluate the decoded compiler-R0 program on finite points and independently
/// transform it to the 27-cell infinity convention.  This path uses only the
/// compiler binding, recipe bank, interpreter, and factored equality tables.
pub fn evaluate_compiled_r0_tensor(
    program: &R0LayerProgram,
    input: &ResolvedR0Input,
) -> Result<[E4; 27], R0ReferenceError> {
    if program.layer as u32 != input.identity.layer {
        return Err(R0ReferenceError::Program(format!(
            "program layer {} does not match input layer {}",
            program.layer, input.identity.layer
        )));
    }
    let rows = reference_rows(input)?;
    let mut finite = [E4::ZERO; 64];
    for x0 in 0..4 {
        for x1 in 0..4 {
            for x2 in 0..4 {
                let point = [finite_point(x0), finite_point(x1), finite_point(x2)];
                let mut sum = E4::ZERO;
                for row in 0..rows {
                    let resolver = CompiledPointResolver {
                        program,
                        input,
                        surviving_row: row,
                        point,
                        pairs: RefCell::new(HashMap::new()),
                    };
                    let (c0_at_t, c2) = interpret_r0_program(program, row, &resolver, 1)
                        .map_err(|error| R0ReferenceError::Program(format!("{error:?}")))?;
                    let mut correction = c2;
                    correction.mul_assign(&point[2]);
                    correction.mul_assign(&point[2]);
                    let mut value = c0_at_t;
                    value.add_assign(&correction);
                    value.mul_assign(&factored_eq_weight(row, &input.eq_tables)?);
                    sum.add_assign(&value);
                }
                finite[finite_index(x0, x1, x2)] = sum;
            }
        }
    }
    transform_checked_finite(&finite)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};
    use std::path::PathBuf;

    use cs::gkr_compiler::GKRCircuitArtifact;
    use field::baby_bear::base::BabyBearField;
    use field::baby_bear::ext4::BabyBearExt4;
    use field::{Field, FieldExtension, PrimeField};
    use gkr_eval_ir::eval::{
        ChallengeResolver, LookupResolver, ReadResolver, Resolvers, VirtualSetupResolver,
    };
    use gkr_eval_ir::{
        BatchingOrder, DagLayer, Expr, ExprId, FieldKind, LookupValueKind, ReadPlace, Root,
        RootGroup, RootId, RootOrigin, SinkInfo, SinkKind, SourceId, SourceKind, VirtualSetupKind,
    };
    use gpu_gkr_compiler::{compile_r0, GpuResourceProfile};

    use crate::abi::{BF, E4};
    use crate::census::CORPUS;
    use crate::r0_artifact::{decode_r0_bundle, FrozenR0Coordinate, R0_CORPUS_BYTES};
    use crate::r0_input::build_r0_input_with_layer;

    use super::{
        assert_degree_two_at_three, eval_backward_claim_expr, eval_expr_with_boundary_policy,
        evaluate_canonical_r0_convention, evaluate_compiled_r0_tensor,
        evaluate_true_canonical_tensor, quadratic_leading, quadratic_tensor_transform,
        quadratic_tensor_transform_with_order, r0_output_checksum, resolve_fence_corners,
        tensor_index, BoundaryPolicy, R0ReferenceError,
    };

    struct PanicRead;

    impl ReadResolver for PanicRead {
        fn read(&self, place: &ReadPlace, row: usize) -> BabyBearExt4 {
            panic!("unexpected read {place:?} at row {row}")
        }
    }

    struct PanicLookup;

    impl LookupResolver for PanicLookup {
        fn lookup(
            &self,
            kind: &LookupValueKind,
            set_index: usize,
            _query: BabyBearExt4,
            row: usize,
        ) -> BabyBearField {
            panic!("lookup resolver called for {kind:?}/{set_index} at row {row}")
        }
    }

    struct PanicVirtual;

    impl VirtualSetupResolver for PanicVirtual {
        fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> BabyBearField {
            panic!("unexpected virtual setup {kind:?} at row {row}")
        }
    }

    struct PanicChallenge;

    impl ChallengeResolver for PanicChallenge {
        fn challenge(&self, reference: &gkr_eval_ir::ChallengeRef) -> BabyBearExt4 {
            panic!("unexpected challenge {reference:?}")
        }
    }

    struct PeeledX2Read;

    impl ReadResolver for PeeledX2Read {
        fn read(&self, place: &ReadPlace, row: usize) -> BabyBearExt4 {
            match place {
                ReadPlace::BaseLayerMemory { column: 0 } => lift_u32(row as u32 + 1),
                ReadPlace::BaseLayerWitness { column: 0 } => lift_u32(row as u32),
                _ => panic!("unexpected synthetic read {place:?}"),
            }
        }
    }

    fn synthetic_cache_product_layer() -> DagLayer {
        let fence = ExprId(0);
        let factor = ExprId(1);
        let product = ExprId(2);
        DagLayer {
            sources: vec![
                SourceKind::Read {
                    place: ReadPlace::BaseLayerMemory { column: 0 },
                },
                SourceKind::Read {
                    place: ReadPlace::BaseLayerWitness { column: 0 },
                },
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Mul(vec![fence, factor]),
            ],
            roots: vec![
                Root {
                    expr: fence,
                    materialize: Some(SinkInfo {
                        kind: SinkKind::Cache {
                            layer: 0,
                            offset: 3,
                        },
                        field: FieldKind::Base,
                    }),
                    claim: None,
                },
                Root {
                    expr: product,
                    materialize: None,
                    claim: Some(RootOrigin {
                        group: RootGroup::Gates,
                        relation_index: 0,
                    }),
                },
            ],
            batching: BatchingOrder {
                roots: vec![RootId(1)],
            },
            resolutions: BTreeMap::new(),
            forward_skip_roots: Default::default(),
        }
    }

    #[test]
    fn cpu_absent_cache_fence_preserves_canonical_c2_contribution() {
        let layer = synthetic_cache_product_layer();
        let cone = gkr_eval_ir::analyze_claim_cone(&layer);
        assert!(cone.cache_boundary(ExprId(0)).is_some());
        let canonical = [
            lift_u32(1),
            lift_u32(2),
            lift_u32(1),
            lift_u32(2),
            lift_u32(1),
            lift_u32(2),
            lift_u32(1),
            lift_u32(2),
        ];
        let retained = resolve_fence_corners(None, || Ok(canonical)).unwrap();
        assert_eq!(retained, canonical);
        let fences = HashMap::from([(ExprId(0), retained)]);
        let resolvers = Resolvers {
            read: &PeeledX2Read,
            lookup: &PanicLookup,
            virtual_setup: &PanicVirtual,
            challenge: &PanicChallenge,
        };
        let mut polynomial = [E4::ZERO; 4];
        for (x2, value) in polynomial.iter_mut().enumerate() {
            *value = eval_expr_with_boundary_policy(
                &layer,
                ExprId(2),
                x2,
                &resolvers,
                &mut HashMap::new(),
                &BoundaryPolicy::CanonicalFences {
                    corners: &fences,
                    point: [E4::ZERO, E4::ZERO, lift_u32(x2 as u32)],
                },
            )
            .unwrap();
        }
        assert_eq!(
            polynomial,
            [lift_u32(0), lift_u32(2), lift_u32(6), lift_u32(12)]
        );
        assert_eq!(
            quadratic_leading(polynomial[0], polynomial[1], polynomial[2]),
            E4::ONE
        );
    }

    #[test]
    fn cpu_bound_cache_fence_uses_independent_bound_corners() {
        let canonical = [E4::ONE; 8];
        let mut bound = canonical;
        bound[5] = lift_u32(9);
        let actual = resolve_fence_corners(Some(bound), || -> Result<[E4; 8], R0ReferenceError> {
            panic!("bound cache ownership must not evaluate the inline expression")
        })
        .unwrap();
        assert_eq!(actual, bound);
        assert_ne!(actual, canonical);
    }

    #[test]
    fn cpu_backward_claim_lookup_value_substitutes_its_query() {
        let layer = DagLayer {
            sources: vec![
                SourceKind::Constant { value: 9 },
                SourceKind::LookupValue {
                    kind: LookupValueKind::GenericColumn { column: 3 },
                    set_index: 2,
                    query: ExprId(0),
                },
            ],
            exprs: vec![Expr::Source(SourceId(0)), Expr::Source(SourceId(1))],
            roots: Vec::new(),
            batching: BatchingOrder { roots: Vec::new() },
            resolutions: BTreeMap::new(),
            forward_skip_roots: Default::default(),
        };
        let resolvers = Resolvers {
            read: &PanicRead,
            lookup: &PanicLookup,
            virtual_setup: &PanicVirtual,
            challenge: &PanicChallenge,
        };

        let actual = eval_backward_claim_expr(&layer, ExprId(1), 0, &resolvers).unwrap();
        let expected = <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(
            BabyBearField::from_u32_with_reduction(9),
        );
        assert_eq!(actual, expected);
    }

    fn lift_u32(value: u32) -> E4 {
        <E4 as FieldExtension<BF>>::from_base(BF::from_u32_with_reduction(value))
    }

    fn fixture_quadratic(x0: u32, x1: u32, x2: u32) -> E4 {
        // The unique x0^2*x1^2*x2^2 coefficient is the literal 31 below.  The
        // rest deliberately mixes all axes so a one-axis-only transform fails.
        let [x0, x1, x2] = [x0, x1, x2].map(lift_u32);
        let mut value = lift_u32(3);
        for (coefficient, mut term) in [
            (2, x0),
            (5, x1),
            (7, x2),
            (11, {
                let mut term = x0;
                term.mul_assign(&x1);
                term
            }),
            (13, {
                let mut term = x1;
                term.mul_assign(&x2);
                term
            }),
            (17, {
                let mut term = x0;
                term.mul_assign(&x0);
                term
            }),
            (19, {
                let mut term = x1;
                term.mul_assign(&x1);
                term
            }),
            (23, {
                let mut term = x2;
                term.mul_assign(&x2);
                term
            }),
            (31, {
                let mut term = x0;
                term.mul_assign(&x0);
                term.mul_assign(&x1);
                term.mul_assign(&x1);
                term.mul_assign(&x2);
                term.mul_assign(&x2);
                term
            }),
        ] {
            term.mul_assign(&lift_u32(coefficient));
            value.add_assign(&term);
        }
        value
    }

    fn fixture_leading_xyz() -> E4 {
        lift_u32(31)
    }

    fn evaluate_fixture_on_grid(points: [u32; 3]) -> [E4; 27] {
        let mut values = [E4::ZERO; 27];
        for x0 in 0..3 {
            for x1 in 0..3 {
                for x2 in 0..3 {
                    values[tensor_index(x0, x1, x2)] =
                        fixture_quadratic(points[x0], points[x1], points[x2]);
                }
            }
        }
        values
    }

    fn evaluate_cubic_fixture_on_grid(points: [u32; 4]) -> [E4; 64] {
        let mut values = [E4::ZERO; 64];
        for x0 in 0..4 {
            for x1 in 0..4 {
                for x2 in 0..4 {
                    let x0_value = lift_u32(points[x0]);
                    let mut value = x0_value;
                    value.mul_assign(&x0_value);
                    value.mul_assign(&x0_value);
                    value.add_assign(&lift_u32(points[x1] + 2 * points[x2]));
                    values[16 * x0 + 4 * x1 + x2] = value;
                }
            }
        }
        values
    }

    #[test]
    fn cpu_quadratic_transform_recovers_all_infinity_cells() {
        let finite = evaluate_fixture_on_grid([0, 1, 2]);
        let tensor = quadratic_tensor_transform(finite).unwrap();
        assert_eq!(tensor[tensor_index(2, 2, 2)], fixture_leading_xyz());
        assert_eq!(tensor_index(1, 2, 0), 15);
    }

    #[test]
    fn cpu_quadratic_transform_is_axis_order_independent() {
        let finite = evaluate_fixture_on_grid([0, 1, 2]);
        let expected = quadratic_tensor_transform(finite).unwrap();
        for order in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            assert_eq!(
                quadratic_tensor_transform_with_order(finite, order).unwrap(),
                expected,
                "axis order {order:?}",
            );
        }
    }

    #[test]
    fn cpu_point_three_rejects_a_cubic_peeled_axis() {
        let values = evaluate_cubic_fixture_on_grid([0, 1, 2, 3]);
        assert!(matches!(
            assert_degree_two_at_three(&values),
            Err(R0ReferenceError::DegreeAboveTwo { axis: 0, .. })
        ));
    }

    #[test]
    fn cpu_compiler_convention_is_not_the_direct_polynomial() {
        // P(t) = 5 + 7t + 11t^2.  R is the multilinear extension of P's
        // Boolean values, and the compiler convention is Q(t) = R(t)+11t^2.
        // Thus Q(1)=34 while P(1)=23: the two diagnostics are intentionally
        // distinct even though their infinity coefficient agrees.
        let mut p_finite = [E4::ZERO; 27];
        let mut q_finite = [E4::ZERO; 27];
        for x0 in 0..3 {
            for x1 in 0..3 {
                for x2 in 0..3 {
                    let t = x2 as u32;
                    p_finite[tensor_index(x0, x1, x2)] = lift_u32(5 + 7 * t + 11 * t * t);
                    q_finite[tensor_index(x0, x1, x2)] = lift_u32(5 + 18 * t + 11 * t * t);
                }
            }
        }
        let p = quadratic_tensor_transform(p_finite).unwrap();
        let q = quadratic_tensor_transform(q_finite).unwrap();
        assert_eq!(p[tensor_index(0, 0, 1)], lift_u32(23));
        assert_eq!(q[tensor_index(0, 0, 1)], lift_u32(34));
        assert_eq!(p[tensor_index(0, 0, 2)], lift_u32(11));
        assert_eq!(q[tensor_index(0, 0, 2)], lift_u32(11));
        assert_ne!(p, q);
    }

    fn load_reference_cases() -> Vec<(
        FrozenR0Coordinate,
        gkr_eval_ir::DagLayer,
        gpu_gkr_compiler::backward::R0LayerProgram,
    )> {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let mut cases = Vec::new();
        for layout in CORPUS {
            let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../../cs/compiled_circuits")
                .join(layout);
            let bytes = std::fs::read(path).unwrap();
            let artifact: GKRCircuitArtifact<BF> = serde_json::from_slice(&bytes).unwrap();
            let dag = gkr_eval_ir::lower_dag(&artifact).unwrap();
            gkr_eval_ir::validate(&dag).unwrap();
            let compiled = compile_r0(&dag).unwrap();
            let circuit = layout.strip_suffix("_layout_gkr.json").unwrap();
            for program in compiled.layers {
                let coordinate = bundle
                    .coordinates
                    .iter()
                    .find(|coordinate| {
                        coordinate.circuit == circuit && coordinate.layer as usize == program.layer
                    })
                    .unwrap()
                    .clone();
                cases.push((coordinate, dag.layers[program.layer].clone(), program));
            }
        }
        cases.sort_by(|left, right| {
            (&left.0.circuit, left.0.layer).cmp(&(&right.0.circuit, right.0.layer))
        });
        assert_eq!(cases.len(), 57);
        cases
    }

    fn assert_reference_case(
        coordinate: &FrozenR0Coordinate,
        layer: &gkr_eval_ir::DagLayer,
        program: &gpu_gkr_compiler::backward::R0LayerProgram,
        log_trace: u32,
        seed: u64,
    ) -> (String, u64, u64, u64) {
        let context = format!(
            "{}:{} log={log_trace} seed={seed}",
            coordinate.circuit, coordinate.layer
        );
        let input = build_r0_input_with_layer(coordinate, layer, log_trace, seed)
            .unwrap_or_else(|error| panic!("{context} input failed: {error:?}"));
        let p = evaluate_true_canonical_tensor(layer, &coordinate.binding, &input)
            .unwrap_or_else(|error| panic!("{context} direct P failed: {error:?}"));
        let q = evaluate_canonical_r0_convention(layer, &coordinate.binding, &input)
            .unwrap_or_else(|error| panic!("{context} canonical Q failed: {error:?}"));
        let compiled = evaluate_compiled_r0_tensor(program, &input)
            .unwrap_or_else(|error| panic!("{context} compiled Q failed: {error:?}"));
        assert_eq!(
            q, compiled,
            "{}:{} log={log_trace} seed={seed}",
            coordinate.circuit, coordinate.layer
        );
        for x0 in 0..3 {
            for x1 in 0..3 {
                if x0 == 2 || x1 == 2 {
                    for x2 in 0..3 {
                        let index = tensor_index(x0, x1, x2);
                        assert_eq!(q[index], compiled[index]);
                    }
                }
            }
        }
        let mut delta = [E4::ZERO; 27];
        for index in 0..27 {
            delta[index] = p[index];
            delta[index].sub_assign(&q[index]);
        }
        (
            input.identity.input_sha256,
            r0_output_checksum(&p),
            r0_output_checksum(&q),
            r0_output_checksum(&delta),
        )
    }

    #[test]
    fn cpu_r0_reference_log3_seed_zero_covers_every_coordinate_and_infinity_selector() {
        for (coordinate, layer, program) in load_reference_cases() {
            let _ = assert_reference_case(&coordinate, &layer, &program, 3, 0);
        }
    }

    #[test]
    fn cpu_r0_reference_add_sub_layer0_log3_seed_zero() {
        let (coordinate, layer, program) = load_reference_cases()
            .into_iter()
            .find(|(coordinate, _, _)| {
                coordinate.circuit == "add_sub_lui_auipc_mop" && coordinate.layer == 0
            })
            .unwrap();
        let _ = assert_reference_case(&coordinate, &layer, &program, 3, 0);
    }

    #[test]
    fn full_r0_reference_corpus() {
        let cases = load_reference_cases();
        let mut pinned = Vec::new();
        for (case_index, (coordinate, layer, program)) in cases.iter().enumerate() {
            for log_trace in [3, 8] {
                for seed in [0, 1, 0x6a09_e667_f3bc_c909] {
                    let diagnostics =
                        assert_reference_case(coordinate, layer, program, log_trace, seed);
                    if matches!(
                        (case_index, log_trace, seed),
                        (0, 3, 0) | (28, 8, 1) | (56, 8, 0x6a09_e667_f3bc_c909)
                    ) {
                        pinned.push(diagnostics.0.clone());
                    }
                    println!(
                        "{}:{} log={log_trace} seed={seed} input={} p={:016x} q={:016x} delta={:016x}",
                        coordinate.circuit,
                        coordinate.layer,
                        diagnostics.0,
                        diagnostics.1,
                        diagnostics.2,
                        diagnostics.3,
                    );
                }
            }
        }
        assert_eq!(
            pinned,
            [
                "c21c5052ea5d96cfaaad0965fd4aa0d4e38897269013ca34846f28e76a572d38",
                "2e14357d27a9d8cebff82301cc661a18ab4e7e820ffae39f7978e7ffd5e2858a",
                "0568d7eb6959a517c9929667c0fa91e7c3509a3331f87583365d7c082156ab39",
            ]
        );
    }
}
