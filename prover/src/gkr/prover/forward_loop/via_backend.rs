//! Forward relations routed through the [`GKRBackend`] archetype methods:
//! fetch the input columns from the storage, allocate the outputs from the
//! pool, let the backend fill them, insert. On `x86_64 + avx2` builds the
//! historical AVX-512 fast paths keep precedence (they are byte-identical and
//! already tuned); every other target reaches the backend, whose defaults are
//! the portable scalar maps.

use super::*;
use crate::allocation_pool::AllocationType;
use crate::gkr::prover::gkr_backend::{AffinePlan, GKRBackend};
use cs::definitions::gkr::AddressSpaceType;
use cs::gkr_compiler::SpecialMemoryContributionRelation;

fn alloc_outputs<F: PrimeField, E: FieldExtension<F> + Field, const N: usize>(
    trace_len: usize,
    pool: &dyn AllocationPool<F, E>,
) -> [crate::allocation_pool::Buffer<E>; N] {
    core::array::from_fn(|_| pool.alloc_ext(trace_len, ColumnLayout::Contiguous))
}

fn insert_outputs<F: PrimeField, E: FieldExtension<F> + Field, const N: usize>(
    gkr_storage: &mut GKRStorage<F, E>,
    layer: usize,
    outputs: [GKRAddress; N],
    buffers: [crate::allocation_pool::Buffer<E>; N],
) {
    for (output, buffer) in outputs.into_iter().zip(buffers) {
        output.assert_as_layer(layer);
        gkr_storage.insert_extension_at_layer(layer, output, unsafe {
            ExtensionFieldPoly::from_pooled(buffer)
        });
    }
}

fn ext<F: PrimeField, E: FieldExtension<F> + Field>(
    gkr_storage: &GKRStorage<F, E>,
    address: GKRAddress,
) -> &[E] {
    gkr_storage
        .try_get_ext_poly(address)
        .unwrap_or_else(|| panic!("ext poly at {:?}", address))
}

fn base<F: PrimeField, E: FieldExtension<F> + Field>(
    gkr_storage: &GKRStorage<F, E>,
    address: GKRAddress,
) -> &[F] {
    gkr_storage
        .try_get_base_poly(address)
        .unwrap_or_else(|| panic!("base poly at {:?}", address))
}

/// AggregateLookupRationalPair: `[[a, b], [c, d]] -> (a d + c b, b d)`.
pub(crate) fn rational_pair_add<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    GB: GKRBackend<F, E>,
>(
    gb: &GB,
    inputs: [[GKRAddress; 2]; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    if super::avx512::enabled::<F, E>(trace_len) {
        return super::lookup_pair::forward_evaluate_lookup_pair(
            inputs,
            outputs,
            gkr_storage,
            expected_output_layer,
            trace_len,
            pool,
            worker,
        );
    }
    let mut outs = alloc_outputs::<F, E, 2>(trace_len, pool);
    {
        let [[a, b], [c, d]] = inputs;
        let a = ext(gkr_storage, a);
        let b = ext(gkr_storage, b);
        let c = ext(gkr_storage, c);
        let d = ext(gkr_storage, d);
        let [num, den] = &mut outs;
        gb.forward_rational_pair_add(a, b, c, d, num.as_mut(), den.as_mut(), worker);
    }
    insert_outputs(gkr_storage, expected_output_layer, outputs, outs);
}

/// TrivialProduct / InitialGrandProductFromCaches: `a b`.
pub(crate) fn ext_product<F: PrimeField, E: FieldExtension<F> + Field, GB: GKRBackend<F, E>>(
    gb: &GB,
    inputs: [GKRAddress; 2],
    output: GKRAddress,
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    if super::avx512::enabled::<F, E>(trace_len) {
        return super::pairwise_product::forward_evaluate_pairwise_product(
            inputs,
            output,
            gkr_storage,
            expected_output_layer,
            trace_len,
            pool,
            worker,
        );
    }
    let mut outs = alloc_outputs::<F, E, 1>(trace_len, pool);
    {
        let a = ext(gkr_storage, inputs[0]);
        let b = ext(gkr_storage, inputs[1]);
        gb.forward_ext_product(a, b, outs[0].as_mut(), worker);
    }
    insert_outputs(gkr_storage, expected_output_layer, [output], outs);
}

/// LookupPairFromMaterializedBaseInputs.
pub(crate) fn base_pair_lookup<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    GB: GKRBackend<F, E>,
>(
    gb: &GB,
    inputs: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    gamma: E,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    if super::avx512::enabled::<F, E>(trace_len) {
        return super::lookup_from_base_inputs::forward_evaluate_lookup_base_inputs_pair(
            inputs,
            outputs,
            gkr_storage,
            expected_output_layer,
            trace_len,
            gamma,
            pool,
            worker,
        );
    }
    let mut outs = alloc_outputs::<F, E, 2>(trace_len, pool);
    {
        let b = base(gkr_storage, inputs[0]);
        let d = base(gkr_storage, inputs[1]);
        let [num, den] = &mut outs;
        gb.forward_base_pair_lookup(b, d, gamma, num.as_mut(), den.as_mut(), worker);
    }
    insert_outputs(gkr_storage, expected_output_layer, outputs, outs);
}

/// LookupPairFromMaterializedVectorInputs.
pub(crate) fn ext_pair_lookup<F: PrimeField, E: FieldExtension<F> + Field, GB: GKRBackend<F, E>>(
    gb: &GB,
    inputs: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    gamma: E,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    if super::avx512::enabled::<F, E>(trace_len) {
        return super::lookup_from_vector_inputs::forward_evaluate_lookup_from_vector_inputs_pair(
            inputs,
            outputs,
            gkr_storage,
            expected_output_layer,
            trace_len,
            gamma,
            pool,
            worker,
        );
    }
    let mut outs = alloc_outputs::<F, E, 2>(trace_len, pool);
    {
        let b = ext(gkr_storage, inputs[0]);
        let d = ext(gkr_storage, inputs[1]);
        let [num, den] = &mut outs;
        gb.forward_ext_pair_lookup(b, d, gamma, num.as_mut(), den.as_mut(), worker);
    }
    insert_outputs(gkr_storage, expected_output_layer, outputs, outs);
}

/// LookupUnbalancedPairWithMaterializedBaseInputs: `[a, b]` ext, `remainder` base.
pub(crate) fn unbalanced_base_lookup<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    GB: GKRBackend<F, E>,
>(
    gb: &GB,
    inputs: [GKRAddress; 2],
    remainder: GKRAddress,
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    gamma: E,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    if super::avx512::enabled::<F, E>(trace_len) {
        return super::lookup_from_base_inputs::forward_evaluate_lookup_rational_with_base_remainder_input(
            inputs,
            remainder,
            outputs,
            gkr_storage,
            expected_output_layer,
            trace_len,
            gamma,
            pool,
            worker,
        );
    }
    let mut outs = alloc_outputs::<F, E, 2>(trace_len, pool);
    {
        let a = ext(gkr_storage, inputs[0]);
        let b = ext(gkr_storage, inputs[1]);
        let d = base(gkr_storage, remainder);
        let [num, den] = &mut outs;
        gb.forward_unbalanced_base_lookup(a, b, d, gamma, num.as_mut(), den.as_mut(), worker);
    }
    insert_outputs(gkr_storage, expected_output_layer, outputs, outs);
}

/// LookupUnbalancedPairWithMaterializedVectorInputs: `[a, b]` ext, `remainder` ext.
pub(crate) fn unbalanced_ext_lookup<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    GB: GKRBackend<F, E>,
>(
    gb: &GB,
    inputs: [GKRAddress; 2],
    remainder: GKRAddress,
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    gamma: E,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    if super::avx512::enabled::<F, E>(trace_len) {
        return super::lookup_from_vector_inputs::forward_evaluate_lookup_rational_with_vector_remainder_input(
            inputs,
            remainder,
            outputs,
            gkr_storage,
            expected_output_layer,
            trace_len,
            gamma,
            pool,
            worker,
        );
    }
    let mut outs = alloc_outputs::<F, E, 2>(trace_len, pool);
    {
        let a = ext(gkr_storage, inputs[0]);
        let b = ext(gkr_storage, inputs[1]);
        let d = ext(gkr_storage, remainder);
        let [num, den] = &mut outs;
        gb.forward_unbalanced_ext_lookup(a, b, d, gamma, num.as_mut(), den.as_mut(), worker);
    }
    insert_outputs(gkr_storage, expected_output_layer, outputs, outs);
}

/// LookupFromMaterializedBaseInputWithSetup: `input` = b, `setup` = [c, d].
pub(crate) fn base_lookup_minus_setup<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    GB: GKRBackend<F, E>,
>(
    gb: &GB,
    input: GKRAddress,
    setup: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    gamma: E,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    if super::avx512::enabled::<F, E>(trace_len) {
        return super::lookup_from_base_inputs::forward_evaluate_lookup_from_base_inputs_with_setup(
            input,
            setup,
            outputs,
            gkr_storage,
            expected_output_layer,
            trace_len,
            gamma,
            pool,
            worker,
        );
    }
    let mut outs = alloc_outputs::<F, E, 2>(trace_len, pool);
    {
        let b = base(gkr_storage, input);
        let c = base(gkr_storage, setup[0]);
        let d = base(gkr_storage, setup[1]);
        let [num, den] = &mut outs;
        gb.forward_base_lookup_minus_setup(b, c, d, gamma, num.as_mut(), den.as_mut(), worker);
    }
    insert_outputs(gkr_storage, expected_output_layer, outputs, outs);
}

/// LookupWithCachedDensAndSetup: nums `[input[0], setup[0]]` base, dens
/// `[input[1], setup[1]]` ext.
pub(crate) fn masked_ext_lookup_minus_setup<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    GB: GKRBackend<F, E>,
>(
    gb: &GB,
    input: [GKRAddress; 2],
    setup: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    gamma: E,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    if super::avx512::enabled::<F, E>(trace_len) {
        return super::lookup_from_vector_inputs::forward_evaluate_masked_lookup_from_vector_inputs_with_setup(
            input,
            setup,
            outputs,
            gkr_storage,
            expected_output_layer,
            trace_len,
            gamma,
            pool,
            worker,
        );
    }
    let mut outs = alloc_outputs::<F, E, 2>(trace_len, pool);
    {
        let a = base(gkr_storage, input[0]);
        let c = base(gkr_storage, setup[0]);
        let b = ext(gkr_storage, input[1]);
        let d = ext(gkr_storage, setup[1]);
        let [num, den] = &mut outs;
        gb.forward_masked_ext_lookup_minus_setup(
            a,
            c,
            b,
            d,
            gamma,
            num.as_mut(),
            den.as_mut(),
            worker,
        );
    }
    insert_outputs(gkr_storage, expected_output_layer, outputs, outs);
}

/// MaskIntoIdentityProduct.
pub(crate) fn mask_into_identity<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    GB: GKRBackend<F, E>,
>(
    gb: &GB,
    input: GKRAddress,
    mask: GKRAddress,
    output: GKRAddress,
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    if super::avx512::enabled::<F, E>(trace_len) {
        return super::mask_product::forward_evaluate_mask_into_identity(
            input,
            mask,
            output,
            gkr_storage,
            expected_output_layer,
            trace_len,
            pool,
            worker,
        );
    }
    let mut outs = alloc_outputs::<F, E, 1>(trace_len, pool);
    {
        let m = base(gkr_storage, mask);
        let v = ext(gkr_storage, input);
        gb.forward_mask_into_identity(m, v, outs[0].as_mut(), worker);
    }
    insert_outputs(gkr_storage, expected_output_layer, [output], outs);
}

/// One affine plan over `columns` into a fresh pooled column.
pub(crate) fn affine_plan<F: PrimeField, E: FieldExtension<F> + Field, GB: GKRBackend<F, E>>(
    gb: &GB,
    plan: &AffinePlan<F, E>,
    columns: &[&[F]],
    trace_len: usize,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) -> AllocationType<E> {
    let mut out = pool.alloc_ext(trace_len, ColumnLayout::Contiguous);
    gb.forward_affine_plan(plan, columns, out.as_mut(), worker);
    unsafe { AllocationType::from_initialized(out) }
}

/// The product of two affine plans over `columns` into a fresh pooled column.
pub(crate) fn affine_plan_product<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    GB: GKRBackend<F, E>,
>(
    gb: &GB,
    lhs: &AffinePlan<F, E>,
    rhs: &AffinePlan<F, E>,
    columns: &[&[F]],
    trace_len: usize,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) -> AllocationType<E> {
    let mut out = pool.alloc_ext(trace_len, ColumnLayout::Contiguous);
    gb.forward_affine_plan_product(lhs, rhs, columns, out.as_mut(), worker);
    unsafe { AllocationType::from_initialized(out) }
}

/// Mirror of [`utils::evaluate_memory_query`] as an [`AffinePlan`] over the
/// base-layer memory columns (column index `i` = memory column `i`); `None`
/// for the shapes that need integer arithmetic on reduced values (dynamic
/// offsets) or the generic address form, which stay on the scalar path.
pub(crate) fn compile_memory_query<F: PrimeField, E: FieldExtension<F> + Field>(
    rel: &SpecialMemoryContributionRelation,
    ch: &GKRExternalChallenges<F, E>,
) -> Option<AffinePlan<F, E>> {
    let lin = &ch.permutation_argument_linearization_challenges;
    let mut additive = ch.permutation_argument_additive_part;
    let mut plan = AffinePlan::new(E::ZERO);
    match rel.address_space {
        CompiledAddressSpaceRelationStrict::Constant(c) => {
            assert!(c < (1u32 << 16));
            additive.add_assign_base(&F::from_u32_unchecked(c));
        }
        CompiledAddressSpaceRelationStrict::IsRam(offset) => {
            plan.base(vec![(F::ONE, offset)], F::ZERO);
        }
        CompiledAddressSpaceRelationStrict::IsRegister(offset) => {
            plan.base(vec![(F::MINUS_ONE, offset)], F::ONE);
        }
    }
    match &rel.address {
        &CompiledAddressStrict::ConstantU16(c) => {
            let mut t = lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            t.mul_assign_by_base(&F::from_u32_unchecked(c as u32));
            additive.add_assign(&t);
        }
        &CompiledAddressStrict::Constant(c) => {
            assert!(c < (1u32 << 16));
            let mut t = lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            t.mul_assign_by_base(&F::from_u32_unchecked(c));
            additive.add_assign(&t);
        }
        &CompiledAddressStrict::U16Space(offset) => plan.linear(
            lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
            vec![(F::ONE, offset)],
            F::ZERO,
        ),
        &CompiledAddressStrict::U32Space([low, high]) => {
            plan.linear(
                lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
                vec![(F::ONE, low)],
                F::ZERO,
            );
            plan.linear(
                lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX],
                vec![(F::ONE, high)],
                F::ZERO,
            );
        }
        &CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            low_offset,
            high,
        } => {
            if low_dynamic_offset.is_some() {
                return None;
            }
            plan.linear(
                lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
                vec![(F::ONE, low_base)],
                F::from_u32_unchecked(low_offset),
            );
            plan.linear(
                lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX],
                vec![(F::ONE, high)],
                F::ZERO,
            );
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => return None,
    }
    match rel.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(ts) => {
            plan.linear(
                lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX],
                vec![(F::ONE, ts[0])],
                F::from_u32_unchecked(rel.timestamp_offset),
            );
            plan.linear(
                lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX],
                vec![(F::ONE, ts[1])],
                F::ZERO,
            );
        }
    }
    match rel.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(rv) => {
            plan.linear(
                lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX],
                vec![(F::ONE, rv[0])],
                F::ZERO,
            );
            plan.linear(
                lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX],
                vec![(F::ONE, rv[1])],
                F::ZERO,
            );
        }
        RamWordRepresentation::U8Limbs(b) => {
            let shift = F::from_u32_unchecked(1u32 << 8);
            plan.linear(
                lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX],
                vec![(F::ONE, b[0]), (shift, b[1])],
                F::ZERO,
            );
            plan.linear(
                lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX],
                vec![(F::ONE, b[2]), (shift, b[3])],
                F::ZERO,
            );
        }
    }
    plan.additive = additive;
    Some(plan)
}

/// Mirror of `inits_and_teardowns::evaluate_init` / `evaluate_teardown` over
/// the memory columns extended by `address_low` / `address_high` at column
/// indices `addr_low_col` / `addr_high_col`.
pub(crate) fn compile_init_or_teardown<F: PrimeField, E: FieldExtension<F> + Field>(
    ch: &GKRExternalChallenges<F, E>,
    address_high_bits: u32,
    high_bits_offset: u32,
    teardown: Option<([usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM], [usize; 2])>,
    addr_low_col: usize,
    addr_high_col: usize,
) -> AffinePlan<F, E> {
    let lin = &ch.permutation_argument_linearization_challenges;
    let mut additive = ch.permutation_argument_additive_part;
    additive.add_assign_base(&F::from_u32_unchecked(AddressSpaceType::RAM as u32));
    let mut plan = AffinePlan::new(additive);
    plan.linear(
        lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
        vec![(F::ONE, addr_low_col)],
        F::ZERO,
    );
    plan.linear(
        lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX],
        vec![(F::ONE, addr_high_col)],
        F::from_u32_unchecked(address_high_bits << high_bits_offset),
    );
    if let Some((timestamp, value)) = teardown {
        plan.linear(
            lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX],
            vec![(F::ONE, timestamp[0])],
            F::ZERO,
        );
        plan.linear(
            lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX],
            vec![(F::ONE, timestamp[1])],
            F::ZERO,
        );
        plan.linear(
            lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX],
            vec![(F::ONE, value[0])],
            F::ZERO,
        );
        plan.linear(
            lin[PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX],
            vec![(F::ONE, value[1])],
            F::ZERO,
        );
    }
    plan
}
