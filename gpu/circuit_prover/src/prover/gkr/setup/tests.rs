use std::alloc::Global;
use std::ops::DerefMut;
use std::ptr::null;
use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use fft::materialize_powers_serial_starting_with_one;

use itertools::Itertools;

use serial_test::serial;
use worker::Worker;

use super::*;
use crate::ops::simple::set_by_ref;
use crate::primitives::field::E4;
use crate::prover::test_utils::make_test_context;
use crate::upstream::{
    ColumnMajorMerkleTreeConstructor, DefaultTreeConstructor, FieldExtension,
    MerkleTreeCapVarLength, PrimeField, VirtualSetupPoly,
};

impl GpuGKRForwardSetup<E4> {
    pub(crate) fn for_test_generic_lookup(
        context: &ProverContext,
        lookup_additive_challenge: E4,
        generic_lookup_values: &[E4],
        decoder_lookup_fill_value: E4,
    ) -> CudaResult<Self> {
        let mut d_lookup_challenges = context.alloc(3, AllocationPlacement::BestFit)?;
        memory_copy_async(
            &mut d_lookup_challenges,
            &[E4::ONE, lookup_additive_challenge, E4::ZERO][..],
            context.get_exec_stream(),
        )?;
        crate::prover::gkr::forward::kernels::schedule_lookup_gamma_consts_prelude_e4(
            d_lookup_challenges[1..2].as_ptr(),
            context,
        )?;

        let mut device_decoder_lookup_fill_value =
            context.alloc::<E4>(1, AllocationPlacement::BestFit)?;
        memory_copy_async(
            &mut device_decoder_lookup_fill_value,
            &[decoder_lookup_fill_value],
            context.get_exec_stream(),
        )?;

        let generic_lookup = if generic_lookup_values.is_empty() {
            None
        } else {
            let mut device =
                context.alloc::<E4>(generic_lookup_values.len(), AllocationPlacement::BestFit)?;
            memory_copy_async(
                &mut device,
                generic_lookup_values,
                context.get_exec_stream(),
            )?;
            Some(device)
        };
        context.get_exec_stream().synchronize()?;

        Ok(Self {
            _tracing_ranges: Vec::new(),
            _callbacks: Callbacks::new(),
            d_lookup_challenges,
            device_decoder_lookup_fill_value,
            generic_lookup,
        })
    }
}

fn make_test_cpu_setup(
    trace_len: usize,
    generic_lookup_width: usize,
    total_tables_size: usize,
) -> CpuGKRSetup<BF> {
    let mut columns = Vec::with_capacity(generic_lookup_width);
    for _ in 0..generic_lookup_width {
        columns.push(vec![BF::ZERO; trace_len].into_boxed_slice());
    }

    for row in 0..total_tables_size {
        for column in 0..generic_lookup_width {
            columns[column][row] = BF::from_u32_unchecked(10 * (column as u32 + 1) + row as u32);
        }
    }

    CpuGKRSetup {
        hypercube_evals: columns.into_iter().map(Arc::new).collect(),
    }
}

fn flatten_setup(setup: &CpuGKRSetup<BF>) -> Vec<BF> {
    if setup.hypercube_evals.is_empty() {
        return Vec::new();
    }
    let trace_len = setup.hypercube_evals[0].len();
    let mut result = vec![BF::ZERO; setup.hypercube_evals.len() * trace_len];
    for (column_idx, column) in setup.hypercube_evals.iter().enumerate() {
        let range = column_idx * trace_len..(column_idx + 1) * trace_len;
        result[range].copy_from_slice(column.as_ref());
    }
    result
}

fn stage1_caps_from_unified_host_cap(
    unified_cap: &[Digest],
    log_lde_factor: u32,
) -> Vec<MerkleTreeCapVarLength> {
    let lde_factor = 1usize << log_lde_factor;
    debug_assert_eq!(unified_cap.len() % lde_factor, 0);
    let per_coset = unified_cap.len() / lde_factor;
    (0..lde_factor)
        .map(|stage1_pos| MerkleTreeCapVarLength {
            cap: unified_cap[stage1_pos * per_coset..(stage1_pos + 1) * per_coset].to_vec(),
        })
        .collect_vec()
}

fn materialize_trace_holder_from_values(
    values: &[BF],
    columns_count: usize,
    trace_len: usize,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
    context: &ProverContext,
) -> TraceHolder<BF> {
    let mut source = context
        .alloc(values.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut source, values, context.get_exec_stream()).unwrap();
    let mut trace_holder = TraceHolder::<BF>::new(
        trace_len.trailing_zeros(),
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        columns_count,
        TreesCacheMode::CachePartial,
        context,
    )
    .unwrap();
    trace_holder
        .materialize_and_commit_from_hypercube_evals(&source, context)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    trace_holder
}

fn copy_base_poly_from_storage(
    storage: &GpuGKRStorage<BF, E4>,
    address: GKRAddress,
    context: &ProverContext,
) -> Vec<BF> {
    let poly = storage.get_base_layer(address);
    let mut tmp = context
        .alloc(poly.len(), AllocationPlacement::BestFit)
        .unwrap();
    set_by_ref(
        &poly.as_device_chunk(),
        tmp.deref_mut(),
        context.get_exec_stream(),
    )
    .unwrap();
    let mut host = vec![BF::ZERO; poly.len()];
    memory_copy_async(&mut host, &tmp, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

fn read_ext_allocation(values: &DeviceAllocation<E4>, context: &ProverContext) -> Vec<E4> {
    let mut host = vec![E4::ZERO; values.len()];
    memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

fn expected_generic_lookup_preprocessing(
    setup: &CpuGKRSetup<BF>,
    generic_lookup_width: usize,
    generic_lookup_len: usize,
    lookup_alpha: E4,
) -> Vec<E4> {
    let powers = materialize_powers_serial_starting_with_one::<E4, Global>(
        lookup_alpha,
        generic_lookup_width,
    );
    let mut result = Vec::with_capacity(generic_lookup_len);
    for row in 0..generic_lookup_len {
        let mut value = E4::ZERO;
        for column in 0..generic_lookup_width {
            let mut contribution = powers[column];
            contribution.mul_assign_by_base(&setup.hypercube_evals[column][row]);
            value.add_assign(&contribution);
        }
        result.push(value);
    }
    result
}

fn launch_generic_lookup_preprocessing(
    setup: &CpuGKRSetup<BF>,
    generic_lookup_width: usize,
    generic_lookup_len: usize,
    lookup_alpha: E4,
    context: &ProverContext,
) -> Vec<E4> {
    let log_lde_factor = 1u32;
    let log_rows_per_leaf = 1u32;
    let log_tree_cap_size = 1u32;
    let host = Arc::new(
        GpuGKRSetupHost::precompute_from_cpu_setup(
            setup,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            context,
        )
        .unwrap(),
    );
    let mut transfer = GpuGKRSetupTransfer::new(Arc::clone(&host), context).unwrap();
    let _h2d = crate::prover::transfer::single_shot_h2d(
        |t| transfer.schedule_transfer(t, context),
        context,
    )
    .unwrap();
    context.get_h2d_stream().synchronize().unwrap();

    let mut device_lookup_alpha = context.alloc(1, AllocationPlacement::BestFit).unwrap();
    memory_copy_async(
        &mut device_lookup_alpha,
        &[lookup_alpha],
        context.get_exec_stream(),
    )
    .unwrap();
    schedule_lookup_alpha_powers_prelude(
        device_lookup_alpha.as_ptr(),
        generic_lookup_width,
        context,
    )
    .unwrap();
    let mut generic_lookup = context
        .alloc(generic_lookup_len, AllocationPlacement::BestFit)
        .unwrap();
    let batch = lower_forward_setup_generic_lookup_batch(
        host.as_ref(),
        transfer.trace_holder.get_hypercube_evals(),
        generic_lookup_width,
        &mut generic_lookup,
    );
    launch_forward_setup_generic_lookup::<E4>(&batch, generic_lookup_len, context).unwrap();

    read_ext_allocation(&generic_lookup, context)
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn setup_host_matches_flattened_cpu_setup_and_caps() {
    let trace_len = 1usize << 16;
    let lde_factor = 2usize;
    let tree_cap_size = 4usize;
    let log_lde_factor = lde_factor.trailing_zeros();
    let log_rows_per_leaf = 1u32;
    let log_tree_cap_size = tree_cap_size.trailing_zeros();
    let setup = make_test_cpu_setup(trace_len, 3, 64);
    let context = make_test_context(256, 64);

    let host = GpuGKRSetupHost::precompute_from_cpu_setup(
        &setup,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        &context,
    )
    .unwrap();

    assert_eq!(&host.raw_hypercube_evals[..], flatten_setup(&setup));

    let worker = Worker::new();
    let twiddles: fft::Twiddles<BF, Global> = fft::Twiddles::new(trace_len, &worker);
    let setup_commitment = setup.commit(
        &twiddles,
        lde_factor,
        log_rows_per_leaf as usize,
        tree_cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );
    let subcap_size = tree_cap_size / lde_factor;
    let setup_caps = <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
        &setup_commitment.tree,
    )
    .cap
    .chunks_exact(subcap_size)
    .map(|chunk| MerkleTreeCapVarLength {
        cap: chunk.to_vec(),
    })
    .collect_vec();
    assert_eq!(
        stage1_caps_from_unified_host_cap(&host.unified_tree_cap[..], log_lde_factor),
        setup_caps
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn setup_transfer_reuses_single_raw_backing_and_lazy_queries_match_fresh_commit() {
    let trace_len = 1usize << 10;
    let lde_factor = 2usize;
    let tree_cap_size = 4usize;
    let log_lde_factor = lde_factor.trailing_zeros();
    let log_rows_per_leaf = 1u32;
    let log_tree_cap_size = tree_cap_size.trailing_zeros();
    let setup = make_test_cpu_setup(trace_len, 3, 32);
    let context = make_test_context(256, 64);

    let host = Arc::new(
        GpuGKRSetupHost::precompute_from_cpu_setup(
            &setup,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            &context,
        )
        .unwrap(),
    );
    let mut transfer = GpuGKRSetupTransfer::new(host, &context).unwrap();
    let _h2d = crate::prover::transfer::single_shot_h2d(
        |t| transfer.schedule_transfer(t, &context),
        &context,
    )
    .unwrap();
    context.get_h2d_stream().synchronize().unwrap();

    let mut raw = vec![BF::ZERO; transfer.trace_holder.get_hypercube_evals().len()];
    memory_copy_async(
        &mut raw,
        transfer.trace_holder.get_hypercube_evals(),
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(raw, flatten_setup(&setup));
    assert!(!transfer.trace_holder.are_cosets_materialized());

    let mut storage = GpuGKRStorage::<BF, crate::primitives::field::E4>::default();
    transfer.bind_setup_columns_into_storage(&mut storage);
    let first_poly = storage.get_base_layer(GKRAddress::Setup(0)).clone_shared();
    for column in 0..setup.hypercube_evals.len() {
        let poly = storage.get_base_layer(GKRAddress::Setup(column));
        assert_eq!(poly.offset(), column * trace_len);
        assert_eq!(poly.len(), trace_len);
        assert!(poly.shares_backing_with(&first_poly));
    }

    let mut fresh_source = context
        .alloc(raw.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut fresh_source, &raw, context.get_exec_stream()).unwrap();
    let mut fresh_holder = TraceHolder::<BF>::new(
        trace_len.trailing_zeros(),
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        setup.hypercube_evals.len(),
        TreesCacheMode::CachePartial,
        &context,
    )
    .unwrap();
    fresh_holder
        .materialize_and_commit_from_hypercube_evals(&fresh_source, &context)
        .unwrap();

    let query_indexes = vec![0u32, 3, 17, 31];
    let mut indexes_device = context
        .alloc(query_indexes.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(
        &mut indexes_device,
        &query_indexes,
        context.get_exec_stream(),
    )
    .unwrap();

    // The earlier `single_shot_h2d` + `h2d_stream.synchronize()` already make
    // the H2D visible on exec_stream for subsequent host-issued kernels.
    let transferred_queries = transfer
        .trace_holder
        .get_leafs_and_merkle_paths(1, &indexes_device, &context)
        .unwrap();
    let fresh_queries = fresh_holder
        .get_leafs_and_merkle_paths(1, &indexes_device, &context)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    assert!(transfer.trace_holder.are_cosets_materialized());
    assert_eq!(
        unsafe { transferred_queries.leafs.get_accessor().get() },
        unsafe { fresh_queries.leafs.get_accessor().get() }
    );
    assert_eq!(
        unsafe { transferred_queries.merkle_paths.get_accessor().get() },
        unsafe { fresh_queries.merkle_paths.get_accessor().get() }
    );
    assert_eq!(
        transfer
            .trace_holder
            .read_per_coset_caps_synchronously(&context)
            .unwrap(),
        fresh_holder
            .read_per_coset_caps_synchronously(&context)
            .unwrap()
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn bootstrap_storage_binds_setup_memory_and_witness_trace_holders() {
    let trace_len = 1usize << 10;
    let lde_factor = 2usize;
    let tree_cap_size = 4usize;
    let log_lde_factor = lde_factor.trailing_zeros();
    let log_rows_per_leaf = 1u32;
    let log_tree_cap_size = tree_cap_size.trailing_zeros();
    let setup = make_test_cpu_setup(trace_len, 2, 32);
    let context = make_test_context(256, 64);

    let host = Arc::new(
        GpuGKRSetupHost::precompute_from_cpu_setup(
            &setup,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            &context,
        )
        .unwrap(),
    );
    let mut transfer = GpuGKRSetupTransfer::new(host, &context).unwrap();
    let _h2d = crate::prover::transfer::single_shot_h2d(
        |t| transfer.schedule_transfer(t, &context),
        &context,
    )
    .unwrap();
    context.get_h2d_stream().synchronize().unwrap();

    let memory_columns = 2usize;
    let witness_columns = 3usize;
    let memory_values = (0..memory_columns * trace_len)
        .map(|i| BF::from_u32_unchecked(i as u32 + 1))
        .collect_vec();
    let witness_values = (0..witness_columns * trace_len)
        .map(|i| BF::from_u32_unchecked(i as u32 + 1000))
        .collect_vec();
    let memory_trace_holder = materialize_trace_holder_from_values(
        &memory_values,
        memory_columns,
        trace_len,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        &context,
    );
    let witness_trace_holder = materialize_trace_holder_from_values(
        &witness_values,
        witness_columns,
        trace_len,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        &context,
    );

    let storage = transfer
        .bootstrap_storage::<E4>(&memory_trace_holder, &witness_trace_holder, &context)
        .unwrap();
    assert_eq!(storage.layers.len(), 1);
    assert!(storage.layers[0].extension_field_inputs.is_empty());

    for column in 0..setup.hypercube_evals.len() {
        let poly = storage.get_base_layer(GKRAddress::Setup(column));
        assert_eq!(poly.offset(), column * trace_len);
        assert_eq!(
            copy_base_poly_from_storage(&storage, GKRAddress::Setup(column), &context),
            &setup.hypercube_evals[column][..]
        );
    }
    for address in [
        GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
        GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp),
        GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
        GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
    ] {
        assert!(
            storage.try_get_base_poly(address).is_none(),
            "virtual setup source {:?} should not be materialized in storage",
            address
        );
    }
    for column in 0..memory_columns {
        let expected = &memory_values[column * trace_len..(column + 1) * trace_len];
        assert_eq!(
            copy_base_poly_from_storage(&storage, GKRAddress::BaseLayerMemory(column), &context),
            expected,
        );
    }
    for column in 0..witness_columns {
        let expected = &witness_values[column * trace_len..(column + 1) * trace_len];
        assert_eq!(
            copy_base_poly_from_storage(&storage, GKRAddress::BaseLayerWitness(column), &context),
            expected,
        );
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn bootstrap_storage_without_uploaded_setup_leaves_virtual_setup_unmaterialized() {
    let trace_len = 1usize << 19;
    let log_lde_factor = 1u32;
    let log_rows_per_leaf = 1u32;
    let log_tree_cap_size = 1u32;
    let context = make_test_context(256, 64);
    let memory_values = (0..trace_len)
        .map(|i| BF::from_u32_unchecked(i as u32 + 1))
        .collect_vec();
    let memory_trace_holder = materialize_trace_holder_from_values(
        &memory_values,
        1,
        trace_len,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        &context,
    );
    let witness_trace_holder = materialize_trace_holder_from_values(
        &[],
        0,
        trace_len,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        &context,
    );

    let storage = bootstrap_storage_from_trace_holders::<E4>(
        None,
        0,
        trace_len.trailing_zeros(),
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        &memory_trace_holder,
        &witness_trace_holder,
        &context,
    )
    .unwrap();

    for address in [
        GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
        GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp),
        GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
        GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
    ] {
        assert!(
            storage.try_get_base_poly(address).is_none(),
            "virtual setup source {:?} should not be materialized in storage",
            address
        );
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn forward_setup_generic_lookup_fused_kernel_matches_expected_for_max_width() {
    let trace_len = 1usize << 10;
    let generic_lookup_width = GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS;
    let generic_lookup_len = 64;
    let setup = make_test_cpu_setup(trace_len, generic_lookup_width, generic_lookup_len);
    let context = make_test_context(256, 64);
    let lookup_alpha = E4::from_array_of_base([BF::new(3), BF::new(5), BF::new(7), BF::new(11)]);

    let actual = launch_generic_lookup_preprocessing(
        &setup,
        generic_lookup_width,
        generic_lookup_len,
        lookup_alpha,
        &context,
    );
    let expected = expected_generic_lookup_preprocessing(
        &setup,
        generic_lookup_width,
        generic_lookup_len,
        lookup_alpha,
    );

    assert_eq!(actual, expected);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn forward_setup_generic_lookup_fused_kernel_handles_single_column() {
    let trace_len = 1usize << 8;
    let generic_lookup_width = 1;
    let generic_lookup_len = 32;
    let setup = make_test_cpu_setup(trace_len, generic_lookup_width, generic_lookup_len);
    let context = make_test_context(256, 64);
    let lookup_alpha = E4::from_array_of_base([BF::new(13), BF::new(17), BF::new(19), BF::new(23)]);

    let actual = launch_generic_lookup_preprocessing(
        &setup,
        generic_lookup_width,
        generic_lookup_len,
        lookup_alpha,
        &context,
    );
    let expected = expected_generic_lookup_preprocessing(
        &setup,
        generic_lookup_width,
        generic_lookup_len,
        lookup_alpha,
    );

    assert_eq!(actual, expected);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn forward_setup_schedule_generic_lookup_matches_cpu() {
    let trace_len = 1usize << 10;
    let generic_lookup_width = 4;
    let generic_lookup_len = 32;
    let setup = make_test_cpu_setup(trace_len, generic_lookup_width, generic_lookup_len);
    let context = make_test_context(256, 64);
    let log_lde_factor = 1u32;
    let log_rows_per_leaf = 1u32;
    let log_tree_cap_size = 1u32;
    let host = Arc::new(
        GpuGKRSetupHost::precompute_from_cpu_setup(
            &setup,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            &context,
        )
        .unwrap(),
    );
    let mut transfer = GpuGKRSetupTransfer::new(Arc::clone(&host), &context).unwrap();
    let _h2d = crate::prover::transfer::single_shot_h2d(
        |t| transfer.schedule_transfer(t, &context),
        &context,
    )
    .unwrap();
    context.get_h2d_stream().synchronize().unwrap();

    let lookup_alpha = E4::from_array_of_base([BF::new(3), BF::new(5), BF::new(7), BF::new(11)]);
    let lookup_additive_part =
        E4::from_array_of_base([BF::new(13), BF::new(17), BF::new(19), BF::new(23)]);
    let constraints_batch_challenge =
        E4::from_array_of_base([BF::new(29), BF::new(31), BF::new(37), BF::new(41)]);
    let mut d_lookup_challenges: DeviceAllocation<E4> =
        context.alloc(3, AllocationPlacement::BestFit).unwrap();
    memory_copy_async(
        &mut d_lookup_challenges,
        &[
            lookup_alpha,
            lookup_additive_part,
            constraints_batch_challenge,
        ][..],
        context.get_exec_stream(),
    )
    .unwrap();

    let scheduled = schedule_forward_setup_for_shape::<E4>(
        Some((&transfer.trace_holder, transfer.host.columns_count)),
        trace_len,
        generic_lookup_width,
        generic_lookup_len,
        false,
        d_lookup_challenges,
        &context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let actual_generic_lookup = read_ext_allocation(
        scheduled
            .generic_lookup
            .as_ref()
            .expect("expected generic lookup"),
        &context,
    );
    let expected_generic_lookup = expected_generic_lookup_preprocessing(
        &setup,
        generic_lookup_width,
        generic_lookup_len,
        lookup_alpha,
    );
    assert_eq!(actual_generic_lookup, expected_generic_lookup);
}

#[test]
#[should_panic(expected = "exceeding the fused setup cap")]
fn forward_setup_generic_lookup_batch_panics_when_width_exceeds_cap() {
    let setup_columns = vec![null(); GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS + 1];
    let _ =
        pack_forward_setup_generic_lookup_batch::<E4>(&setup_columns, null_mut(), null_mut(), 0);
}
