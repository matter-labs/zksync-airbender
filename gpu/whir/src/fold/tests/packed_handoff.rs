use super::*;
use gpu_gkr::packed_merge::launch_merge_claims_e4;
use gpu_hash::blake2s::{transcript_squeeze_fresh_e4, STATE_SIZE};
use prover::definitions::SecurityLevel;
use prover::gkr::prover::merge_claims;
use prover::gkr::prover::transcript_utils::{
    draw_fresh_random_field_els, draw_random_field_els, draw_random_field_els_with_pow,
};
use prover::gkr::prover::WhirSchedule;
use prover::gkr::prover_config::commitment_geometry::{BaseCommitmentGeometry, BaseOracleRole};
use prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture as packed_config;
use prover::gkr::prover_config::{BaseColumns, ProverConfig};
use prover::gkr::whir::hypercube_to_monomial::parallel_multivariate_hypercube_evals_into_coeffs;
use prover::transcript::{Blake2sTranscript, Seed};

fn read<T: Copy + Default>(data: &DeviceSlice<T>, context: &ProverContext) -> Vec<T> {
    let mut values = vec![T::default(); data.len()];
    if !values.is_empty() {
        memory_copy_async(&mut values, data, context.get_exec_stream()).unwrap();
    }
    context.get_exec_stream().synchronize().unwrap();
    values
}

fn handoff(k: usize) {
    handoff_for_mode(k, false);
}

fn handoff_for_mode(k: usize, merged_mode: bool) {
    let context = make_test_context(256, 16);
    let worker = Worker::new_with_num_threads(4);
    let message_log = 13usize;
    let n = message_log - k;
    let pack = 1usize << k;
    let rows = 1usize << n;
    let message = 1usize << message_log;
    let logical_widths = if merged_mode {
        [225, 538, 6]
    } else {
        [pack + 1, 2 * pack + 1, 1]
    };
    let widths = if merged_mode {
        [logical_widths[0] + logical_widths[1], 0, logical_widths[2]]
    } else {
        logical_widths
    };
    let mut config = ProverConfig::whir_only(
        message_log,
        WhirSchedule::from_legacy_arrays(2, 16, 0, &[1, 5], &[1, 1], &[2], &[0, 0]),
        SecurityLevel::Sec100,
    );
    if merged_mode {
        config.commitment_mode = prover::gkr::prover_config::CommitmentMode::MergedMemoryAndWitness;
    }
    config.trace_len_log2 = n;
    config.whir_schedule.base_round.physical_packing_log2 = k;
    let geometry = BaseCommitmentGeometry::from_config(
        &config,
        BaseColumns {
            memory: logical_widths[0],
            witness: logical_widths[1],
            setup: logical_widths[2],
        },
    )
    .unwrap();
    let logical_point: Vec<_> = (0..n).map(|i| sample_ext(19 + 13 * i as u32)).collect();
    let unmerged_raw: [Vec<BF>; 3] = std::array::from_fn(|role| {
        (0..logical_widths[role] * rows)
            .map(|i| BF::new((i as u32 * 73 + role as u32 * 101 + 7) % 100003))
            .collect()
    });
    let unmerged_claims: [Vec<E4>; 3] = std::array::from_fn(|role| {
        unmerged_raw[role]
            .chunks_exact(rows)
            .map(|column| {
                let mut values: Vec<E4> = column.iter().copied().map(E4::from_base).collect();
                for r in &logical_point {
                    fold_evaluation_form_for_test(&mut values, *r);
                }
                values[0]
            })
            .collect()
    });
    let logical_claims = if merged_mode {
        [
            unmerged_claims[0]
                .iter()
                .chain(&unmerged_claims[1])
                .copied()
                .collect(),
            Vec::new(),
            unmerged_claims[2].clone(),
        ]
    } else {
        unmerged_claims.clone()
    };
    let raw = if merged_mode {
        [
            [unmerged_raw[0].as_slice(), unmerged_raw[1].as_slice()].concat(),
            Vec::new(),
            unmerged_raw[2].clone(),
        ]
    } else {
        unmerged_raw
    };
    if merged_mode {
        assert_eq!(&logical_claims[0][225..], &unmerged_claims[1]);
        assert_eq!(
            geometry.oracle(BaseOracleRole::Memory).physical_columns(),
            48
        );
        assert_eq!(
            geometry.oracle(BaseOracleRole::Witness).physical_columns(),
            0
        );
        assert_eq!(geometry.total_physical_columns(), 49);
    }
    // Reproduce the preceding GKR draw so the negative control is anchored at
    // the boundary that must advance past an already emitted digest.
    let mut seed = Seed(std::array::from_fn(|i| {
        0x1234_5678u32.wrapping_add(0x1723_4567u32.wrapping_mul(i as u32))
    }));
    let _preceding = draw_random_field_els::<BF, E4, Blake2sTranscript>(&mut seed, 1);
    let boundary_seed = seed;
    let mut device_seed = alloc_and_copy(&seed.0, &context);
    assert_eq!(read(&device_seed, &context), boundary_seed.0);
    let mut expected_point = logical_point.clone();
    let coordinates = if k == 0 {
        Vec::new()
    } else {
        let mut plain_seed = boundary_seed;
        let plain = draw_random_field_els::<BF, E4, Blake2sTranscript>(&mut plain_seed, k);
        let fresh = draw_fresh_random_field_els::<BF, E4, Blake2sTranscript>(&mut seed, k);
        assert_ne!(
            plain, fresh,
            "plain squeeze must not satisfy the packing oracle"
        );
        assert_ne!(plain_seed.0, seed.0);
        fresh
    };
    expected_point.extend_from_slice(&coordinates);
    let mut device_point = alloc_and_copy(&vec![E4::ZERO; message_log], &context);
    memory_copy_async(
        &mut device_point[..n],
        &logical_point,
        context.get_exec_stream(),
    )
    .unwrap();
    if k != 0 {
        transcript_squeeze_fresh_e4(
            &mut device_seed,
            &mut device_point[n..],
            context.get_exec_stream(),
        )
        .unwrap();
    }
    assert_eq!(read(&device_point, &context), expected_point);
    assert_eq!(
        read(&device_seed, &context),
        seed.0,
        "post-fresh boundary seed"
    );
    let device_fresh_seed = read(&device_seed, &context);
    for role in 0..3 {
        let expected = if k == 0 {
            logical_claims[role].clone()
        } else {
            merge_claims(&logical_claims[role], &coordinates)
        };
        let device_claims = alloc_and_copy(&logical_claims[role], &context);
        if k == 0 {
            assert_eq!(read(&device_claims, &context), expected);
        } else {
            let mut merged = context
                .alloc::<E4>(expected.len(), AllocationPlacement::BestFit)
                .unwrap();
            launch_merge_claims_e4(
                &device_claims,
                &device_point[n..],
                k as u32,
                &mut merged,
                &context,
            )
            .unwrap();
            assert_eq!(read(&merged, &context), expected, "role={role}, k={k}");
        }
        assert_eq!(
            read(&device_claims, &context),
            logical_claims[role],
            "merge preserves original claims"
        );
    }
    if merged_mode {
        let expected = merge_claims(&logical_claims[0], &coordinates);
        let mut wrong = unmerged_claims[0].clone();
        wrong.resize(240, E4::ZERO);
        wrong.extend_from_slice(&unmerged_claims[1]);
        let wrong = merge_claims(&wrong, &coordinates);
        assert_ne!(
            expected[14], wrong[14],
            "per-side padding changes the boundary fold"
        );
        assert_eq!(expected.len(), 48);
        assert!(
            logical_claims[1].is_empty(),
            "empty Witness returns before the merge kernel launch"
        );
    }
    assert_eq!(
        read(&device_seed, &context),
        device_fresh_seed,
        "claims are not re-absorbed"
    );
    let batching_bits = if merged_mode {
        let mut real_config = packed_config(20, 4, SecurityLevel::Sec100);
        real_config.commitment_mode =
            prover::gkr::prover_config::CommitmentMode::MergedMemoryAndWitness;
        let real_geometry = BaseCommitmentGeometry::from_config(
            &real_config,
            BaseColumns {
                memory: 225,
                witness: 538,
                setup: 6,
            },
        )
        .unwrap();
        assert_eq!(real_geometry.total_physical_columns(), 49);
        real_config.base_round().batching_pow_bits::<BF, E4>(
            real_config.security_level.security_bits(),
            real_geometry.message_size_log2(),
            real_geometry.total_physical_columns(),
        )
    } else {
        8
    };
    let (expected_nonce, batching) = draw_random_field_els_with_pow::<BF, E4, Blake2sTranscript>(
        &mut seed,
        1,
        batching_bits,
        &worker,
    );
    let mut device_nonce = context
        .alloc::<u64>(1, AllocationPlacement::BestFit)
        .unwrap();
    let mut device_batching = context
        .alloc::<E4>(1, AllocationPlacement::BestFit)
        .unwrap();
    crate::pow::schedule_draw_e4_challenges_with_pow(
        &mut device_seed,
        &mut device_batching,
        batching_bits,
        &mut device_nonce[0],
        &context,
    )
    .unwrap();
    assert_eq!(read(&device_nonce, &context), [expected_nonce]);
    assert_eq!(read(&device_batching, &context), batching);
    assert_eq!(
        read(&device_seed, &context),
        seed.0,
        "post-batching boundary seed"
    );

    let mut holders = Vec::new();
    for (role_index, role) in [
        BaseOracleRole::Memory,
        BaseOracleRole::Witness,
        BaseOracleRole::Setup,
    ]
    .into_iter()
    .enumerate()
    {
        let mut holder = TraceHolder::<BF>::new_base_without_cosets(
            geometry,
            role,
            TreesCacheMode::CacheNone,
            &context,
        )
        .unwrap();
        memory_copy_async(
            holder.get_uninit_hypercube_evals_mut(),
            &raw[role_index],
            context.get_exec_stream(),
        )
        .unwrap();
        holders.push(holder);
    }
    let mut state = GpuWhirState::new_with_queries(message, 1, 2, &context).unwrap();
    schedule_initialize_batched_forms(
        &holders[0],
        &holders[1],
        &holders[2],
        widths[0].div_ceil(pack),
        widths[1].div_ceil(pack),
        widths[2].div_ceil(pack),
        &device_batching,
        true,
        &mut state,
        &context,
    )
    .unwrap();
    let mut expected_evals = vec![E4::ZERO; message];
    let mut power = E4::ONE;
    for role in 0..3 {
        for column in 0..widths[role].div_ceil(pack) {
            for row in 0..message {
                let value = raw[role]
                    .get(column * message + row)
                    .copied()
                    .unwrap_or(BF::ZERO);
                let mut term = E4::from_base(value);
                term.mul_assign(&power);
                expected_evals[row].add_assign(&term);
            }
            power.mul_assign(&batching[0]);
        }
    }
    assert_eq!(
        read(&state.sumchecked_poly_evaluation_form, &context),
        expected_evals,
        "initial WHIR polynomial"
    );
    let mut expected_monomials = expected_evals;
    parallel_multivariate_hypercube_evals_into_coeffs(
        &mut expected_monomials,
        message_log as u32,
        &worker,
    );
    assert_eq!(
        read(state.sumchecked_poly_monomial_form.slice(), &context),
        e4_coeffs_to_vectorized(&expected_monomials)
    );
    eprintln!("packed_handoff_cpu_parity k={k}: boundary seeds, point, three sets, nonce/challenge, initial polynomial and monomials checked");
}

macro_rules! cases {
    ($($name:ident: $k:expr),*) => { $(#[test] fn $name() { handoff($k); })* };
}
cases! {
    packed_handoff_cpu_parity_k0: 0,
    packed_handoff_cpu_parity_k1: 1,
    packed_handoff_cpu_parity_k2: 2,
    packed_handoff_cpu_parity_k3: 3,
    packed_handoff_cpu_parity_k4: 4
}

#[test]
fn packed_handoff_merged_blake_widths_cpu_parity() {
    handoff_for_mode(4, true);
}
