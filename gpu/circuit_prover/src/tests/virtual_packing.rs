//! Zero-fold protocol components exercise the production handoff and scheduler,
//! independently of circuit-level admission. CPU references use prover::whir_fold.
use super::*;
use cs::definitions::GKRAddress;
use era_cudart::slice::DeviceSlice;
use gpu_gkr::proof_layout::{
    ProofLayout, ProofLayoutInputs, WhirBaseLayerDims, WhirBaseLayerKind, WhirDims,
    WhirIntermediateDims,
};
use gpu_trace::trace::holder::{TraceHolder, TreesCacheMode};
use prover::allocation_pool::GenericAllocationPool;
use prover::gkr::prover::backend::NaiveBackend;
use prover::gkr::prover::stages::commitment_utils::commit_trace_part_with_packing;
use prover::gkr::prover::transcript_utils::draw_random_field_els;
use prover::gkr::prover::NaiveGKRBackend;
use prover::gkr::prover::SetupCommitment;
use prover::gkr::sumcheck::access_and_fold::{BaseFieldPoly, GKRLayerSource, GKRStorage};
use prover::gkr::whir::{whir_fold, WhirIntermediateOracleMode};
use prover::transcript::{Blake2sTranscript, Seed};
use std::collections::BTreeMap;

fn config(k: usize) -> ProverConfig {
    CircuitType::Delegation(if k == 0 {
        DelegationCircuitType::BigIntWithControl
    } else {
        DelegationCircuitType::Blake2WithCompression
    })
    .prover_config(SecurityLevel::Sec100)
}

/// The certified ethproofs-soundcalc config of `config(k)`'s circuit, as
/// committed next to its layout. Its internal rounds gate the folding
/// challenges and OOD draws behind PoW.
fn ethproofs_config(k: usize) -> ProverConfig {
    let json = if k == 0 {
        include_str!(
            "../../../../circuit_defs/bigint_with_control/generated/prover_config_sec_100_ethproofs_soundcalc.json"
        )
    } else {
        include_str!(
            "../../../../circuit_defs/blake2_with_compression/generated/prover_config_sec_100_ethproofs_soundcalc.json"
        )
    };
    let ethproofs: ProverConfig = serde_json::from_str(json).unwrap();
    assert_eq!(ethproofs.trace_len_log2, config(k).trace_len_log2);
    assert!(ethproofs
        .whir_schedule
        .internal_rounds
        .iter()
        .all(|round| round.folding_pow_bits > 0));
    assert!(ethproofs.whir_schedule.internal_rounds[0].ood_pow_bits > 0);
    ethproofs
}

fn layout(config: &ProverConfig, geometry: BaseCommitmentGeometry) -> ProofLayout {
    let schedule = &config.whir_schedule;
    let fold_steps = schedule.fold_steps();
    let total_folding_steps = fold_steps.iter().sum::<usize>();
    let base = |role| {
        let columns = geometry.oracle(role).physical_columns();
        WhirBaseLayerDims {
            num_columns: columns,
            logical_num_columns: geometry.oracle(role).logical_columns(),
            cap_digest_count: if columns == 0 { 0 } else { geometry.cap_size() },
            query_count: schedule.base_round.num_queries,
            leaf_values_len: columns,
            path_len: if columns == 0 {
                0
            } else {
                geometry.message_size_log2() + geometry.lde_factor().trailing_zeros() as usize
                    - geometry.cap_size().trailing_zeros() as usize
            },
        }
    };
    let mut log_n = geometry.message_size_log2();
    let mut previous_fold = 0;
    let intermediate = schedule
        .internal_rounds
        .iter()
        .map(|round| {
            log_n -= previous_fold;
            previous_fold = round.folding_log2;
            WhirIntermediateDims {
                cap_digest_count: schedule.cap_size,
                query_count: round.num_queries,
                leaf_values_len: 1 << round.folding_log2,
                path_len: log_n + round.lde_factor_log2
                    - round.folding_log2
                    - schedule.cap_size.trailing_zeros() as usize,
            }
        })
        .collect();
    ProofLayout::new(&ProofLayoutInputs {
        output_evaluations: BTreeMap::new(),
        backward_layers: vec![],
        whir: WhirDims {
            pack_log2: geometry.pack_log2(),
            original_evaluation_point_len: geometry.message_size_log2(),
            setup: base(BaseOracleRole::Setup),
            memory: base(BaseOracleRole::Memory),
            witness: base(BaseOracleRole::Witness),
            intermediate,
            num_ood_samples: schedule
                .internal_rounds
                .iter()
                .map(|round| round.num_ood_samples)
                .sum(),
            total_sumcheck_polys: total_folding_steps,
            pow_rounds: schedule.num_rounds(),
            final_monomials_len: 1 << (geometry.message_size_log2() - total_folding_steps),
        },
    })
}

#[test]
fn cpu_virtual_slab_schema_and_claim_aliases() {
    for k in [0, 2] {
        let config = config(k);
        let geometry = BaseCommitmentGeometry::from_config(
            &config,
            BaseColumns {
                memory: 5,
                witness: 0,
                setup: 0,
            },
        )
        .unwrap();
        let layout = layout(&config, geometry);
        let mut aligned = vec![E4::ZERO; layout.total_bytes.div_ceil(std::mem::size_of::<E4>())];
        // SAFETY: initialized E4 storage provides every parser field alignment.
        let bytes = unsafe {
            std::slice::from_raw_parts(aligned.as_ptr().cast::<u8>(), layout.total_bytes)
        };
        let proof = layout.parse_whir_proof(bytes, &config.whir_schedule);
        assert!(proof.base_sumcheck_polys.is_empty());
        assert!(proof.base_folding_pow_nonces.is_empty());
        assert_eq!(proof.intermediate_whir_oracles.len(), 4);
        assert_eq!(proof.intermediate_whir_oracles[0].sumcheck_polys.len(), 6);
        assert_eq!(
            proof
                .intermediate_whir_oracles
                .iter()
                .map(|r| r.sumcheck_polys.len())
                .sum::<usize>(),
            21
        );
        assert_eq!(proof.final_monomials.len(), 2);
        assert!(proof.witness_commitment.queries.is_empty());
        assert!(proof.setup_commitment.commitment.cap.cap.is_empty());
        // No slab is dereferenced: the accessors only calculate aligned offsets.
        let ptr = aligned.as_mut_ptr().cast::<u8>();
        unsafe {
            let (point, len) = layout.whir_original_evaluation_point_device_mut(ptr);
            assert_eq!(len, 22);
            assert!(!point.is_null());
            let logical = layout.whir_base_logical_evals_device_mut(ptr, WhirBaseLayerKind::Memory);
            let physical = layout.whir_base_evals_device_mut(ptr, WhirBaseLayerKind::Memory);
            assert_eq!(logical.0 == physical.0, k == 0);
            assert_eq!(logical.1, 5);
            assert_eq!(
                physical.1,
                geometry.oracle(BaseOracleRole::Memory).physical_columns()
            );
        }
    }
}

fn standalone(k: usize, config: &ProverConfig) {
    assert_eq!(config.pack_log2(), k);
    standalone_for_config(config, 64);
}

fn standalone_for_config(config: &ProverConfig, first_leaf_values: usize) {
    let k = config.pack_log2();
    let message_log = config.whir_message_size_log2();
    let message_log_u32 = u32::try_from(message_log).unwrap();
    config.validate_for_whir_message_size(message_log);
    let context = make_test_context_with_device_allocator_block_log_size(None, 256, 20);
    let baseline = context.get_used_mem_current();
    let worker = Worker::new_with_num_threads(4);
    let pack = 1usize << k;
    let widths = if k == 0 {
        [1, 0, 0]
    } else {
        [pack + 1, 2 * pack + 1, 1]
    };
    let geometry = BaseCommitmentGeometry::from_config(
        config,
        BaseColumns {
            memory: widths[0],
            witness: widths[1],
            setup: widths[2],
        },
    )
    .unwrap();
    gpu_whir::validate_baby_bear_recursive_schedule(message_log_u32, &config.whir_schedule, 27);
    let rows = 1usize << config.trace_len_log2;
    let raw: [Vec<BF>; 3] = std::array::from_fn(|role| {
        (0..rows * widths[role])
            .map(|i| {
                BF::new(((i as u32).wrapping_mul(0x85ebca6b) ^ (role as u32 * 101 + 7)) % 100003)
            })
            .collect()
    });
    let point: Vec<E4> = (0..config.trace_len_log2)
        .map(|i| {
            E4::from_array_of_base(std::array::from_fn::<_, 4, _>(|j| {
                BF::new((19 + i * 13 + j * 7) as u32)
            }))
        })
        .collect();
    let claims: [Vec<E4>; 3] = std::array::from_fn(|role| {
        raw[role]
            .chunks_exact(rows)
            .map(|col| {
                let mut values: Vec<_> = col.iter().copied().map(E4::from_base).collect();
                for r in &point {
                    for i in 0..values.len() / 2 {
                        let mut delta = values[2 * i + 1];
                        delta.sub_assign(&values[2 * i]);
                        delta.mul_assign(r);
                        delta.add_assign(&values[2 * i]);
                        values[i] = delta;
                    }
                    values.truncate(values.len() / 2);
                }
                values[0]
            })
            .collect()
    });
    let twiddles = Twiddles::<BF, Global>::new(1 << message_log, &worker);
    let pool = GenericAllocationPool::proxy();
    let [mem, wit, setup] = std::array::from_fn(|role| {
        let cols: Vec<_> = raw[role].chunks_exact(rows).collect();
        commit_trace_part_with_packing::<BF, E4, DefaultTreeConstructor, _>(
            &NaiveBackend,
            &cols,
            &twiddles,
            config.lde_factor(),
            0,
            config.cap_size,
            config.trace_len_log2,
            k,
            &pool,
            &worker,
        )
    });
    let mut layer = GKRLayerSource::<BF, E4>::default();
    for role in 0..3 {
        for (i, col) in raw[role].chunks_exact(rows).enumerate() {
            let address = match role {
                0 => GKRAddress::BaseLayerMemory(i),
                1 => GKRAddress::BaseLayerWitness(i),
                _ => GKRAddress::Setup(i),
            };
            layer
                .base_field_inputs
                .insert(address, BaseFieldPoly::new(col.to_vec().into_boxed_slice()));
        }
    }
    let mut seed = Seed(std::array::from_fn(|i| {
        0x12345678u32.wrapping_add(i as u32 * 137)
    }));
    let _preceding = draw_random_field_els::<BF, E4, Blake2sTranscript>(&mut seed, 1);
    let cpu = whir_fold::<BF, E4, DefaultTreeConstructor, Blake2sTranscript, _, _>(
        mem,
        claims[0].clone(),
        wit,
        claims[1].clone(),
        &SetupCommitment::InMemory(setup),
        claims[2].clone(),
        GKRStorage {
            layers: vec![layer],
        },
        config,
        point.clone(),
        &twiddles,
        seed,
        &NaiveBackend,
        &NaiveGKRBackend,
        WhirIntermediateOracleMode::InMemoryContinuous,
        &pool,
        &worker,
    );
    let layout = layout(config, geometry);
    let slab = context
        .alloc::<E4>(
            layout.total_bytes.div_ceil(std::mem::size_of::<E4>()),
            AllocationPlacement::BestFit,
        )
        .unwrap();
    let mut holders: Vec<_> = [
        BaseOracleRole::Memory,
        BaseOracleRole::Witness,
        BaseOracleRole::Setup,
    ]
    .into_iter()
    .enumerate()
    .map(|(role, kind)| {
        let mut holder =
            TraceHolder::<BF>::new_base(geometry, kind, TreesCacheMode::CachePartial, &context)
                .unwrap();
        if !raw[role].is_empty() {
            memory_copy_async(
                holder.get_uninit_hypercube_evals_mut(),
                &raw[role],
                context.get_exec_stream(),
            )
            .unwrap();
        }
        holder.commit_all(&context).unwrap();
        holder
    })
    .collect();
    let ptr = slab.as_ptr() as *mut u8;
    for (role, kind) in [
        WhirBaseLayerKind::Memory,
        WhirBaseLayerKind::Witness,
        WhirBaseLayerKind::Setup,
    ]
    .into_iter()
    .enumerate()
    {
        // SAFETY: disjoint slab fields, alive through terminal readback.
        unsafe {
            let (dst, len) = layout.whir_base_logical_evals_device_mut(ptr, kind);
            if len != 0 {
                memory_copy_async(
                    DeviceSlice::from_raw_parts_mut(dst, len),
                    &claims[role],
                    context.get_exec_stream(),
                )
                .unwrap();
            }
            let (dst, len) = layout.whir_base_cap_device_mut(ptr, kind);
            if len != 0 {
                let cap = holders[role].unified_device_cap.as_ref().unwrap();
                let src = DeviceSlice::from_raw_parts(cap.as_ptr().cast::<u32>(), len);
                memory_copy_async(
                    DeviceSlice::from_raw_parts_mut(dst, len),
                    src,
                    context.get_exec_stream(),
                )
                .unwrap();
            }
        }
    }
    let device_point = upload_slice_to_device_for_test(&point, &context);
    let mut device_seed = upload_slice_to_device_for_test(&seed.0, &context);
    crate::proof::schedule_base_commitment_handoff(
        geometry,
        &device_point,
        &mut device_seed,
        &slab,
        &layout,
        config.base_round().batching_pow_bits::<BF, E4>(
            config.security_level.security_bits(),
            message_log,
            geometry.total_physical_columns(),
        ),
        &context,
    )
    .unwrap();
    let mut setup_holder = holders.pop().unwrap();
    let mut witness_holder = holders.pop().unwrap();
    let mut memory_holder = holders.pop().unwrap();
    let rounds = &config.whir_schedule.internal_rounds;
    let folding_pow_bits: Vec<u32> = rounds.iter().map(|round| round.folding_pow_bits).collect();
    let ood_pow_bits: Vec<u32> = rounds.iter().map(|round| round.ood_pow_bits).collect();
    let scheduled = unsafe {
        // The per-oracle PoW vectors follow the slab's layout: one OOD-PoW slot
        // per intermediate oracle, one folding-PoW slot per folding step.
        let (_, folding_pow_slots) = layout.whir_folding_pow_nonces_device_mut(ptr);
        let (_, ood_pow_slots) = layout.whir_ood_pow_nonces_device_mut(ptr);
        assert_eq!(ood_pow_slots, ood_pow_bits.len());
        assert_eq!(folding_pow_bits.len(), ood_pow_bits.len());
        assert_eq!(
            folding_pow_slots,
            config.whir_schedule.fold_steps().iter().sum::<usize>()
        );
        let (point, point_len) = layout.whir_original_evaluation_point_device_mut(ptr);
        let (gamma, gamma_len) = layout.whir_batching_challenge_device_mut(ptr);
        gpu_whir::fold::schedule_gpu_whir_fold_with_sources(
            &mut memory_holder,
            &mut witness_holder,
            &mut setup_holder,
            DeviceSlice::from_raw_parts(point, point_len),
            &mut device_seed,
            DeviceSlice::from_raw_parts(gamma, gamma_len),
            config.lde_factor(),
            config.whir_schedule.fold_steps(),
            config.whir_schedule.queries_per_round(),
            config.whir_schedule.intermediate_lde_factors(),
            config.whir_schedule.queries_pow_bits_per_round(),
            &folding_pow_bits,
            &ood_pow_bits,
            config.cap_size,
            message_log_u32,
            true,
            &slab,
            &layout,
            &context,
        )
        .unwrap()
    };
    let mut mirror = vec![E4::ZERO; layout.total_bytes.div_ceil(std::mem::size_of::<E4>())];
    // SAFETY: initialized and aligned ordinary-host storage lives through the terminal sync.
    let bytes = unsafe {
        std::slice::from_raw_parts_mut(mirror.as_mut_ptr().cast::<u8>(), layout.total_bytes)
    };
    // This terminal ordinary-host readback is consumed only after synchronization.
    unsafe {
        memory_copy_async(
            &mut *bytes,
            DeviceSlice::from_raw_parts(ptr, layout.total_bytes),
            context.get_exec_stream(),
        )
        .unwrap();
    }
    drop((
        scheduled,
        memory_holder,
        witness_holder,
        setup_holder,
        device_seed,
        device_point,
        slab,
    ));
    assert_eq!(context.get_used_mem_current(), baseline);
    context.get_exec_stream().synchronize().unwrap();
    let mut gpu = layout.parse_whir_proof(bytes, &config.whir_schedule);
    // Match terminal proof assembly: parse_whir_proof leaves this outer
    // handoff nonce to its caller, separate from the per-round nonce stream.
    gpu.batching_challenge_pow_nonce = layout.batched_proximity_pow_nonce_host(bytes);
    assert_whir_proof_eq_for_test(&gpu, &cpu);
    assert_eq!(
        serde_json::to_vec(&gpu).unwrap(),
        serde_json::to_vec(&cpu).unwrap()
    );
    assert!(gpu.base_sumcheck_polys.is_empty());
    assert!(gpu.base_folding_pow_nonces.is_empty());
    // The gated draws really ran: one folding nonce per step of a gated round,
    // an OOD nonce exactly for gated OOD draws.
    for (oracle, round) in gpu
        .intermediate_whir_oracles
        .iter()
        .zip(&config.whir_schedule.internal_rounds)
    {
        let gated_steps = if round.folding_pow_bits > 0 {
            round.folding_log2
        } else {
            0
        };
        assert_eq!(oracle.folding_pow_nonces.len(), gated_steps);
        assert_eq!(oracle.ood_pow_nonce.is_some(), round.ood_pow_bits > 0);
    }
    assert_eq!(
        gpu.intermediate_whir_oracles[0].queries[0]
            .leaf_values_concatenated
            .len(),
        first_leaf_values
    );
    assert_eq!(gpu.final_monomials.len(), 2);
    assert_eq!(context.get_used_mem_current(), baseline);
}

#[test]
#[ignore = "full-domain zero-fold protocol with empty roles and batching override"]
fn virtual_whir_k0_empty_roles_cpu_parity() {
    let mut config = config(0);
    config.whir_schedule.base_round.batching_pow_bits = Some(13);
    standalone(0, &config);
}

#[test]
#[ignore = "full-domain physical plus virtual zero-fold protocol"]
fn virtual_whir_k2_tail_groups_cpu_parity() {
    standalone(2, &config(2));
}

#[test]
#[ignore = "full-domain zero-fold protocol under the certified ethproofs schedule (folding and OOD PoW)"]
fn virtual_whir_k0_ethproofs_pow_cpu_parity() {
    standalone(0, &ethproofs_config(0));
}

#[test]
#[ignore = "full-domain physical plus virtual zero-fold protocol under the certified ethproofs schedule (folding and OOD PoW)"]
fn virtual_whir_k2_ethproofs_pow_cpu_parity() {
    standalone(2, &ethproofs_config(2));
}

fn bounded_virtual_config() -> ProverConfig {
    // Synthetic protocol parity only: keep the query and PoW work bounded.
    let mut config = ProverConfig::whir_only(
        12,
        prover::gkr::prover_config::WhirSchedule::from_legacy_arrays(
            4,
            32,
            1,
            &[0, 5, 4, 3],
            &[4, 4, 4, 4],
            &[4, 64, 512],
            &[0, 0, 0, 0],
        ),
        SecurityLevel::Sec100,
    );
    config.whir_schedule.base_round.batching_pow_bits = Some(4);
    config
}

#[test]
fn cpu_g4_nondefault_virtual_slab_schema() {
    let config = bounded_virtual_config();
    assert_eq!(config.whir_message_size_log2(), 13);
    config.validate_for_whir_message_size(13);
    let geometry = BaseCommitmentGeometry::from_config(
        &config,
        BaseColumns {
            memory: 3,
            witness: 5,
            setup: 1,
        },
    )
    .unwrap();
    let layout = layout(&config, geometry);
    let aligned = vec![E4::ZERO; layout.total_bytes.div_ceil(std::mem::size_of::<E4>())];
    // SAFETY: initialized E4 storage provides every parser field alignment.
    let bytes =
        unsafe { std::slice::from_raw_parts(aligned.as_ptr().cast::<u8>(), layout.total_bytes) };
    let proof = layout.parse_whir_proof(bytes, &config.whir_schedule);
    assert!(proof.base_sumcheck_polys.is_empty());
    assert!(proof.base_folding_pow_nonces.is_empty());
    assert_eq!(proof.intermediate_whir_oracles.len(), 3);
    assert_eq!(
        proof
            .intermediate_whir_oracles
            .iter()
            .map(|round| round.sumcheck_polys.len())
            .collect::<Vec<_>>(),
        [5, 4, 3]
    );
    assert_eq!(proof.final_monomials.len(), 2);
    assert_eq!(proof.memory_commitment.queries.len(), 4);
    assert_eq!(
        proof.memory_commitment.queries[0]
            .leaf_values_concatenated
            .len(),
        2
    );
}

#[test]
#[ignore = "bounded nondefault zero-fold ladder with physical packing, LDE4 and cap32"]
fn geometry_guard_g_virtual_whir_m13_nondefault_cpu_parity() {
    standalone_for_config(&bounded_virtual_config(), 32);
}
