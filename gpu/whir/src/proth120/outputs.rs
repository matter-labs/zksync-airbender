use std::marker::PhantomData;
use std::sync::{Arc, Mutex};

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, HostAllocation, UnsafeAccessor};
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::PR;
use gpu_hash::keccak256::Digest;
use gpu_prover_context::ProverContext;

use super::shape::L1WhirShape;
use crate::upstream::{
    BaseFieldQuery, ExtensionFieldQuery, Keccak256MerkleTreeWithCap, MerkleTreeCapVarLength,
    WhirBaseLayerCommitmentAndQueries, WhirCommitment, WhirIntermediateCommitmentAndQueries,
    WhirPolyCommitProof, WhirSchedule,
};

pub(crate) struct BaseOpeningsDevice {
    pub(crate) leaves: DeviceAllocation<PR>,
    pub(crate) paths: DeviceAllocation<Digest>,
    pub(crate) tree_indexes: DeviceAllocation<u32>,
}

pub(crate) struct IntermediateProofDevice {
    pub(crate) cap: DeviceAllocation<Digest>,
    pub(crate) leaves: DeviceAllocation<PR>,
    pub(crate) paths: DeviceAllocation<Digest>,
    pub(crate) tree_indexes: DeviceAllocation<u32>,
}

pub(crate) struct L1WhirProofDevice {
    pub(crate) memory: BaseOpeningsDevice,
    pub(crate) setup: BaseOpeningsDevice,
    pub(crate) intermediate: Vec<IntermediateProofDevice>,
    pub(crate) ood_samples: DeviceAllocation<PR>,
    pub(crate) sumcheck_polys: DeviceAllocation<PR>,
    pub(crate) pow_nonces: DeviceAllocation<u64>,
    pub(crate) final_monomials: DeviceAllocation<PR>,
    pub(crate) batched_opening: DeviceAllocation<PR>,
}

fn product(a: usize, b: usize) -> usize {
    a.checked_mul(b)
        .expect("Proth120 WHIR: proof buffer length overflow")
}

impl BaseOpeningsDevice {
    fn new(
        queries: usize,
        values: usize,
        columns: usize,
        path_len: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        Ok(Self {
            leaves: context.alloc(
                product(product(queries, values), columns),
                AllocationPlacement::BestFit,
            )?,
            paths: context.alloc(product(queries, path_len), AllocationPlacement::BestFit)?,
            tree_indexes: context.alloc(queries, AllocationPlacement::BestFit)?,
        })
    }
}

impl L1WhirProofDevice {
    pub(crate) fn new(
        shape: &L1WhirShape,
        memory_columns: usize,
        setup_columns: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        assert!(
            memory_columns > 0 && setup_columns > 0,
            "Proth120 WHIR: packed column counts must be nonzero"
        );
        let first = shape.rounds[0];
        let base_path = (first.query_domain_log2 - shape.cap_log) as usize;
        let mut intermediate = Vec::with_capacity(shape.rounds.len() - 1);
        for (r, round) in shape.rounds.iter().enumerate().take(shape.rounds.len() - 1) {
            let oracle = round
                .oracle
                .expect("Proth120 WHIR: intermediate oracle missing");
            let q = shape.rounds[r + 1].queries;
            intermediate.push(IntermediateProofDevice {
                cap: context.alloc(1 << shape.cap_log, AllocationPlacement::BestFit)?,
                leaves: context
                    .alloc(product(q, 1 << oracle.log_v), AllocationPlacement::BestFit)?,
                paths: context.alloc(product(q, oracle.path_len), AllocationPlacement::BestFit)?,
                tree_indexes: context.alloc(q, AllocationPlacement::BestFit)?,
            });
        }
        Ok(Self {
            memory: BaseOpeningsDevice::new(
                first.queries,
                1 << first.folds,
                memory_columns,
                base_path,
                context,
            )?,
            setup: BaseOpeningsDevice::new(
                first.queries,
                1 << first.folds,
                setup_columns,
                base_path,
                context,
            )?,
            intermediate,
            ood_samples: context.alloc(shape.rounds.len() - 1, AllocationPlacement::BestFit)?,
            sumcheck_polys: context.alloc(
                product(shape.total_sumcheck_polys, 3),
                AllocationPlacement::BestFit,
            )?,
            pow_nonces: context.alloc(shape.rounds.len(), AllocationPlacement::BestFit)?,
            final_monomials: context.alloc(1 << shape.log_final, AllocationPlacement::BestFit)?,
            batched_opening: context.alloc(1, AllocationPlacement::BestFit)?,
        })
    }
}

pub(crate) struct BaseOpeningsHost {
    pub(crate) leaves: HostAllocation<[PR]>,
    pub(crate) paths: HostAllocation<[Digest]>,
    pub(crate) tree_indexes: HostAllocation<[u32]>,
}

pub(crate) struct IntermediateProofHost {
    pub(crate) cap: HostAllocation<[Digest]>,
    pub(crate) leaves: HostAllocation<[PR]>,
    pub(crate) paths: HostAllocation<[Digest]>,
    pub(crate) tree_indexes: HostAllocation<[u32]>,
}

pub(crate) struct L1WhirProofHost {
    pub(crate) memory: BaseOpeningsHost,
    pub(crate) setup: BaseOpeningsHost,
    pub(crate) intermediate: Vec<IntermediateProofHost>,
    pub(crate) memory_cap: HostAllocation<[Digest]>,
    pub(crate) setup_cap: HostAllocation<[Digest]>,
    pub(crate) claims: HostAllocation<[PR]>,
    pub(crate) original_evaluation_point: HostAllocation<[PR]>,
    pub(crate) batching_challenge: HostAllocation<[PR]>,
    pub(crate) ood_samples: HostAllocation<[PR]>,
    pub(crate) sumcheck_polys: HostAllocation<[PR]>,
    pub(crate) pow_nonces: HostAllocation<[u64]>,
    pub(crate) final_monomials: HostAllocation<[PR]>,
    pub(crate) batched_opening: HostAllocation<[PR]>,
}

impl BaseOpeningsHost {
    fn new(device: &BaseOpeningsDevice, context: &ProverContext) -> Self {
        unsafe {
            Self {
                leaves: context.alloc_host_uninit_slice(device.leaves.len()),
                paths: context.alloc_host_uninit_slice(device.paths.len()),
                tree_indexes: context.alloc_host_uninit_slice(device.tree_indexes.len()),
            }
        }
    }
}

impl L1WhirProofHost {
    pub(crate) fn new(
        shape: &L1WhirShape,
        device: &L1WhirProofDevice,
        memory_columns: usize,
        setup_columns: usize,
        context: &ProverContext,
    ) -> Self {
        unsafe {
            Self {
                memory: BaseOpeningsHost::new(&device.memory, context),
                setup: BaseOpeningsHost::new(&device.setup, context),
                intermediate: device
                    .intermediate
                    .iter()
                    .map(|d| IntermediateProofHost {
                        cap: context.alloc_host_uninit_slice(d.cap.len()),
                        leaves: context.alloc_host_uninit_slice(d.leaves.len()),
                        paths: context.alloc_host_uninit_slice(d.paths.len()),
                        tree_indexes: context.alloc_host_uninit_slice(d.tree_indexes.len()),
                    })
                    .collect(),
                memory_cap: context.alloc_host_uninit_slice(1 << shape.cap_log),
                setup_cap: context.alloc_host_uninit_slice(1 << shape.cap_log),
                claims: context.alloc_host_uninit_slice(
                    memory_columns
                        .checked_add(setup_columns)
                        .expect("Proth120 WHIR: claims length overflow"),
                ),
                original_evaluation_point: context
                    .alloc_host_uninit_slice(shape.log_message as usize),
                batching_challenge: context.alloc_host_uninit_slice(1),
                ood_samples: context.alloc_host_uninit_slice(device.ood_samples.len()),
                sumcheck_polys: context.alloc_host_uninit_slice(device.sumcheck_polys.len()),
                pow_nonces: context.alloc_host_uninit_slice(device.pow_nonces.len()),
                final_monomials: context.alloc_host_uninit_slice(device.final_monomials.len()),
                batched_opening: context.alloc_host_uninit_slice(1),
            }
        }
    }
}

pub type L1WhirProof = WhirPolyCommitProof<PR, PR, Keccak256MerkleTreeWithCap>;

pub struct L1WhirScheduled {
    _callbacks: Callbacks<'static>,
    _host: L1WhirProofHost,
    result: Arc<Mutex<Option<L1WhirProof>>>,
    tracing_ranges: Vec<(String, Range)>,
}

impl L1WhirScheduled {
    pub fn into_proof_after_completion(self) -> L1WhirProof {
        self.result
            .lock()
            .expect("Proth120 WHIR: proof result lock poisoned")
            .take()
            .expect("Proth120 WHIR: proof callback has not run")
    }

    pub fn phase_times_after_completion(&self) -> CudaResult<Vec<(String, f32)>> {
        self.tracing_ranges
            .iter()
            .map(|(name, range)| Ok((name.clone(), range.elapsed()?)))
            .collect()
    }
}

struct BaseOpeningsReadback {
    leaves: UnsafeAccessor<[PR]>,
    paths: UnsafeAccessor<[Digest]>,
    tree_indexes: UnsafeAccessor<[u32]>,
}

struct IntermediateReadback {
    cap: UnsafeAccessor<[Digest]>,
    openings: BaseOpeningsReadback,
}

struct L1WhirReadback {
    memory: BaseOpeningsReadback,
    setup: BaseOpeningsReadback,
    intermediate: Vec<IntermediateReadback>,
    memory_cap: UnsafeAccessor<[Digest]>,
    setup_cap: UnsafeAccessor<[Digest]>,
    claims: UnsafeAccessor<[PR]>,
    original_evaluation_point: UnsafeAccessor<[PR]>,
    batching_challenge: UnsafeAccessor<[PR]>,
    ood_samples: UnsafeAccessor<[PR]>,
    sumcheck_polys: UnsafeAccessor<[PR]>,
    pow_nonces: UnsafeAccessor<[u64]>,
    final_monomials: UnsafeAccessor<[PR]>,
    batched_opening: UnsafeAccessor<[PR]>,
}

impl BaseOpeningsHost {
    fn readback(&self) -> BaseOpeningsReadback {
        BaseOpeningsReadback {
            leaves: self.leaves.get_accessor(),
            paths: self.paths.get_accessor(),
            tree_indexes: self.tree_indexes.get_accessor(),
        }
    }
}

impl L1WhirProofHost {
    fn readback(&self) -> L1WhirReadback {
        L1WhirReadback {
            memory: self.memory.readback(),
            setup: self.setup.readback(),
            intermediate: self
                .intermediate
                .iter()
                .map(|host| IntermediateReadback {
                    cap: host.cap.get_accessor(),
                    openings: BaseOpeningsReadback {
                        leaves: host.leaves.get_accessor(),
                        paths: host.paths.get_accessor(),
                        tree_indexes: host.tree_indexes.get_accessor(),
                    },
                })
                .collect(),
            memory_cap: self.memory_cap.get_accessor(),
            setup_cap: self.setup_cap.get_accessor(),
            claims: self.claims.get_accessor(),
            original_evaluation_point: self.original_evaluation_point.get_accessor(),
            batching_challenge: self.batching_challenge.get_accessor(),
            ood_samples: self.ood_samples.get_accessor(),
            sumcheck_polys: self.sumcheck_polys.get_accessor(),
            pow_nonces: self.pow_nonces.get_accessor(),
            final_monomials: self.final_monomials.get_accessor(),
            batched_opening: self.batched_opening.get_accessor(),
        }
    }
}

fn copy_base_openings(
    host: &mut BaseOpeningsHost,
    device: &BaseOpeningsDevice,
    stream: &CudaStream,
) -> CudaResult<()> {
    memory_copy_async(&mut host.leaves, &device.leaves, stream)?;
    memory_copy_async(&mut host.paths, &device.paths, stream)?;
    memory_copy_async(&mut host.tree_indexes, &device.tree_indexes, stream)
}

unsafe fn assemble_base_queries(
    host: &BaseOpeningsReadback,
) -> Vec<BaseFieldQuery<PR, Keccak256MerkleTreeWithCap>> {
    let indexes = host.tree_indexes.get();
    let leaves = host.leaves.get();
    let paths = host.paths.get();
    let leaf_width = leaves.len() / indexes.len();
    let depth = paths.len() / indexes.len();
    indexes
        .iter()
        .enumerate()
        .map(|(q, &index)| BaseFieldQuery {
            index: index as usize,
            leaf_values_concatenated: leaves[q * leaf_width..(q + 1) * leaf_width].to_vec(),
            path: paths[q * depth..(q + 1) * depth].to_vec(),
            _marker: PhantomData,
        })
        .collect()
}

unsafe fn assemble_whir_proof(
    host: &L1WhirReadback,
    schedule: &WhirSchedule,
    memory_columns: usize,
    setup_columns: usize,
) -> L1WhirProof {
    let claims = host.claims.get();
    let intermediate_whir_oracles = host
        .intermediate
        .iter()
        .map(|oracle| {
            let indexes = oracle.openings.tree_indexes.get();
            let leaves = oracle.openings.leaves.get();
            let paths = oracle.openings.paths.get();
            let width = leaves.len() / indexes.len();
            let depth = paths.len() / indexes.len();
            WhirIntermediateCommitmentAndQueries {
                commitment: WhirCommitment {
                    cap: MerkleTreeCapVarLength {
                        cap: oracle.cap.get().to_vec(),
                    },
                    _marker: PhantomData,
                },
                queries: indexes
                    .iter()
                    .enumerate()
                    .map(|(q, &index)| ExtensionFieldQuery {
                        index: index as usize,
                        leaf_values_concatenated: leaves[q * width..(q + 1) * width].to_vec(),
                        path: paths[q * depth..(q + 1) * depth].to_vec(),
                        _marker: PhantomData,
                    })
                    .collect(),
            }
        })
        .collect();
    WhirPolyCommitProof {
        setup_commitment: WhirBaseLayerCommitmentAndQueries {
            commitment: WhirCommitment {
                cap: MerkleTreeCapVarLength {
                    cap: host.setup_cap.get().to_vec(),
                },
                _marker: PhantomData,
            },
            num_columns: setup_columns,
            evals: claims[memory_columns..memory_columns + setup_columns].to_vec(),
            queries: assemble_base_queries(&host.setup),
        },
        memory_commitment: WhirBaseLayerCommitmentAndQueries {
            commitment: WhirCommitment {
                cap: MerkleTreeCapVarLength {
                    cap: host.memory_cap.get().to_vec(),
                },
                _marker: PhantomData,
            },
            num_columns: memory_columns,
            evals: claims[..memory_columns].to_vec(),
            queries: assemble_base_queries(&host.memory),
        },
        witness_commitment: Default::default(),
        intermediate_whir_oracles,
        ood_samples: host.ood_samples.get().to_vec(),
        sumcheck_polys: host
            .sumcheck_polys
            .get()
            .chunks_exact(3)
            .map(|p| p.try_into().unwrap())
            .collect(),
        pow_nonces: host.pow_nonces.get().to_vec(),
        final_monomials: host.final_monomials.get().to_vec(),
        whir_schedule: schedule.clone(),
        batching_challenge: Some(host.batching_challenge.get()[0]),
        original_evaluation_point: Some(host.original_evaluation_point.get().to_vec()),
        batched_opening: Some(host.batched_opening.get()[0]),
    }
}

pub(crate) fn schedule_readback_and_assemble(
    device: L1WhirProofDevice,
    mut host: L1WhirProofHost,
    memory_cap: &DeviceSlice<Digest>,
    setup_cap: &DeviceSlice<Digest>,
    schedule: &WhirSchedule,
    memory_columns: usize,
    setup_columns: usize,
    tracing_ranges: Vec<(String, Range)>,
    context: &ProverContext,
) -> CudaResult<L1WhirScheduled> {
    let stream = context.get_exec_stream();
    copy_base_openings(&mut host.memory, &device.memory, stream)?;
    copy_base_openings(&mut host.setup, &device.setup, stream)?;
    for (host, device) in host.intermediate.iter_mut().zip(&device.intermediate) {
        memory_copy_async(&mut host.cap, &device.cap, stream)?;
        memory_copy_async(&mut host.leaves, &device.leaves, stream)?;
        memory_copy_async(&mut host.paths, &device.paths, stream)?;
        memory_copy_async(&mut host.tree_indexes, &device.tree_indexes, stream)?;
    }
    memory_copy_async(&mut host.memory_cap, memory_cap, stream)?;
    memory_copy_async(&mut host.setup_cap, setup_cap, stream)?;
    memory_copy_async(&mut host.ood_samples, &device.ood_samples, stream)?;
    memory_copy_async(&mut host.sumcheck_polys, &device.sumcheck_polys, stream)?;
    memory_copy_async(&mut host.pow_nonces, &device.pow_nonces, stream)?;
    memory_copy_async(&mut host.final_monomials, &device.final_monomials, stream)?;
    memory_copy_async(&mut host.batched_opening, &device.batched_opening, stream)?;
    let readback = host.readback();
    let result = Arc::new(Mutex::new(None));
    let destination = Arc::clone(&result);
    let schedule = schedule.clone();
    let mut callbacks = Callbacks::new();
    callbacks.schedule(
        move || {
            let proof =
                unsafe { assemble_whir_proof(&readback, &schedule, memory_columns, setup_columns) };
            *destination
                .lock()
                .expect("Proth120 WHIR: proof result lock poisoned") = Some(proof);
        },
        stream,
    )?;
    Ok(L1WhirScheduled {
        _callbacks: callbacks,
        _host: host,
        result,
        tracing_ranges,
    })
}
