use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::{DeviceAllocation, HostAllocation};
use gpu_core::primitives::field::PR;
use gpu_hash::keccak256::Digest;
use gpu_prover_context::ProverContext;

use super::shape::L1WhirShape;

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
