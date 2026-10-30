// Batch-aggregation guest (BENCHMARKING DRAFT): verifies N unified-recursion proofs with
// exactly the verifier `fsv_unified_recursion_layer_sec_100` runs, requires that they all
// share one recursion chain, and folds their public outputs into a single commitment. It
// mirrors, in spirit, v2's recursion-level aggregation of batch public inputs; it is not a
// production protocol design.
//
// ND stream: `N`, then N unified-verifier streams back to back, each exactly what
// `full_statement_verifier::host_utils::build_unified_stream` produces for a
// `RecursionUnified` proof artifact (`cli aggregate-input` writes such an input).
//
// Each verification returns 16 words: [0..8] = x10..x17 of the base program, passed
// through every layer (the batch's public output), [8..16] = the recursion-chain hash
// after the verified layer. That chain hash is the only thing binding the proof to a
// program: the unified setup is read from ND, and its end params are hashed into the
// chain (`[0; 8] || base end params` -> bridge -> final verifier). So the chain part must
// match across all N proofs, and it must reach the output.
//
// Commitment, with H = blake2s as used for the recursion chain (`Blake2sBufferingTranscript`,
// `USE_REDUCED_BLAKE2_ROUNDS`, one 16-word block per step) and C = the common chain hash:
//   acc_0 = H(C || N || 0^7)
//   acc_i = H(acc_{i-1} || out_i)   for i = 1..N, out_i = the 8 public-output words of proof i
// Output: x10..x17 = acc_N, x18..x25 = 0. The upper half has to be zero because this guest
// is proven as an ordinary (base-layer) program, and the base-layer statement verifiers
// require x18..x25 == 0 (the recursion-chain start convention); C is bound through acc_0
// instead. A verifier of the aggregated proof recomputes acc_N from the trusted chain hash
// (`prover_pipeline::unified_verification_chain_hashes`) and the batches' public inputs.
//
// Build (standard machine; blake via the delegation circuit, no special opcodes):
//   cd tools/gkr_verifier && ./dump_bin.sh --blake blake2_with_compression --variant caches \
//       fsv_aggregate_unified_sec_100

use non_determinism_source::{CSRBasedSource, U32WordNonDeterminismSource};
use riscv_common::zksync_os_finish_success;
use verifier_common::errors::PanicErrorCreator;
use verifier_common::transcript::Blake2sBufferingTranscript;
use verifier_common::USE_REDUCED_BLAKE2_ROUNDS;

/// Sanity bound on proofs per run (the benchmark uses N <= 10).
const MAX_PROOFS: u32 = 1024;

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

unsafe fn workload() -> ! {
    let num_proofs = CSRBasedSource.read_word();
    assert!(num_proofs > 0 && num_proofs <= MAX_PROOFS);

    let mut hasher = Blake2sBufferingTranscript::<USE_REDUCED_BLAKE2_ROUNDS>::new();
    // [acc_{i-1} || out_i]; the first half starts as C, then holds the running accumulator.
    let mut block = [0u32; 16];
    let mut chain = [0u32; 8];

    for proof_idx in 0..num_proofs {
        let Ok(regs) = full_statement_verifier::unified_circuit_statement::verify_unified_circuit_recursion_layer_sec_100::<
            CSRBasedSource,
            PanicErrorCreator,
            USE_REDUCED_BLAKE2_ROUNDS,
        >(&mut CSRBasedSource);

        if proof_idx == 0 {
            for i in 0..8 {
                chain[i] = regs[8 + i];
                block[i] = regs[8 + i];
            }
            // acc_0 = H(C || N || 0^7)
            block[8] = num_proofs;
            hasher.absorb(&block);
            let acc = hasher.finalize_reset();
            for i in 0..8 {
                block[i] = acc.0[i];
            }
        } else {
            // same program and same recursion chain as the first proof (manually unrolled
            // comparison, as in the statement verifier, to avoid memcmp)
            let mut equal = true;
            for i in 0..8 {
                equal &= regs[8 + i] == chain[i];
            }
            assert!(equal);
        }

        // acc_i = H(acc_{i-1} || out_i)
        for i in 0..8 {
            block[8 + i] = regs[i];
        }
        hasher.absorb(&block);
        let acc = hasher.finalize_reset();
        for i in 0..8 {
            block[i] = acc.0[i];
        }
    }

    let mut output = [0u32; 8];
    for i in 0..8 {
        output[i] = block[i];
    }
    zksync_os_finish_success(&output);
}

#[inline(never)]
fn main() -> ! {
    riscv_common::boot_sequence::init();
    unsafe { workload() }
}
