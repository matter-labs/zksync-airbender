use full_statement_verifier::cost_model::{riscv_order, CircuitId, DELEGATION_TYPES};
use full_statement_verifier::program_proof::ProgramProof;
use setups::Setups;
use verifier_common::fsv_binaries::FsvProgram;
use verifier_common::gkr::flatten::flatten_gkr_proof_for_nds;
use verifier_common::prover::definitions::MerkleTreeCap;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Section {
    Riscv,
    Delegation,
}

pub struct RegionPlan {
    pub circuit: CircuitId,
    pub section: Section,
    pub count_word: usize,
    pub end_word: usize,
    pub proof_first_words: Vec<usize>,
    pub closes_at_epilogue: bool,
}

pub struct StreamPlan {
    pub prefix_words: usize,
    pub regions: Vec<RegionPlan>,
    pub inits_count_word: usize,
    pub inits_first_word: usize,
    pub pow_word: usize,
    pub total_words: usize,
}

pub fn plan_unrolled_stream(
    setups: &Setups,
    proof: &ProgramProof,
    program: FsvProgram,
) -> StreamPlan {
    let mut w = 0usize;

    for params in setups.values() {
        w += MerkleTreeCap::flatten_single(&params.setup_caps).len();
    }
    w += 32 * 3;
    w += 3;
    w += external_challenge_words(proof);
    let prefix_words = w;

    let mut regions = Vec::new();
    for k in riscv_order(program) {
        let count_word = w;
        w += 1;
        let mut proof_first_words = Vec::new();
        if let Some(proofs) = proof.riscv_proofs.get(k) {
            let compiled = &proof.compiled_riscv_circuits[k];
            for p in proofs {
                proof_first_words.push(w);
                w += flatten_gkr_proof_for_nds(p, compiled).len();
            }
        }
        regions.push(RegionPlan {
            circuit: CircuitId::Riscv(*k),
            section: Section::Riscv,
            count_word,
            end_word: 0,
            proof_first_words,
            closes_at_epilogue: false,
        });
    }

    let inits_count_word = w;
    w += 1;
    let inits_first_word = w;
    {
        let compiled = proof
            .inits_and_teardowns_circuit
            .as_ref()
            .expect("compiled inits and teardowns");
        for p in &proof.inits_and_teardown_proofs {
            w += flatten_gkr_proof_for_nds(p, compiled).len();
        }
    }

    for k in DELEGATION_TYPES {
        let count_word = w;
        w += 1;
        let mut proof_first_words = Vec::new();
        if let Some(proofs) = proof.delegation_proofs.get(k) {
            let compiled = &proof.compiled_delegation_circuits[k];
            for p in proofs {
                proof_first_words.push(w);
                w += flatten_gkr_proof_for_nds(p, compiled).len();
            }
        }
        regions.push(RegionPlan {
            circuit: CircuitId::Delegation(*k),
            section: Section::Delegation,
            count_word,
            end_word: 0,
            proof_first_words,
            closes_at_epilogue: false,
        });
    }

    let pow_word = w;
    w += 2;
    if proof.recursion_chain_preimage.is_some() {
        w += 16;
    }

    for i in 0..regions.len() {
        let same_section_next = regions
            .get(i + 1)
            .filter(|next| next.section == regions[i].section)
            .map(|next| next.count_word);
        regions[i].end_word = match (same_section_next, regions[i].section) {
            (Some(next), _) => next,
            (None, Section::Riscv) => inits_count_word,
            (None, Section::Delegation) => pow_word,
        };
        regions[i].closes_at_epilogue =
            same_section_next.is_none() && regions[i].section == Section::Delegation;
    }

    StreamPlan {
        prefix_words,
        regions,
        inits_count_word,
        inits_first_word,
        pow_word,
        total_words: w,
    }
}

fn external_challenge_words(proof: &ProgramProof) -> usize {
    let mut buf = Vec::new();
    let challenges = proof
        .riscv_proofs
        .values()
        .flatten()
        .next()
        .expect("at least one riscv proof")
        .external_challenges;
    challenges.flatten_into_buffer(&mut buf);
    buf.len()
}
