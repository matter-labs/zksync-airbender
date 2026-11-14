//! Replace inner proof streams with natively verified challenges and outputs.
use super::{Chain, Selection};
use full_statement_verifier::{
    delegation_params::NUM_DELEGATION_CIRCUIT_TYPES,
    imports::{
        DelegationCircuitOutput, InitsAndTeardownsCircuitOutput, UnifiedCircuitOutput,
        UnifiedCircuitOutputWithCap, UnrolledCircuitOutput,
    },
    statement_common::read_setup_cap,
    unified_circuit_statement::{
        address_high_bits_shift, verify_full_statement_for_unified_circuit,
        verify_full_statement_for_unified_circuit_without_delegations,
    },
    unrolled_circuit_params,
    unrolled_proof_statement::verify_full_statement_for_unrolled_circuits,
    verifier_common::{
        errors::{DebugErrorCreator, VerificationError},
        field::{baby_bear::base::BabyBearField, baby_bear::ext4::BabyBearExt4},
        prover::definitions::{
            GKRExternalChallenges, MerkleTreeCap, SoundnessMode, DEFAULT_CAP_SIZE,
        },
        InitsAndTeardownsProduct, VerifierOutput, USE_REDUCED_BLAKE2_ROUNDS,
    },
};

type Challenges = GKRExternalChallenges<BabyBearField, BabyBearExt4>;
type CircuitFn<I, O> = fn(&Challenges, &mut I) -> Result<O, VerificationError>;

// Explicit words avoid serializing Rust layout, padding, or uninitialized bytes.
trait Words: Sized {
    fn write(&self, dst: &mut Vec<u32>);
    fn read(src: &mut impl Iterator<Item = u32>) -> Self;
}

impl Words for u32 {
    fn write(&self, dst: &mut Vec<u32>) {
        dst.push(*self);
    }
    fn read(src: &mut impl Iterator<Item = u32>) -> Self {
        src.next().expect("missing mock word")
    }
}

impl<T: Words, const N: usize> Words for [T; N] {
    fn write(&self, dst: &mut Vec<u32>) {
        for value in self {
            value.write(dst);
        }
    }
    fn read(src: &mut impl Iterator<Item = u32>) -> Self {
        core::array::from_fn(|_| T::read(src))
    }
}

impl Words for BabyBearExt4 {
    fn write(&self, dst: &mut Vec<u32>) {
        [self.c0.c0, self.c0.c1, self.c1.c0, self.c1.c1]
            .map(|v| v.to_u32())
            .write(dst);
    }
    fn read(src: &mut impl Iterator<Item = u32>) -> Self {
        Self::from_array_of_base(core::array::from_fn(|_| {
            let word = u32::read(src);
            assert!(
                word < BabyBearField::ORDER,
                "noncanonical mock field element"
            );
            BabyBearField::new(word)
        }))
    }
}

impl Words for Challenges {
    fn write(&self, dst: &mut Vec<u32>) {
        self.permutation_argument_linearization_challenges
            .write(dst);
        self.permutation_argument_additive_part.write(dst);
    }
    fn read(src: &mut impl Iterator<Item = u32>) -> Self {
        Self {
            permutation_argument_linearization_challenges: Words::read(src),
            permutation_argument_additive_part: Words::read(src),
            _marker: core::marker::PhantomData,
        }
    }
}

impl<const IT: usize, const CAP: usize, const MEM: usize, const SETUP: usize> Words
    for VerifierOutput<BabyBearExt4, IT, CAP, MEM, SETUP>
{
    fn write(&self, dst: &mut Vec<u32>) {
        self.inits_and_teardowns_top_bits.write(dst);
        self.memory_caps.write(dst);
        self.setup_caps.write(dst);
        self.grand_product_read_set_accumulator.write(dst);
        self.grand_product_write_set_accumulator.write(dst);
        match self.inits_and_teardowns {
            None => 0u32.write(dst),
            Some(product) => {
                1u32.write(dst);
                product.read_product.write(dst);
                product.write_product.write(dst);
            }
        }
    }
    fn read(src: &mut impl Iterator<Item = u32>) -> Self {
        Self {
            inits_and_teardowns_top_bits: Words::read(src),
            memory_caps: Words::read(src),
            setup_caps: Words::read(src),
            grand_product_read_set_accumulator: Words::read(src),
            grand_product_write_set_accumulator: Words::read(src),
            inits_and_teardowns: match u32::read(src) {
                0 => None,
                1 => Some(InitsAndTeardownsProduct {
                    read_product: Words::read(src),
                    write_product: Words::read(src),
                }),
                _ => panic!("invalid mock i/t product tag"),
            },
        }
    }
}

struct Stream<I, const RECORD: bool> {
    source: I,
    statement: Vec<u32>,
    inside_verifier: bool,
}

impl<I: Iterator<Item = u32>, const RECORD: bool> Iterator for Stream<I, RECORD> {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        let word = self.source.next()?;
        if RECORD && !self.inside_verifier {
            self.statement.push(word);
        }
        Some(word)
    }
}

fn inner<I: Iterator<Item = u32> + Send + Sync, O: Words, const RECORD: bool>(
    challenges: &Challenges,
    nds: &mut Stream<I, RECORD>,
    real: CircuitFn<Stream<I, RECORD>, O>,
) -> Result<O, VerificationError> {
    if RECORD {
        assert!(!nds.inside_verifier);
        nds.inside_verifier = true;
        let output = real(challenges, nds)?;
        nds.inside_verifier = false;
        challenges.write(&mut nds.statement);
        output.write(&mut nds.statement);
        Ok(output)
    } else {
        assert_eq!(
            Challenges::read(nds),
            *challenges,
            "mock challenge mismatch"
        );
        Ok(O::read(nds))
    }
}

macro_rules! inner_verifier {
    ($name:ident, $output:ty) => {
        fn $name<I: Iterator<Item = u32> + Send + Sync, const RECORD: bool>(
            challenges: &Challenges,
            nds: &mut Stream<I, RECORD>,
        ) -> Result<$output, VerificationError> {
            inner(
                challenges,
                nds,
                circuits::$name::verify::<_, DebugErrorCreator>,
            )
        }
    };
}

macro_rules! mode_statements {
    ($mode:ident) => {
        mod $mode {
            use super::*;
            use full_statement_verifier::{
                delegation_circuits_setups::$mode::DELEGATION_CIRCUITS_SETUP_PARAMS,
                delegation_params::$mode as delegations,
                imports::$mode as circuits,
                unrolled_circuit_params::$mode as unrolled,
            };
            inner_verifier!(add_sub_lui_auipc_mop, UnrolledCircuitOutput);
            inner_verifier!(jump_branch_slt, UnrolledCircuitOutput);
            inner_verifier!(shift_binop, UnrolledCircuitOutput);
            inner_verifier!(unsigned_mul_div, UnrolledCircuitOutput);
            inner_verifier!(mem_word_only, UnrolledCircuitOutput);
            inner_verifier!(mem_subword_only, UnrolledCircuitOutput);
            inner_verifier!(inits_and_teardowns, InitsAndTeardownsCircuitOutput);
            inner_verifier!(unified_reduced_machine, UnifiedCircuitOutput);
            inner_verifier!(blake2_with_extended_control, DelegationCircuitOutput);
            inner_verifier!(bigint_with_extended_control, DelegationCircuitOutput);
            inner_verifier!(keccak_special5, DelegationCircuitOutput);
            inner_verifier!(keccak_theta_rho, DelegationCircuitOutput);
            inner_verifier!(keccak_column_parity, DelegationCircuitOutput);
            inner_verifier!(keccak_chi5, DelegationCircuitOutput);

            fn delegation_verifiers<
                I: Iterator<Item = u32> + Send + Sync,
                const RECORD: bool,
                const BASE: bool,
            >() -> [CircuitFn<Stream<I, RECORD>, DelegationCircuitOutput>; NUM_DELEGATION_CIRCUIT_TYPES] {
                if BASE {
                    [
                        blake2_with_extended_control::<I, RECORD>,
                        bigint_with_extended_control::<I, RECORD>,
                        keccak_special5::<I, RECORD>,
                        keccak_theta_rho::<I, RECORD>,
                        keccak_column_parity::<I, RECORD>,
                        keccak_chi5::<I, RECORD>,
                    ]
                } else {
                    let mut table =
                        delegations::reduced_machine_delegation_circuit_verifiers::<_, DebugErrorCreator>();
                    for (csr, verifier) in full_statement_verifier::definitions::DELEGATION_TYPES
                        .iter()
                        .zip(&mut table)
                    {
                        if *csr == common_constants::BLAKE2S_DELEGATION_CSR_REGISTER {
                            *verifier = blake2_with_extended_control::<I, RECORD>;
                        }
                    }
                    table
                }
            }

            fn unrolled_statement<
                I: Iterator<Item = u32> + Send + Sync,
                const RECORD: bool,
                const BASE: bool,
            >(
                nds: &mut Stream<I, RECORD>,
            ) -> Result<[u32; 16], VerificationError> {
                let (mut table, wrappers) = if BASE {
                    let wrappers: [CircuitFn<_, UnrolledCircuitOutput>; 6] = [
                        add_sub_lui_auipc_mop::<I, RECORD>,
                        jump_branch_slt::<I, RECORD>,
                        shift_binop::<I, RECORD>,
                        unsigned_mul_div::<I, RECORD>,
                        mem_word_only::<I, RECORD>,
                        mem_subword_only::<I, RECORD>,
                    ];
                    (
                        unrolled::unrolled_circuit_verifiers_for_base_layer::<_, DebugErrorCreator>().to_vec(),
                        wrappers.to_vec(),
                    )
                } else {
                    let wrappers: [CircuitFn<_, UnrolledCircuitOutput>; 4] = [
                        add_sub_lui_auipc_mop::<I, RECORD>,
                        jump_branch_slt::<I, RECORD>,
                        shift_binop::<I, RECORD>,
                        mem_word_only::<I, RECORD>,
                    ];
                    (
                        unrolled::unrolled_circuit_verifiers_for_recursion_layer::<_, DebugErrorCreator>()
                            .to_vec(),
                        wrappers.to_vec(),
                    )
                };
                assert_eq!(table.len(), wrappers.len());
                for (entry, wrapper) in table.iter_mut().zip(wrappers) {
                    entry.2 = wrapper;
                }
                let num_setups = if BASE {
                    unrolled_circuit_params::NUM_BASE_LAYER_CIRCUITS
                } else {
                    unrolled_circuit_params::NUM_RECURSION_LAYER_CIRCUITS
                };
                // SAFETY: the production reader initializes the whole cap; no extra caller obligations.
                let setups: Vec<MerkleTreeCap<DEFAULT_CAP_SIZE>> = (0..num_setups)
                    .map(|_| unsafe { read_setup_cap(nds) })
                    .collect();
                let setup_refs: Vec<_> = setups.iter().collect();
                // SAFETY: the statement function has no extra caller obligations.
                unsafe {
                    verify_full_statement_for_unrolled_circuits::<
                        _,
                        DebugErrorCreator,
                        BASE,
                        USE_REDUCED_BLAKE2_ROUNDS,
                    >(
                        &setup_refs,
                        &table,
                        inits_and_teardowns::<I, RECORD>,
                        &DELEGATION_CIRCUITS_SETUP_PARAMS,
                        &delegation_verifiers::<I, RECORD, BASE>(),
                        nds,
                    )
                }
            }

            pub(super) fn statement<I: Iterator<Item = u32> + Send + Sync, const RECORD: bool>(
                chain: Chain,
                nds: &mut Stream<I, RECORD>,
            ) -> Result<[u32; 16], VerificationError> {
                match chain {
                    Chain::Base => unrolled_statement::<I, RECORD, true>(nds),
                    Chain::Unrolled => unrolled_statement::<I, RECORD, false>(nds),
                    Chain::Unified | Chain::UnrolledUnified => {
                        // SAFETY: these production functions have no extra caller obligations.
                        unsafe {
                            let setup = read_setup_cap::<_, DEFAULT_CAP_SIZE>(nds);
                            verify_full_statement_for_unified_circuit::<_, DebugErrorCreator, false, USE_REDUCED_BLAKE2_ROUNDS, _, _>(
                                &setup, unified_reduced_machine::<I, RECORD>,
                                &DELEGATION_CIRCUITS_SETUP_PARAMS, &delegation_verifiers::<I, RECORD, false>(), nds,
                            )
                        }
                    }
                    Chain::Compression => unreachable!("compression statements use their mode-specific mock"),
                }
            }
        }
    };
}

mode_statements!(pessimistic_conjecture);
mode_statements!(ethproofs_soundcalc);

macro_rules! compression_statement {
    ($mode:ident, $module:ident) => {
        mod $mode {
            use super::*;
            use full_statement_verifier::imports::$module as m;

            fn verify<I: Iterator<Item = u32> + Send + Sync, const RECORD: bool>(
                challenges: &Challenges,
                nds: &mut Stream<I, RECORD>,
            ) -> Result<UnifiedCircuitOutputWithCap<{ m::CAP_SIZE }>, VerificationError> {
                inner(challenges, nds, m::verify::<_, DebugErrorCreator>)
            }

            pub(super) fn statement<I: Iterator<Item = u32> + Send + Sync, const RECORD: bool>(
                nds: &mut Stream<I, RECORD>,
            ) -> Result<[u32; 16], VerificationError> {
                // SAFETY: the production reader and statement have no extra caller obligations.
                unsafe {
                    let setup = read_setup_cap::<_, { m::CAP_SIZE }>(nds);
                    verify_full_statement_for_unified_circuit_without_delegations::<
                        _,
                        DebugErrorCreator,
                        USE_REDUCED_BLAKE2_ROUNDS,
                        { m::CAP_SIZE },
                        { address_high_bits_shift(m::TRACE_LEN_LOG2) },
                        { 1u64 << m::TRACE_LEN_LOG2 },
                        _,
                    >(&setup, verify::<I, RECORD>, nds)
                }
            }
        }
    };
}

compression_statement!(
    pessimistic_conjecture_compression,
    unified_reduced_machine_sec_100_compression_final
);

impl Selection {
    fn statement<I: Iterator<Item = u32> + Send + Sync, const RECORD: bool>(
        self,
        nds: &mut Stream<I, RECORD>,
    ) -> [u32; 16] {
        let output = match (self.mode, self.chain) {
            (SoundnessMode::PessimisticConjecture, Chain::Compression) => {
                pessimistic_conjecture_compression::statement(nds)
            }
            (SoundnessMode::EthproofsSoundnessCalc, Chain::Compression) => {
                panic!("Ethproofs compression statement is unavailable")
            }
            (SoundnessMode::PessimisticConjecture, _) => {
                pessimistic_conjecture::statement(self.chain, nds)
            }
            (SoundnessMode::EthproofsSoundnessCalc, _) => {
                ethproofs_soundcalc::statement(self.chain, nds)
            }
        }
        .expect("statement verifier rejected input");
        assert!(nds.next().is_none(), "statement verifier left NDS words");
        output
    }

    pub fn record(self, source: impl Iterator<Item = u32> + Send + Sync) -> ([u32; 16], Vec<u32>) {
        let mut nds = Stream::<_, true> {
            source,
            statement: Vec::new(),
            inside_verifier: false,
        };
        let output = self.statement(&mut nds);
        (output, nds.statement)
    }

    pub fn verify_mocked(self, source: impl Iterator<Item = u32> + Send + Sync) -> [u32; 16] {
        self.statement(&mut Stream::<_, false> {
            source,
            statement: Vec::new(),
            inside_verifier: false,
        })
    }
}
