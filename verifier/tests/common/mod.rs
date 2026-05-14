use prover::definitions::GKRExternalChallenges;
pub use verifier_common::test_circuits::{CircuitData, CIRCUITS};

use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use prover::gkr::prover::GKRProof;
use prover::merkle_trees::DefaultTreeConstructor;
use verifier_common::errors::{DebugErrorCreator, VerificationError};
use verifier_common::gkr::flatten::flatten_gkr_proof_for_nds;
use verifier_common::prover::nd_source_std::{set_iterator, ThreadLocalBasedSource};

pub const VERIFIER_STACK_SIZE: usize = 1 << 27;

macro_rules! define_dispatch {
    ($($name:ident; $trace_len_log_2:expr; $layout_suffix:expr),* $(,)?) => {
        macro_rules! with_circuit {
            ($circuit_name:expr, $level:expr, |$m:ident| $body:expr) => {
                match ($circuit_name, $level) {
                    $(
                        #[cfg(feature = "security_80")]
                        (stringify!($name), ::prover::definitions::SecurityLevel::Sec80) => {
                            use verifier::$name::sec_80 as $m;
                            $body
                        }
                        #[cfg(feature = "security_100")]
                        (stringify!($name), ::prover::definitions::SecurityLevel::Sec100) => {
                            use verifier::$name::sec_100 as $m;
                            $body
                        }
                    )*
                    (other, _) => panic!("unknown or disabled circuit/level: {}", other),
                }
            };
        }
    };
}
verifier_common::gkr_circuits!(define_dispatch);

pub use verifier_common::test_circuits::SecurityLevel;

pub fn load_nds(
    name: &str,
    level: SecurityLevel,
) -> (Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>) {
    circuit_by_name(name).load_nds_for(level)
}

pub fn binary_paths(name: &str, level: SecurityLevel) -> (String, String, String) {
    circuit_by_name(name).binary_paths_for(level)
}

pub fn circuit_by_name(name: &str) -> &'static CircuitData {
    CIRCUITS
        .iter()
        .find(|c| c.name == name)
        .unwrap_or_else(|| panic!("unknown circuit: {}", name))
}

#[cfg(feature = "verifier_stats")]
pub fn print_stats_log(circuit_name: &str) {
    type Counters = (
        field::stats::Stats,
        verifier_common::non_determinism_source::stats::Stats,
        common_constants::stats::Stats,
    );
    const GAS_COSTS: Counters = (
        field::stats::Stats {
            fext_adds: 8,
            fext_muls: 8,
            fbase_adds: 8,
            fbase_muls: 8,
        },
        verifier_common::non_determinism_source::stats::Stats { read_bytes: 16 },
        common_constants::stats::Stats { blake2s_hashes: 42 },
    );

    macro_rules! print_padded {
        ($($arg:expr),* $(,)?) => {
            println!(
                "{:<25} {:^6} {:^6} {:^5} {:^6} {:^7} {:^6} {:^8}",
                $($arg),*
            )
        };
    }

    fn first_two_words(label: &str) -> (&str, &str) {
        let mut words = label.split_whitespace();
        (words.next().unwrap_or(""), words.next().unwrap_or(""))
    }

    fn print_header() {
        print_padded!("", "F4+", "F4*", "F+", "F*", "bytes", "hashes", "tot.gas");
        // println!("---------------------------------------------------------------------------");
        let (gf, gn, gh) = GAS_COSTS;
        print_padded!(
            "gas/op",
            gas(gf.fext_adds),
            gas(gf.fext_muls),
            gas(gf.fbase_adds),
            gas(gf.fbase_muls),
            gas(gn.read_bytes),
            gas(gh.blake2s_hashes),
            "",
        );
        println!("---------------------------------------------------------------------------");
    }

    fn print_row(label: &str, cur: Counters, prev: Counters) {
        let (f, n, h) = cur;
        let (pf, pn, ph) = prev;
        print_padded!(
            label,
            f.fext_adds - pf.fext_adds,
            f.fext_muls - pf.fext_muls,
            f.fbase_adds - pf.fbase_adds,
            f.fbase_muls - pf.fbase_muls,
            n.read_bytes - pn.read_bytes,
            h.blake2s_hashes - ph.blake2s_hashes,
            "",
        );
    }

    fn gas(gas: usize) -> String {
        format!("({})", gas)
    }
    fn gas_k(gas: usize) -> String {
        format!("({}k)", gas.div_ceil(1000))
    }
    fn gas_totk(gas: usize) -> String {
        format!("{}k", gas.div_ceil(1000))
    }

    fn print_gas_row(cur: Counters, prev: Counters) {
        let (f, n, h) = cur;
        let (pf, pn, ph) = prev;
        let (gf, gn, gh) = GAS_COSTS;
        let fext_adds_gas = (f.fext_adds - pf.fext_adds) * gf.fext_adds;
        let fext_muls_gas = (f.fext_muls - pf.fext_muls) * gf.fext_muls;
        let fbase_adds_gas = (f.fbase_adds - pf.fbase_adds) * gf.fbase_adds;
        let fbase_muls_gas = (f.fbase_muls - pf.fbase_muls) * gf.fbase_muls;
        let read_bytes_gas = (n.read_bytes - pn.read_bytes) * gn.read_bytes;
        let hashes_gas = (h.blake2s_hashes - ph.blake2s_hashes) * gh.blake2s_hashes;
        let total_gas = fext_adds_gas
            + fext_muls_gas
            + fbase_adds_gas
            + fbase_muls_gas
            + read_bytes_gas
            + hashes_gas;

        print_padded!(
            "",
            gas_k(fext_adds_gas),
            gas_k(fext_muls_gas),
            gas_k(fbase_adds_gas),
            gas_k(fbase_muls_gas),
            gas_k(read_bytes_gas),
            gas_k(hashes_gas),
            gas_totk(total_gas),
        );
    }

    fn print_totals(
        first: &str,
        two_word_totals: &[(&str, &str, Counters, Counters)],
        cur: Counters,
        prev: Counters,
    ) {
        println!();
        print_header();
        for (first, second, cur, prev) in two_word_totals {
            print_row(&format!("TOTAL {} {}", first, second), *cur, *prev);
            print_gas_row(*cur, *prev);
        }
        print_row(&format!("TOTAL {}", first), cur, prev);
        print_gas_row(cur, prev);
        println!();
        println!();
        print_header();
    }

    let log = verifier_common::stats::STATS_LOG.with_borrow(|log| log.clone());
    println!(
        "\n=== {} stats log ({} entries) ===",
        circuit_name,
        log.len()
    );
    println!();
    print_header();

    let zero = (
        field::stats::Stats::default(),
        verifier_common::non_determinism_source::stats::Stats::default(),
        common_constants::stats::Stats::default(),
    );
    let (first_label, _, _, _) = *log.get(0);
    let (mut current_first, mut current_second) = first_two_words(first_label);
    let mut prev = zero;
    let mut prev_two_word_total = zero;
    let mut prev_one_word_total = zero;
    let mut two_word_totals = Vec::new();

    for i in 0..log.len() {
        let (label, f, n, h) = *log.get(i);
        let cur = (f, n, h);
        let (first, second) = first_two_words(label);

        if first != current_first {
            two_word_totals.push((current_first, current_second, prev, prev_two_word_total));
            print_totals(current_first, &two_word_totals, prev, prev_one_word_total);
            two_word_totals.clear();
            prev_one_word_total = prev;
            prev_two_word_total = prev;
            current_first = first;
            current_second = second;
        } else if second != current_second {
            two_word_totals.push((current_first, current_second, prev, prev_two_word_total));
            prev_two_word_total = prev;
            current_second = second;
        }

        print_row(label, cur, prev);
        prev = cur;
    }

    two_word_totals.push((current_first, current_second, prev, prev_two_word_total));
    print_totals(current_first, &two_word_totals, prev, prev_one_word_total);

    let (_label, f, n, h) = *log.get(log.len() - 1);
    print_row("TOTAL ALL", (f, n, h), zero);
    print_gas_row((f, n, h), zero);
    println!();
}

#[derive(Debug)]
pub enum VerifyRejection {
    Error(VerificationError),
    Panic(String),
}

pub fn verify_nds(
    name: &str,
    level: SecurityLevel,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    nds: Vec<u32>,
) -> Result<(), VerifyRejection> {
    let prev_hook = std::panic::take_hook();
    let panic_msg = std::sync::Arc::new(std::sync::Mutex::new(None::<String>));
    let panic_msg_clone = panic_msg.clone();
    std::panic::set_hook(Box::new(move |info| {
        *panic_msg_clone.lock().unwrap() = Some(format!("{}", info));
    }));

    let outcome: Result<Result<(), VerificationError>, ()> = std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name(format!("verify_{}_{:?}", name, level))
            .stack_size(VERIFIER_STACK_SIZE)
            .spawn_scoped(s, move || {
                set_iterator(nds.into_iter());
                with_circuit!(name, level, |m| {
                    m::verify::<ThreadLocalBasedSource, DebugErrorCreator>(external_challenges)
                        .map(|_| ())
                })
            })
            .expect("failed to spawn thread");

        handle.join().map_err(|_| ())
    });

    std::panic::set_hook(prev_hook);

    match outcome {
        Ok(Ok(())) => Ok(()),
        Ok(Err(e)) => Err(VerifyRejection::Error(e)),
        Err(()) => {
            let msg = panic_msg
                .lock()
                .unwrap()
                .take()
                .unwrap_or_else(|| "(no panic message captured)".to_string());
            Err(VerifyRejection::Panic(msg))
        }
    }
}

pub fn assert_rejects_corrupted_nds(
    name: &str,
    level: SecurityLevel,
    label: &str,
    corrupt: impl FnOnce(&mut Vec<u32>),
    expected: impl FnOnce(&VerifyRejection) -> bool,
) {
    let (mut nds, external_challenges) = load_nds(name, level);
    corrupt(&mut nds);
    match verify_nds(name, level, &external_challenges, nds) {
        Ok(()) => panic!("{}: should reject {}", name, label),
        Err(r) => assert!(
            expected(&r),
            "{}: {} rejected with unexpected rejection: {:?}",
            name,
            label,
            r
        ),
    }
}

pub fn proof_to_nds(
    name: &str,
    level: SecurityLevel,
    proof: &GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>,
) -> (Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>) {
    let circuit_data = circuit_by_name(name);
    let compiled = circuit_data.compiled_circuit();
    let inits_and_teardowns_top_bits: Vec<u32> = (0..compiled.memory_layout.teardown_sets.len())
        .map(|i| i as u32)
        .collect();
    let nds = flatten_gkr_proof_for_nds::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
        proof, &compiled,
    );
    let external_challenges = proof.external_challenges;

    (nds, external_challenges)
}

pub fn assert_rejects_with_variant(
    name: &str,
    level: SecurityLevel,
    label: &str,
    proof: &GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>,
    expected: impl FnOnce(&VerificationError) -> bool,
) {
    let (nds, external_challenges) = proof_to_nds(name, level, proof);
    match verify_nds(name, level, &external_challenges, nds) {
        Ok(()) => panic!("{}: should reject {}", name, label),
        Err(VerifyRejection::Error(e)) => {
            assert!(
                expected(&e),
                "{}: {} rejected with unexpected variant {:?}",
                name,
                label,
                e
            );
        }
        Err(VerifyRejection::Panic(msg)) => {
            panic!(
                "{}: {} rejected via panic (expected specific error variant): {}",
                name, label, msg
            );
        }
    }
}

pub fn assert_rejects_via_panic(
    name: &str,
    level: SecurityLevel,
    label: &str,
    proof: &GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>,
) {
    let (nds, external_challenges) = proof_to_nds(name, level, proof);
    match verify_nds(name, level, &external_challenges, nds) {
        Ok(()) => panic!("{}: should reject {}", name, label),
        Err(VerifyRejection::Panic(_)) => {}
        Err(VerifyRejection::Error(e)) => {
            panic!(
                "{}: {} rejected via error {:?} (expected panic)",
                name, label, e
            );
        }
    }
}

pub fn load_binary_section(path: &str) -> Vec<u32> {
    let bytes = std::fs::read(path).unwrap_or_else(|_| {
        panic!(
            "Missing {} — run `cd tools/gkr_verifier && ./dump_bin.sh` first",
            path
        )
    });
    assert!(bytes.len() % 4 == 0);
    bytes
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect()
}
