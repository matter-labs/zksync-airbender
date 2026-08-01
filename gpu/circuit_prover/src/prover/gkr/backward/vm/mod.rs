//! Backward coefficient-term ISA: the SEGMENTED lean VM's descriptor ABI,
//! lowering and launch.
//!
//! The launch geometry is the segmented-lean-VM design's: one warp per term
//! list, `blockDim == 32 * K`, one 32-row tile per block, and a JAOT fold
//! prologue that materializes every source a round needs before the eval loop
//! walks the lean wire. There is no cell file, no residency and no paging: the
//! Plan-6 cell executor — its pager, placement, u16 cell codec, by-value cell
//! descriptor, budget artifacts and CUDA kernels — was RETIRED wholesale, not
//! disabled. Nothing here has an ABI or runtime switch back to it.
//!
//! The kernel is specialized by `(Regime, FoldDepth, Epilogue, CoeffMode,
//! ProgramMode)`; `K` is runtime launch metadata, so one instantiation covers
//! every split width.
//!
//! # Running the tests — `--features bench` is REQUIRED
//!
//! Everything below that carries the correctness story is
//! `#[cfg(all(test, feature = "bench"))]`: [`seg_gpu_tests`] (the three-oracle
//! parity ladder), [`seg_report`] (the spike harness, the A/B matrix and the
//! corpus sweep), and [`seg_compile`]'s fixture bridge. A plain
//! `cargo test -p gpu_circuit_prover` compiles NONE of them and exits 0 having run
//! none of the GPU gates. Only [`seg_abi_tests`] — the Rust↔CUDA ABI gate — and
//! [`seg_lower_tests`] are always compiled.
//!
//! Build unlocked, then run under the GPU lock:
//!
//! ```text
//! cargo test -p gpu_circuit_prover --release --features bench --no-run
//! .agents/bin/with_gpu_lock.sh <binary> --exact <test> --ignored --nocapture
//! ```
//!
//! `bwd_coeff_gating_notice` below states this in the default run's own output, and
//! `AB_REQUIRE_BENCH_GATES=1` turns a `bench`-less run into a failure for callers
//! that need non-vacuity proved rather than assumed.

/// Launchers for the segmented lean VM: its own `__constant__` coefficient bank,
/// the `32 * k`-thread tile geometry, and the three epilogue specializations.
pub(crate) mod seg;
/// Cutover blocker 4: the lean coefficient bank evaluated ON DEVICE, by
/// translating each `NormalizedCoefficientRecipe` into the immediate-factor recipe
/// format the production `eval_recipes` kernel already evaluates. Production
/// challenges are GPU-derived, so the host cannot pre-evaluate the bank the way the
/// harness does.
pub(crate) mod seg_coeff_eval;
/// The corpus coverage proof for [`seg_coeff_eval`] — no recipe needs more than the
/// device monomial's two challenge factors — and the device-vs-CPU-oracle gate on
/// the fill. `bench`-gated because the corpus lowering lives in [`seg_compile`].
#[cfg(all(test, feature = "bench"))]
mod seg_coeff_eval_tests;
/// The segmented lean VM's fixture bridge: lean artifact plus round binding to
/// [`seg_lower::BwdSegSetup`], and the host storage model its CPU oracles resolve
/// through. `bench`-gated, like [`seg_gpu_tests`].
#[cfg(all(test, feature = "bench"))]
mod seg_compile;
/// The segmented lean VM's launch descriptors, and the source-window struct plus
/// origin / procedural-kind / publication constants rehomed here when the
/// cell-era descriptor was deleted.
pub(crate) mod seg_desc;
/// The segmented lean VM's GPU parity ladder: `K`, rounds, epilogues, D2 policies,
/// a nonzero `c_init` and the d3→d4 chain, each against BOTH CPU oracles and the
/// incumbent round update. `bench`-gated and `#[ignore]`d.
#[cfg(all(test, feature = "bench"))]
mod seg_gpu_tests;
/// Host lowering for the segmented lean VM: per-round source classes, the
/// publish-scratch plan, and the validated by-value descriptor.
pub(crate) mod seg_lower;
/// The segmented lean VM's spike harness: interleaved paired timing against the
/// incumbent compact evaluator, the Stage-A `(epilogue, K)` matrix, the corpus
/// sweep and the launch-attribute probe. `bench`-gated and `#[ignore]`d.
#[cfg(all(test, feature = "bench"))]
mod seg_report;

#[cfg(test)]
mod seg_abi_tests;
#[cfg(test)]
mod seg_lower_tests;

/// Makes the `bench`-feature gating above visible from a DEFAULT test run.
///
/// This plan has produced six vacuous-verification incidents, several of them the
/// same shape: a runner that matched nothing, exited 0, and read as a pass. The
/// whole coefficient-ISA GPU suite being feature-gated is a standing instance of
/// that shape — `cargo test -p gpu_circuit_prover` is green whether or not a single
/// gate ran.
///
/// So this module is deliberately NOT feature-gated. It does three things:
///
///   1. names the required invocation in the default run's own output, under a test
///      name that says what is missing;
///   2. under `--features bench`, references a marker the gated module defines, so
///      the suite is proved to have compiled rather than assumed; and
///   3. honours `AB_REQUIRE_BENCH_GATES=1` by FAILING a `bench`-less run — the
///      opt-in a CI job or an agent uses when "the GPU gates ran" is the claim
///      being made.
///
/// It does not fail a plain developer run: making the default invocation red would
/// just teach people to ignore it.
#[cfg(test)]
mod gating {
    /// The four gates the segmented VM's acceptance rests on, so a reader of a
    /// `bench`-less run can see exactly what did not execute.
    const GPU_GATES: [&str; 4] = [
        "bwd_seg_r0_parity_over_k_and_banks",
        "bwd_seg_cont_d0_d3_parity_over_k",
        "bwd_seg_epilogues_are_bit_identical",
        "bwd_seg_add_sub_l0_r0_matrix",
    ];

    /// Read only by the `bench`-less arm below, which is the arm that can lie about
    /// having run the gates. Under `--features bench` there is nothing to opt into,
    /// so the constant is genuinely unused there.
    #[cfg_attr(feature = "bench", allow(dead_code))]
    const REQUIRE_ENV: &str = "AB_REQUIRE_BENCH_GATES";

    #[test]
    fn bwd_coeff_gating_notice() {
        let invocation = "cargo test -p gpu_circuit_prover --release --features bench --no-run, \
                          then run the binary under .agents/bin/with_gpu_lock.sh";

        #[cfg(feature = "bench")]
        {
            // A real link to the gated module: if `seg_gpu_tests` is renamed, moved
            // or loses its marker, this stops compiling under `--features bench`
            // instead of silently going back to proving nothing.
            assert!(
                super::seg_gpu_tests::SEG_PARITY_SUITE_COMPILED,
                "the bench-gated GPU parity suite must be compiled in a bench build"
            );
            eprintln!(
                "[bwd-seg] bench feature ON: the GPU parity suite is compiled. \
                 Its gates are #[ignore]d GPU tests -- {GPU_GATES:?} -- so they \
                 still need --ignored to actually run."
            );
        }

        #[cfg(not(feature = "bench"))]
        {
            let message = format!(
                "[bwd-seg] bench feature OFF: the segmented lean VM's GPU suite \
                 was NOT compiled and NONE of its gates ran ({GPU_GATES:?}). This run \
                 says nothing about them. To run them: {invocation}. Set \
                 {REQUIRE_ENV}=1 to make this a failure."
            );
            eprintln!("{message}");
            assert!(
                std::env::var_os(REQUIRE_ENV).is_none(),
                "{REQUIRE_ENV} is set, but this binary was built WITHOUT --features bench, \
                 so the GPU gates cannot have run. {message}"
            );
        }

        // Referenced in both configurations so neither arm carries a dead binding.
        assert!(!invocation.is_empty() && GPU_GATES.len() == 4);
    }
}
