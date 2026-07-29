fn main() {
    // The build script lives under `build/`; once any `rerun-if-changed` is
    // emitted (the shared helper emits them for `native/`), Cargo tracks only
    // the declared paths — so watch the build dir explicitly too.
    println!("cargo:rerun-if-changed=build");
    // `circuit_prover_native` links blake2s-dependent kernels (`ops/gkr_ops*`,
    // `whir/leaves`) that `#include "hash.cuh"`; the helper auto-forwards
    // `DEP_GPU_HASH_NATIVE_INCLUDE` (and `DEP_GPU_CORE_NATIVE_INCLUDE`) as CMake
    // include defines. `deterministic_pow` propagates to `AB_DETERMINISTIC_POW`
    // so the GPU PoW search matches the host verifier (proof parity).
    let archive = gpu_native_build::CudaArchive::new("circuit_prover_native", "GPU_PROVER")
        .deterministic_pow(true);
    // The Rust `bench` feature (cfg(all(test, feature = "bench"))) gates the
    // GKR eval-ISA A/B bench harness (`prover::gkr::forward::bench_interp` +
    // `vm::gpu_tests`), which drives the production v2 fwd-VM kernels — no
    // bench-only native sources remain, so this feature has no CMake side.

    // The segmented VM's register-pin sweep (measurement-trust pass §4.1).
    //
    // THE SHIPPED DEFAULT LIVES HERE, not in the CMake cache: this script
    // forwards a value on every build, so a `CACHE STRING` default would always
    // be overridden and an env-free build could never carry a pin. `0` means "no
    // qualifier on the nine swept continuation executors" — the natural band —
    // and the pass's final ship decision changes THIS constant.
    const SHIPPED_CONT_MAXNREG: &str = "0";
    println!("cargo:rerun-if-env-changed=AB_GKR_SEG_CONT_MAXNREG");
    println!("cargo:rerun-if-env-changed=AB_GKR_SEG_NO_MAXNREG");
    let cont_maxnreg = std::env::var("AB_GKR_SEG_CONT_MAXNREG")
        .unwrap_or_else(|_| SHIPPED_CONT_MAXNREG.to_owned());
    let cont_maxnreg = cont_maxnreg.trim().to_owned();
    let budget: u32 = cont_maxnreg.parse().unwrap_or_else(|error| {
        panic!("AB_GKR_SEG_CONT_MAXNREG must be an integer register budget (0 = natural), got {cont_maxnreg:?}: {error}")
    });
    assert!(
        budget == 0 || (32..=255).contains(&budget),
        "a __maxnreg__ budget outside 32..=255 is not a register band this family has"
    );
    // The H9 control (§7.2 row 2b): suppresses EVERY __maxnreg__ in the family,
    // the ten permanent ones included, so the control cannot carry the very
    // directives it exists to test.
    let no_maxnreg = if std::env::var_os("AB_GKR_SEG_NO_MAXNREG").is_some() {
        "ON"
    } else {
        "OFF"
    };
    // §4.5's loop-form attribution arm: the delta-3 fold unrolled, delta <= 2
    // rolled. A DEFINE rather than a source edit, so the fourth build comes off
    // the SAME frozen revision as the three pin levels — M4's
    // one-immutable-revision rule would otherwise be broken by an edit made after
    // the freeze, and the pin winner would stop being attributable to the pin.
    println!("cargo:rerun-if-env-changed=AB_GKR_SEG_D3_UNROLL");
    let d3_unroll = if std::env::var_os("AB_GKR_SEG_D3_UNROLL").is_some() {
        "ON"
    } else {
        "OFF"
    };
    let archive = archive
        .define("AB_GKR_SEG_CONT_MAXNREG", &cont_maxnreg)
        .define("AB_GKR_SEG_NO_MAXNREG", no_maxnreg)
        .define("AB_GKR_SEG_D3_UNROLL", d3_unroll);
    archive.build();
}
