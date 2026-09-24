pub const PRECOMPILE_MODE_BITS: usize = 3;
pub const ITERATION_BITS: usize = 3;
pub const ROUND_BITS: usize = 5;

pub const KECCAK5_TOTAL_NUM_CONTROL_BITS: usize =
    PRECOMPILE_MODE_BITS + ITERATION_BITS + ROUND_BITS;

pub const NUM_X10_INDIRECT_U64_WORDS: usize = 6;
pub const KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS: usize = NUM_X10_INDIRECT_U64_WORDS;

pub const KECCAK_SPECIAL5_CSR_REGISTER: u32 = super::super::NON_DETERMINISM_CSR + 11;

pub const KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS: usize = 31;
pub const KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS_PADDED: usize =
    KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS.next_power_of_two();

pub const NUM_DELEGATION_CALLS_FOR_KECCAK_F1600: usize = 649;

/// Keccak-f1600 state plus scratch space in the layout expected by the
/// `keccak_special5` delegation circuit.
///
/// The precompile ABI requires the base pointer in `x11` to be 256-byte aligned
/// so the circuit can address all state words through cheap low-bit offsets.
#[derive(Debug, Clone)]
#[repr(align(256))]
pub struct KeccakF1600State(pub [u64; KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS_PADDED]);

impl KeccakF1600State {
    #[inline(always)]
    pub const fn zeroed() -> Self {
        Self([0; KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS_PADDED])
    }

    #[inline(always)]
    pub fn as_words(&self) -> &[u64; KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS] {
        unsafe { core::mem::transmute(&self.0) }
    }

    #[inline(always)]
    pub fn as_words_mut(&mut self) -> &mut [u64; KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS] {
        unsafe { core::mem::transmute(&mut self.0) }
    }
}

#[cfg(target_arch = "riscv32")]
#[inline(always)]
pub fn keccak_f1600(state: &mut KeccakF1600State) {
    super::keccak_k2::keccak_f1600(state)
}

pub const NUM_KECCAK_SPECIAL5_REGISTER_ACCESSES: usize = 2;
pub const NUM_KECCAK_SPECIAL5_INDIRECT_READS: usize = 0;

pub const KECCAK_SPECIAL5_X11_NUM_WRITES: usize = NUM_X10_INDIRECT_U64_WORDS * 2; // 6 u64 r/w
pub const KECCAK_SPECIAL5_TOTAL_RAM_ACCESSES: usize = KECCAK_SPECIAL5_X11_NUM_WRITES;
pub const KECCAK_SPECIAL5_BASE_ABI_REGISTER: u32 = 10;

pub const INITIAL_KECCAK_F1600_CONTROL_VALUE: u32 = 0;
pub const FINAL_KECCAK_F1600_CONTROL_VALUE: u32 = 1544;

#[cfg(test)]
mod tests {
    extern crate std;

    use super::super::keccak_k2::{
        NUM_KECCAK_K2_CHI5_CALLS, NUM_KECCAK_K2_COLUMN_PARITY_CALLS, NUM_KECCAK_K2_THETA_RHO_CALLS,
    };
    use super::*;
    use std::{format, vec};
    use std::{fs, process::Command, string::String};

    const RISCV_TARGET: &str = "riscv32im-unknown-none-elf";

    #[test]
    fn keccak_f1600_state_layout_matches_delegation_abi() {
        assert_eq!(core::mem::align_of::<KeccakF1600State>(), 256);
        assert_eq!(core::mem::size_of::<KeccakF1600State>(), 256);
    }

    // We want to make sure that compiler doesn't inject anything between `csrrw` invocations,
    // so we use a snapshot to ensure the shape of generated code.
    //
    // This test expects the RISC-V target and cargo-binutils to be installed, which matches the
    // Airbender development environment and CI setup.
    #[test]
    fn keccak_f1600_riscv_codegen_emits_single_uninterrupted_delegation_run() {
        let fixture_dir = create_codegen_fixture();
        let fixture_crate = fixture_dir.path();
        let manifest_path = fixture_crate.join("Cargo.toml");

        let disassembly = run_command(&format!(
            "cargo objdump --manifest-path {} --locked --offline --lib --release --target {RISCV_TARGET} -- --disassemble --no-show-raw-insn",
            manifest_path.display()
        ));

        let disassembly = normalize_disassembly(&disassembly);
        for (csr, calls) in [
            ("0x7cc", NUM_KECCAK_K2_THETA_RHO_CALLS),
            ("0x7cd", NUM_KECCAK_K2_COLUMN_PARITY_CALLS),
            ("0x7ce", NUM_KECCAK_K2_CHI5_CALLS),
        ] {
            assert_eq!(
                disassembly.matches(&format!("csrw\t{csr}, zero")).count(),
                calls
            );
        }
        insta::assert_snapshot!("keccak_f1600_riscv_codegen", disassembly);
    }

    fn create_codegen_fixture() -> tempfile::TempDir {
        let fixture_dir = tempfile::tempdir().expect("test fixture directory should be created");
        let fixture_crate = fixture_dir.path();

        fs::create_dir_all(fixture_crate.join("src"))
            .expect("test fixture source directory should be created");

        // This fixture deliberately stays below the SHA3 layer. It exercises the
        // migrated ABI surface directly and leaves permutation correctness tests
        // to crates that already own a host-side Keccak implementation.
        fs::write(
            fixture_crate.join("Cargo.toml"),
            format!(
                r#"[package]
name = "keccak_codegen_fixture"
version = "0.0.0"
edition = "2021"

[dependencies]
common_constants = {{ path = "{}" }}
"#,
                env!("CARGO_MANIFEST_DIR")
            ),
        )
        .expect("test fixture manifest should be written");

        fs::write(
            fixture_crate.join("src/lib.rs"),
            r#"
#![no_std]

use common_constants::delegation_types::keccak_special5::{keccak_f1600, KeccakF1600State};

#[no_mangle]
pub extern "C" fn invoke_keccak_f1600(state: &mut KeccakF1600State) {
    keccak_f1600(state);
}
"#,
        )
        .expect("test fixture library should be written");

        fixture_dir
    }

    fn run_command(cmd: &str) -> String {
        let mut args = cmd.split_whitespace();
        let command = args.next().expect("test command should not be empty");
        let output = Command::new(command)
            .args(args)
            .env("CARGO_NET_OFFLINE", "true")
            .output()
            .expect("while attempting to run test command");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "command `{cmd}` failed:\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );

        stdout.into_owned()
    }

    // Only fetch the generated body for the exported fixture function so the snapshot
    // stays focused on the delegation run rather than object-file boilerplate.
    fn normalize_disassembly(disassembly: &str) -> String {
        disassembly
            .lines()
            .skip_while(|line| line.contains("<invoke_keccak_f1600>:") == false)
            .skip(1)
            .filter(|line| line.trim().is_empty() == false)
            .map(str::trim)
            .collect::<vec::Vec<_>>()
            .join("\n")
    }
}
