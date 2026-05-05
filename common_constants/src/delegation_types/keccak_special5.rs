pub const PRECOMPILE_MODE_BITS: usize = 3;
pub const ITERATION_BITS: usize = 3;
pub const ROUND_BITS: usize = 5;

pub const KECCAK5_TOTAL_NUM_CONTROL_BITS: usize =
    PRECOMPILE_MODE_BITS + ITERATION_BITS + ROUND_BITS;

pub const NUM_X10_INDIRECT_U64_WORDS: usize = 6;
pub const KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS: usize = NUM_X10_INDIRECT_U64_WORDS;

pub const KECCAK_SPECIAL5_CSR_REGISTER: u32 = super::NON_DETERMINISM_CSR + 11;

pub const KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS: usize = 31;

pub const NUM_DELEGATION_CALLS_FOR_KECCAK_F1600: usize = 649;

/// Keccak-f1600 state plus scratch space in the layout expected by the
/// `keccak_special5` delegation circuit.
///
/// The precompile ABI requires the base pointer in `x11` to be 256-byte aligned
/// so the circuit can address all state words through cheap low-bit offsets.
#[derive(Debug, Clone)]
#[repr(align(256))]
pub struct KeccakF1600State(pub [u64; KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS]);

impl KeccakF1600State {
    #[inline(always)]
    pub const fn zeroed() -> Self {
        Self([0; KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS])
    }

    #[inline(always)]
    pub fn as_words(&self) -> &[u64; KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS] {
        &self.0
    }

    #[inline(always)]
    pub fn as_words_mut(&mut self) -> &mut [u64; KECCAK_SPECIAL5_STATE_AND_SCRATCH_U64_WORDS] {
        &mut self.0
    }
}

#[cfg(target_arch = "riscv32")]
#[inline(always)]
pub fn keccak_f1600(state: &mut KeccakF1600State) {
    let state_ptr = state.0.as_mut_ptr();

    unsafe {
        // The transpiler recognizes Keccak-f1600 as one uninterrupted run of
        // identical CSR instructions. Keeping the whole run in one `asm!` block
        // prevents LLVM from scheduling spills or unrelated instructions into
        // the middle of the delegation's internal control-state sequence.
        seq_macro::seq!(_ in 0..649 {
            core::arch::asm!(
                "add x10, x0, x0",
                #( "csrrw x0, 0x7CB, x0", )*
                in("x11") state_ptr.addr(),
                out("x10") _,
                options(nostack, preserves_flags)
            );
        });
    }
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

    use super::*;
    use std::{format, vec};
    use std::{fs, process::Command, string::String};

    const RISCV_TARGET: &str = "riscv32im-unknown-none-elf";
    const KECCAK_SPECIAL5_CSRRW: &str = "csrw\t0x7cb, zero";

    #[test]
    fn keccak_f1600_state_layout_matches_delegation_abi() {
        assert_eq!(core::mem::align_of::<KeccakF1600State>(), 256);
        assert_eq!(core::mem::size_of::<KeccakF1600State>(), 256);
    }

    // We want to make sure that compiler doesn't inject anything between `csrrw` invocations,
    // so we use a snapshot to ensure the shape of generated code.
    //
    // This test expects riscv target and cargo-objcopy to be installed unconditionally, which
    // should be fine as they're required for working with airbender anyway.
    #[test]
    fn keccak_f1600_riscv_codegen_emits_single_uninterrupted_delegation_run() {
        let fixture_dir = create_codegen_fixture();
        let fixture_crate = fixture_dir.path();
        let manifest_path = fixture_crate.join("Cargo.toml");

        let disassembly = run_command(&format!(
            "cargo objdump --manifest-path {} --locked --lib --release --target {RISCV_TARGET} -- --disassemble --no-show-raw-insn",
            manifest_path.display()
        ));

        let disassembly = normalize_disassembly(&disassembly);
        assert_eq!(
            disassembly.matches(KECCAK_SPECIAL5_CSRRW).count(),
            NUM_DELEGATION_CALLS_FOR_KECCAK_F1600
        );
        insta::assert_snapshot!("keccak_f1600_riscv_codegen", disassembly);
    }

    fn create_codegen_fixture() -> tempfile::TempDir {
        let fixture_dir = tempfile::tempdir().unwrap();
        let fixture_crate = fixture_dir.path();

        fs::create_dir_all(fixture_crate.join("src")).unwrap();

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
        .unwrap();

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
        .unwrap();

        fixture_dir
    }

    fn run_command(cmd: &str) -> String {
        let mut args = cmd.split_whitespace();
        let command = args.next().expect("test command should not be empty");
        let output = Command::new(command)
            .args(args)
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

    // Only fetch relevant part of disassembly
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
