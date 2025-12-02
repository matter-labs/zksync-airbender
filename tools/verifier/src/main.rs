#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]

extern "C" {
    // Boundaries of the heap
    static mut _sheap: usize;
    static mut _eheap: usize;

    // Boundaries of the stack
    static mut _sstack: usize;
    static mut _estack: usize;
}
#[cfg(any(
    feature = "universal_circuit",
    feature = "universal_circuit_no_delegation"
))]
use reduced_keccak::Keccak32;

core::arch::global_asm!(include_str!("asm/asm_reduced.S"));

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

#[export_name = "_setup_interrupts"]
pub unsafe fn custom_setup_interrupts() {
    extern "C" {
        fn _machine_start_trap();
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct MachineTrapFrame {
    pub registers: [u32; 32],
}

/// Exception (trap) handler in rust.
/// Called from the asm/asm.S
#[link_section = ".trap.rust"]
#[export_name = "_machine_start_trap_rust"]
pub extern "C" fn machine_start_trap_rust(_trap_frame: *mut MachineTrapFrame) -> usize {
    {
        unsafe { core::hint::unreachable_unchecked() }
    }
}

#[cfg(feature = "panic_output")]
#[macro_export]
macro_rules! print
{
	($($args:tt)+) => ({
		use core::fmt::Write;
		let _ = write!(riscv_common::QuasiUART::new(), $($args)+);
	});
}

#[cfg(feature = "panic_output")]
#[macro_export]
macro_rules! println
{
	() => ({
		crate::print!("\r\n")
	});
	($fmt:expr) => ({
		crate::print!(concat!($fmt, "\r\n"))
	});
	($fmt:expr, $($args:tt)+) => ({
		crate::print!(concat!($fmt, "\r\n"), $($args)+)
	});
}

#[cfg(feature = "panic_output")]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    print_panic(_info);

    riscv_common::zksync_os_finish_error()
}

#[cfg(feature = "panic_output")]
fn print_panic(_info: &core::panic::PanicInfo) {
    print!("Aborting: ");
    if let Some(p) = _info.location() {
        println!("line {}, file {}", p.line(), p.file(),);

        if let Some(m) = _info.message().as_str() {
            println!("line {}, file {}: {}", p.line(), p.file(), m,);
        } else {
            println!(
                "line {}, file {}, message:\n{}",
                p.line(),
                p.file(),
                _info.message()
            );
        }
    } else {
        println!("no information available");
    }
}

#[cfg(feature = "base_layer")]
unsafe fn workload() -> ! {
    let output = full_statement_verifier::verify_base_layer();
    riscv_common::zksync_os_finish_success_extended(&output);
}

#[cfg(any(feature = "recursion_step", feature = "recursion_step_no_delegation"))]
unsafe fn workload() -> ! {
    let output = full_statement_verifier::verify_recursion_layer();
    riscv_common::zksync_os_finish_success_extended(&output);
}

#[cfg(any(feature = "recursion_log_23_step"))]
unsafe fn workload() -> ! {
    let output = full_statement_verifier::verify_recursion_log_23_layer();
    riscv_common::zksync_os_finish_success_extended(&output);
}

#[cfg(feature = "final_recursion_step")]
unsafe fn workload() -> ! {
    let output = full_statement_verifier::verify_final_recursion_layer();
    riscv_common::zksync_os_finish_success_extended(&output);
}

#[cfg(any(
    feature = "universal_circuit",
    feature = "universal_circuit_no_delegation"
))]
// This verifier can handle any circuit and any layer.
// It uses the first word in the input to determine which circuit to verify.
unsafe fn workload() -> ! {
    let metadata = riscv_common::csr_read_word();

    // These values should match VerifierCircuitsIdentifiers.
    match metadata {
        0 => {
            let output = full_statement_verifier::verify_base_layer();
            riscv_common::zksync_os_finish_success_extended(&output);
        }
        1 => {
            let output = full_statement_verifier::verify_recursion_layer();
            riscv_common::zksync_os_finish_success_extended(&output);
        }
        // 2 used to be final layer, but we don't have that anymore.
        3 => {
            full_statement_verifier::RISC_V_VERIFIER_PTR(
                &mut core::mem::MaybeUninit::uninit().assume_init_mut(),
                &mut full_statement_verifier::verifier_common::ProofPublicInputs::uninit(),
            );
            riscv_common::zksync_os_finish_success(&[1, 2, 3, 0, 0, 0, 0, 0]);
        }
        // Combine 2 proofs into one.
        4 => {
            // First - verify both proofs (keep reading from the CSR).
            let output1 = full_statement_verifier::verify_recursion_layer();
            let output2 = full_statement_verifier::verify_recursion_layer();

            // merge the inputs together
            let result = merge_recursive_circuit_output(output1, output2);

            riscv_common::zksync_os_finish_success_extended(&result);
        }
        5 => {
            let output = full_statement_verifier::verify_recursion_log_23_layer();
            riscv_common::zksync_os_finish_success_extended(&output);
        }
        // Combine multiple proofs into one.
        // This is similar to 4, combine 2 proofs into one, but now we combine N proofs into one.
        // The advantage is in the number of proving rounds you need to do.
        // Option 4 requires O(n) rounds of proving, whilst this requires a single round (time will be closer to O(logn), due to recursion).
        //
        // The right way to think about this method is a rolling hash over circuits:
        // keccak(..., keccak(keccak(output1 || output2), output3), output4, ... outputN)
        6 => {
            let no_circuits = riscv_common::csr_read_word();
            assert!(no_circuits >= 2, "Requires at least two circuits to verify");

            // verify first proof & use it as the seed for the rolling hash
            //
            // the proof's outputs are as follows:
            // output[0..8] - the actual output of the circuit
            // output[8..16] - the verification key (should be the same across all proofs, checked inside merge_recursive_circuit_output)
            // merging is done over inputs [0..8], whilst key is not modified (being copied over and over)
            let mut rolling_hash = full_statement_verifier::verify_recursion_layer();

            // iterate over remaining circuits
            for _ in 1..no_circuits {
                // verify proof
                let output = full_statement_verifier::verify_recursion_layer();

                // build the rolling hash over the remaining proofs' outputs (ensuring they belong to same proving chain)
                rolling_hash = merge_recursive_circuit_output(rolling_hash, output);
            }

            riscv_common::zksync_os_finish_success_extended(&rolling_hash);
        }
        // Unknown metadata.
        _ => {
            riscv_common::zksync_os_finish_error();
        }
    }
}

#[cfg(any(
    feature = "universal_circuit",
    feature = "universal_circuit_no_delegation"
))]
/// Merges proof outputs from two recursive circuits into one output.
/// TL;DR; Keccaks the two outputs together.
///
/// Note, a proof is structured as follows:
/// - first 8 u32s are the actual proof output
/// - last 8 u32s are the verification key identifier (proving chain)
fn merge_recursive_circuit_output(first: [u32; 16], second: [u32; 16]) -> [u32; 16] {
    // Proving chain must be equal
    for i in 8..16 {
        assert_eq!(first[i], second[i], "Proving chains must be equal");
    }

    // To make it compatible with our SNARK - we'll assume that last register (7th) is 0 (as snark ignores that too).
    // and we'll actually shift them all by 1.

    // TODO: in the future, check explicitly that output1[7] && output2[7] == 0.
    let mut hasher = Keccak32::new();
    hasher.update(&[0u32]);

    for val in &first[0..7] {
        hasher.update(&[*val]);
    }

    // TODO: in the future, check explicitly that output1[7] && output2[7] == 0.
    hasher.update(&[0u32]);

    for val in &second[0..7] {
        hasher.update(&[*val]);
    }

    let mut result = [0u32; 16];
    // merged outputs
    result[0..8].copy_from_slice(&hasher.finalize());
    // same vk
    result[8..16].copy_from_slice(&first[8..16]);

    result
}

#[cfg(feature = "verifier_tests")]
unsafe fn workload() -> ! {
    use core::mem::MaybeUninit;
    use verifier::concrete::size_constants::*;
    use verifier::verify;
    use verifier::ProofPublicInputs;

    use verifier::verifier_common::ProofOutput;

    let mut proof_output: ProofOutput<TREE_CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 1> =
        unsafe { MaybeUninit::uninit().assume_init() };
    let mut state_variables = ProofPublicInputs::uninit();

    unsafe { verify(&mut proof_output, &mut state_variables) };

    let mut output = [0u32; 16];
    for i in 0..16 {
        output[i] = i as u32;
    }
    riscv_common::zksync_os_finish_success_extended(&output)
}

#[inline(never)]
fn main() -> ! {
    unsafe { workload() }
}
