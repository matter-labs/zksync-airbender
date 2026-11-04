//! Compliance tests for the transpiler VM.
//!
//! The following instructions are not tested because the VM does not support them:
//!  - I-fence
//!  - M-div
//!  - M-mulh
//!  - M-mulhsu
//!  - M-rem

#![allow(non_snake_case)]

use std::convert::Infallible;

use fuzzing::rv32im::run_on_airbender;
use fuzzing::rv32im::run_on_unicorn;
use log::LevelFilter;
use rstest::rstest;
use simplelog::Config;
use simplelog::TestLogger;

const PASSING_TEST: [u32; 8] = [97, 97, 97, 97, 97, 97, 97, 97];
// const FAILING_TEST: [u32; 8] = [65, 65, 65, 65, 65, 65, 65, 65];

fn setup_logging() {
    let _ = TestLogger::init(LevelFilter::Debug, Config::default());
}

fn run_compliance_test<E: std::fmt::Display>(
    name: &str,
    cb: impl Fn() -> Result<Option<[u32; 8]>, E>,
) {
    setup_logging();

    let result = match cb() {
        Ok(Some(regs)) => regs,
        Ok(None) => {
            panic!("{name} execution failed");
        }
        Err(err) => {
            panic!("{name} setup failed: {err}");
        }
    };

    assert_eq!(result, PASSING_TEST);
}

macro_rules! include_bin {
    ($name:expr) => {
        include_bytes!(concat!("compliance-tests-programs/", $name, ".bin"))
    };
}

macro_rules! include_text {
    ($name:expr) => {
        include_bytes!(concat!("compliance-tests-programs/", $name, ".text"))
    };
}

macro_rules! I {
    ($name:ident) => {
        concat!("I-", stringify!($name), "-00")
    };
}

macro_rules! M {
    ($name:ident) => {
        concat!("M-", stringify!($name), "-00")
    };
}

#[rstest]
#[case::I_add(include_bin!(I!(add)), include_text!(I!(add)))]
#[case::I_addi(include_bin!(I!(addi_patched)), include_text!(I!(addi_patched)))]
#[case::I_and(include_bin!(I!(and_patched)), include_text!(I!(and_patched)))]
#[case::I_andi(include_bin!(I!(andi)), include_text!(I!(andi)))]
#[case::I_auipc(include_bin!(I!(auipc)), include_text!(I!(auipc)))]
#[case::I_beq(include_bin!(I!(beq)), include_text!(I!(beq)))]
#[case::I_bge(include_bin!(I!(bge)), include_text!(I!(bge)))]
#[case::I_bgeu(include_bin!(I!(bgeu)), include_text!(I!(bgeu)))]
#[case::I_blt(include_bin!(I!(blt)), include_text!(I!(blt)))]
#[case::I_bltu(include_bin!(I!(bltu)), include_text!(I!(bltu)))]
#[case::I_bne(include_bin!(I!(bne)), include_text!(I!(bne)))]
#[case::I_jal(include_bin!(I!(jal)), include_text!(I!(jal)))]
#[case::I_jalr(include_bin!(I!(jalr)), include_text!(I!(jalr)))]
#[case::I_lb(include_bin!(I!(lb)), include_text!(I!(lb)))]
#[case::I_lbu(include_bin!(I!(lbu)), include_text!(I!(lbu)))]
#[case::I_lh(include_bin!(I!(lh)), include_text!(I!(lh)))]
#[case::I_lhu(include_bin!(I!(lhu)), include_text!(I!(lhu)))]
#[case::I_lui(include_bin!(I!(lui)), include_text!(I!(lui)))]
#[case::I_lw(include_bin!(I!(lw)), include_text!(I!(lw)))]
#[case::I_nop(include_bin!(I!(nop)), include_text!(I!(nop)))]
#[case::I_or(include_bin!(I!(or)), include_text!(I!(or)))]
#[case::I_ori(include_bin!(I!(ori)), include_text!(I!(ori)))]
#[case::I_sb(include_bin!(I!(sb)), include_text!(I!(sb)))]
#[case::I_sh(include_bin!(I!(sh)), include_text!(I!(sh)))]
#[case::I_sll(include_bin!(I!(sll)), include_text!(I!(sll)))]
#[case::I_slli(include_bin!(I!(slli)), include_text!(I!(slli)))]
#[case::I_slt(include_bin!(I!(slt)), include_text!(I!(slt)))]
#[case::I_slti(include_bin!(I!(slti_patched)), include_text!(I!(slti_patched)))]
#[case::I_sltiu(include_bin!(I!(sltiu)), include_text!(I!(sltiu)))]
#[case::I_sltu(include_bin!(I!(sltu)), include_text!(I!(sltu)))]
#[case::I_sra(include_bin!(I!(sra)), include_text!(I!(sra)))]
#[case::I_srai(include_bin!(I!(srai)), include_text!(I!(srai)))]
#[case::I_srl(include_bin!(I!(srl)), include_text!(I!(srl)))]
#[case::I_srli(include_bin!(I!(srli)), include_text!(I!(srli)))]
#[case::I_sub(include_bin!(I!(sub)), include_text!(I!(sub)))]
#[case::I_sw(include_bin!(I!(sw)), include_text!(I!(sw)))]
#[case::I_xor(include_bin!(I!(xor)), include_text!(I!(xor)))]
#[case::I_xori(include_bin!(I!(xori)), include_text!(I!(xori)))]
#[case::M_divu(include_bin!(M!(divu)), include_text!(M!(divu)))]
#[case::M_mul(include_bin!(M!(mul)), include_text!(M!(mul)))]
#[case::M_mulhu(include_bin!(M!(mulhu)), include_text!(M!(mulhu)))]
#[case::M_remu(include_bin!(M!(remu)), include_text!(M!(remu)))]
fn test_unicorn<const N: usize, const M: usize>(#[case] binary: &[u8; N], #[case] text: &[u8; M]) {
    run_compliance_test("Unicorn", || {
        run_on_unicorn(binary, Some(text.len() as u64))
    })
}

#[rstest]
#[case::I_add(include_bin!(I!(add)), include_text!(I!(add)))] // Passes
#[case::I_addi(include_bin!(I!(addi_patched)), include_text!(I!(addi_patched)))]
#[case::I_and(include_bin!(I!(and_patched)), include_text!(I!(and_patched)))]
#[case::I_andi(include_bin!(I!(andi)), include_text!(I!(andi)))] // Passes
#[case::I_auipc(include_bin!(I!(auipc)), include_text!(I!(auipc)))] // Passes
#[case::I_beq(include_bin!(I!(beq)), include_text!(I!(beq)))] // Passes
#[case::I_bge(include_bin!(I!(bge)), include_text!(I!(bge)))] // Passes
#[case::I_bgeu(include_bin!(I!(bgeu)), include_text!(I!(bgeu)))] // Passes
#[case::I_blt(include_bin!(I!(blt)), include_text!(I!(blt)))] // Passes
#[case::I_bltu(include_bin!(I!(bltu)), include_text!(I!(bltu)))] // Passes
#[case::I_bne(include_bin!(I!(bne)), include_text!(I!(bne)))] // Passes
#[case::I_jal(include_bin!(I!(jal)), include_text!(I!(jal)))] // Passes
#[case::I_jalr(include_bin!(I!(jalr)), include_text!(I!(jalr)))] // Passes
#[case::I_lb(include_bin!(I!(lb)), include_text!(I!(lb)))] // Passes
#[case::I_lbu(include_bin!(I!(lbu)), include_text!(I!(lbu)))] // Passes
#[case::I_lh(include_bin!(I!(lh)), include_text!(I!(lh)))] // Passes
#[case::I_lhu(include_bin!(I!(lhu)), include_text!(I!(lhu)))] // Passes
#[case::I_lui(include_bin!(I!(lui)), include_text!(I!(lui)))] // Passes
#[case::I_lw(include_bin!(I!(lw)), include_text!(I!(lw)))] // Passes
#[case::I_nop(include_bin!(I!(nop)), include_text!(I!(nop)))] // Passes
#[case::I_or(include_bin!(I!(or)), include_text!(I!(or)))] // Passes
#[case::I_ori(include_bin!(I!(ori)), include_text!(I!(ori)))] // Passes
#[case::I_sb(include_bin!(I!(sb)), include_text!(I!(sb)))] // Passes
#[case::I_sh(include_bin!(I!(sh)), include_text!(I!(sh)))] // Passes
#[case::I_sll(include_bin!(I!(sll)), include_text!(I!(sll)))] // Passes
#[case::I_slli(include_bin!(I!(slli)), include_text!(I!(slli)))] // Passes
#[case::I_slt(include_bin!(I!(slt)), include_text!(I!(slt)))] // Passes
#[case::I_slti(include_bin!(I!(slti_patched)), include_text!(I!(slti_patched)))]
#[case::I_sltiu(include_bin!(I!(sltiu)), include_text!(I!(sltiu)))] // Passes
#[case::I_sltu(include_bin!(I!(sltu)), include_text!(I!(sltu)))] // Passes
#[case::I_sra(include_bin!(I!(sra)), include_text!(I!(sra)))] // Passes
#[case::I_srai(include_bin!(I!(srai)), include_text!(I!(srai)))] // Passes
#[case::I_srl(include_bin!(I!(srl)), include_text!(I!(srl)))] // Passes
#[case::I_srli(include_bin!(I!(srli)), include_text!(I!(srli)))] // Passes
#[case::I_sub(include_bin!(I!(sub)), include_text!(I!(sub)))] // Passes
#[case::I_sw(include_bin!(I!(sw)), include_text!(I!(sw)))] // Passes
#[case::I_xor(include_bin!(I!(xor)), include_text!(I!(xor)))] // Passes
#[case::I_xori(include_bin!(I!(xori)), include_text!(I!(xori)))] // Passes
#[case::M_divu(include_bin!(M!(divu)), include_text!(M!(divu)))] // Passes
#[case::M_mul(include_bin!(M!(mul)), include_text!(M!(mul)))] // Passes
#[case::M_mulhu(include_bin!(M!(mulhu)), include_text!(M!(mulhu)))] // Passes
#[case::M_remu(include_bin!(M!(remu)), include_text!(M!(remu)))] // Passes
fn test_airbender<const N: usize, const M: usize>(
    #[case] binary: &[u8; N],
    #[case] text: &[u8; M],
) {
    run_compliance_test::<Infallible>("Airbender", || {
        Ok(run_on_airbender::<false>(binary, Some(text)))
    })
}
