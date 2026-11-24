import SailRV32.Classify
import SailRV32.Prelude
import SailRV32.Flen
import SailRV32.Vlen
import SailRV32.FdextRegs
import SailRV32.VextRegs
import SailRV32.FextInsts
import SailRV32.DextInsts
import SailRV32.ZfhInsts
import SailRV32.VextUtilsInsts

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ArchSem

noncomputable section
namespace SailRV32

open ArchSem

namespace Functions

open zvk_vsm4r_funct6
open zvk_vsha2_funct6
open zvk_vaesem_funct6
open zvk_vaesef_funct6
open zvk_vaesdm_funct6
open zvk_vaesdf_funct6
open zvabd_vwabda_func6
open zvabd_vabd_func6
open zilx_mode
open zicondop
open xRET_type
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open wrsop
open write_kind
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vstart_class
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vextfunct6
open vector_support
open uop
open tdata
open stateen_bit
open sopw
open sop
open seed_opst
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfwvvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pte_check_failure
open pmpAddrMatch
open physaddr
open page_based_mem_type
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open ntl_type
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open misaligned_exception
open mem_payload
open maskfunct3
open landing_pad_expectation
open iop
open instruction
open indexed_mop
open hlvop
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open fregno
open fregidx
open float_class
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extop_zbb
open extension
open exception
open event_csr
open csrop
open cregidx
open checked_cbop
open cfregidx
open cbop_zicbop
open cbop_zicbom
open cbie
open cacheop
open bropw_zbb
open brop_zbs
open brop_zbkb
open brop_zbb
open breakpoint_cause
open bop
open biop_zbs
open biop
open barrier_kind
open amoop
open agtype
open access_kind
open XtvecModeReservedBehavior
open XipReadType
open XenvcfgCbieReservedBehavior
open WaitReason
open VectorHalf
open Trigger
open Trig_Type
open Trig_Match
open Trig_Action
open TrapVectorMode
open TrapCause
open TranslationStage
open Step
open Splittability
open Software_Check_Code
open Signedness
open Sdtrig_breakpoint_reentrancy
open SWCheckCodes
open SATPMode
open Reservability
open Register
open RV32ZdinxOddRegisterReservedBehavior
open Privileged_ISA_Version
open Privilege
open PointerMaskingMode
open PmpWriteOnlyReservedBehavior
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open PM_Ext
open OOBVstartReservedBehavior
open MemoryRegionType
open MemoryAccessType
open InterruptType
open IllegalVtypeReservedBehavior
open ISA_Format
open Hit
open HartState
open HGATPMode
open FflagsDirtyPolicy
open FetchResult
open FetchBytes_Result
open FeatureEnabledResult
open FcsrRmReservedBehavior
open Ext_DataAddr_Check
open ExtStatus
open ExtContextPolicy
open ExecutionResult
open ExceptionType
open Event
open Compare_Selection
open CSRCheckResult
open CSRAccessType
open AtomicSupport
open Architecture
open AmocasOddRegisterReservedBehavior

/-- Type quantifiers: SEW : Nat, List.elem SEW [8, 16, 32, 64] -/
def valid_fp_op (SEW : Nat) (rm_3b : (BitVec 3)) : Bool :=
  let valid_sew := ((SEW ≥b 8) && (SEW ≤b 64))
  let valid_rm := (not ((rm_3b == 0b101#3) || ((rm_3b == 0b110#3) || (rm_3b == 0b111#3))))
  (valid_sew && valid_rm)

/-- Type quantifiers: SEW : Nat, List.elem SEW [8, 16, 32, 64] -/
def illegal_fp_normal (vd : vregidx) (vm : (BitVec 1)) (SEW : Nat) (rm_3b : (BitVec 3)) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (valid_rd_mask vd vm)) || (not
          (valid_fp_op SEW rm_3b)))))

/-- Type quantifiers: SEW : Nat, List.elem SEW [8, 16, 32, 64] -/
def illegal_fp_vd_masked (vd : vregidx) (SEW : Nat) (rm_3b : (BitVec 3)) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((vd == zvreg) || (not (valid_fp_op SEW rm_3b)))))

/-- Type quantifiers: SEW : Nat, List.elem SEW [8, 16, 32, 64] -/
def illegal_fp_vd_unmasked (SEW : Nat) (rm_3b : (BitVec 3)) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || (not (valid_fp_op SEW rm_3b))))

/-- Type quantifiers: LMUL_pow_new : Int, SEW_new : Nat, SEW : Nat, List.elem SEW [8, 16, 32, 64], 0
  ≤ SEW_new -/
def illegal_fp_variable_width (vd : vregidx) (vm : (BitVec 1)) (SEW : Nat) (rm_3b : (BitVec 3)) (SEW_new : Nat) (LMUL_pow_new : Int) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (valid_rd_mask vd vm)) || ((not
            (valid_fp_op SEW rm_3b)) || (not (valid_eew_emul SEW_new LMUL_pow_new))))))

/-- Type quantifiers: SEW : Nat, List.elem SEW [8, 16, 32, 64] -/
def illegal_fp_reduction (SEW : Nat) (rm_3b : (BitVec 3)) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || (not (valid_fp_op SEW rm_3b))))

/-- Type quantifiers: EEW : Nat, SEW : Nat, List.elem SEW [8, 16, 32, 64], 0 ≤ EEW -/
def illegal_fp_widening_reduction (SEW : Nat) (rm_3b : (BitVec 3)) (EEW : Nat) : SailM Bool := do
  (pure ((← (illegal_fp_reduction SEW rm_3b)) || (not ((EEW ≥b 8) && (EEW ≤b elen)))))

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def f_is_neg_inf (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_neg_inf_H xf)
  | 32 => (f_is_neg_inf_S xf)
  | _ => (f_is_neg_inf_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def f_is_neg_norm (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_neg_norm_H xf)
  | 32 => (f_is_neg_norm_S xf)
  | _ => (f_is_neg_norm_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def f_is_neg_subnorm (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_neg_subnorm_H xf)
  | 32 => (f_is_neg_subnorm_S xf)
  | _ => (f_is_neg_subnorm_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def f_is_neg_zero (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_neg_zero_H xf)
  | 32 => (f_is_neg_zero_S xf)
  | _ => (f_is_neg_zero_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def f_is_pos_zero (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_pos_zero_H xf)
  | 32 => (f_is_pos_zero_S xf)
  | _ => (f_is_pos_zero_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def f_is_pos_subnorm (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_pos_subnorm_H xf)
  | 32 => (f_is_pos_subnorm_S xf)
  | _ => (f_is_pos_subnorm_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def f_is_pos_norm (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_pos_norm_H xf)
  | 32 => (f_is_pos_norm_S xf)
  | _ => (f_is_pos_norm_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def f_is_pos_inf (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_pos_inf_H xf)
  | 32 => (f_is_pos_inf_S xf)
  | _ => (f_is_pos_inf_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def f_is_SNaN (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_SNaN_H xf)
  | 32 => (f_is_SNaN_S xf)
  | _ => (f_is_SNaN_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def f_is_QNaN (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_QNaN_H xf)
  | 32 => (f_is_QNaN_S xf)
  | _ => (f_is_QNaN_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def f_is_NaN (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_NaN_H xf)
  | 32 => (f_is_NaN_S xf)
  | _ => (f_is_NaN_D xf)

/-- Type quantifiers: SEW : Nat, SEW ≥ 0, List.elem SEW [16, 32, 64] -/
def get_scalar_fp (rs1 : fregidx) (SEW : Nat) : SailM (BitVec SEW) := do
  «assert» (flen ≥b SEW) "invalid vector floating-point type width: FLEN < SEW"
  match SEW with
  | 16 => (rF_H rs1)
  | 32 => (rF_S rs1)
  | _ => (rF_D rs1)

def get_fp_rounding_mode (_ : Unit) : SailM rounding_mode := do
  (encdec_rounding_mode_backwards (_get_Fcsr_FRM (← readReg fcsr)))

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def negate_fp (xf : (BitVec k_m)) : (BitVec k_m) :=
  match (Sail.BitVec.length xf) with
  | 16 => (negate_H xf)
  | 32 => (negate_S xf)
  | _ => (negate_D xf)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_add (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) : (bits_fflags × (BitVec k_m)) :=
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Add rm_3b op1 op2)
    | 32 => (riscv_f32Add rm_3b op1 op2)
    | _ => (riscv_f64Add rm_3b op1 op2)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_sub (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) : (bits_fflags × (BitVec k_m)) :=
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Sub rm_3b op1 op2)
    | 32 => (riscv_f32Sub rm_3b op1 op2)
    | _ => (riscv_f64Sub rm_3b op1 op2)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_min (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, op1_lt_op2) : (bits_fflags × Bool) :=
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Lt_quiet op1 op2)
    | 32 => (riscv_f32Lt_quiet op1 op2)
    | _ => (riscv_f64Lt_quiet op1 op2)
  let result_val :=
    if (((f_is_NaN op1) && (f_is_NaN op2)) : Bool)
    then (canonical_NaN (n := (Sail.BitVec.length op2)))
    else
      (if ((f_is_NaN op1) : Bool)
      then op2
      else
        (if ((f_is_NaN op2) : Bool)
        then op1
        else
          (if (((f_is_neg_zero op1) && (f_is_pos_zero op2)) : Bool)
          then op1
          else
            (if (((f_is_neg_zero op2) && (f_is_pos_zero op1)) : Bool)
            then op2
            else
              (if (op1_lt_op2 : Bool)
              then op1
              else op2)))))
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_max (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, op1_lt_op2) : (bits_fflags × Bool) :=
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Lt_quiet op1 op2)
    | 32 => (riscv_f32Lt_quiet op1 op2)
    | _ => (riscv_f64Lt_quiet op1 op2)
  let result_val :=
    if (((f_is_NaN op1) && (f_is_NaN op2)) : Bool)
    then (canonical_NaN (n := (Sail.BitVec.length op2)))
    else
      (if ((f_is_NaN op1) : Bool)
      then op2
      else
        (if ((f_is_NaN op2) : Bool)
        then op1
        else
          (if (((f_is_neg_zero op1) && (f_is_pos_zero op2)) : Bool)
          then op2
          else
            (if (((f_is_neg_zero op2) && (f_is_pos_zero op1)) : Bool)
            then op1
            else
              (if (op1_lt_op2 : Bool)
              then op2
              else op1)))))
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_eq (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, result_val) : (bits_fflags × Bool) :=
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Eq op1 op2)
    | 32 => (riscv_f32Eq op1 op2)
    | _ => (riscv_f64Eq op1 op2)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_gt (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, temp_val) : (bits_fflags × Bool) :=
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Le op1 op2)
    | 32 => (riscv_f32Le op1 op2)
    | _ => (riscv_f64Le op1 op2)
  let result_val :=
    if ((fflags == 0b10000#5) : Bool)
    then false
    else (not temp_val)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_ge (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, temp_val) : (bits_fflags × Bool) :=
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Lt op1 op2)
    | 32 => (riscv_f32Lt op1 op2)
    | _ => (riscv_f64Lt op1 op2)
  let result_val :=
    if ((fflags == 0b10000#5) : Bool)
    then false
    else (not temp_val)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_lt (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, result_val) : (bits_fflags × Bool) :=
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Lt op1 op2)
    | 32 => (riscv_f32Lt op1 op2)
    | _ => (riscv_f64Lt op1 op2)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_le (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, result_val) : (bits_fflags × Bool) :=
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Le op1 op2)
    | 32 => (riscv_f32Le op1 op2)
    | _ => (riscv_f64Le op1 op2)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_mul (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) : (bits_fflags × (BitVec k_m)) :=
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Mul rm_3b op1 op2)
    | 32 => (riscv_f32Mul rm_3b op1 op2)
    | _ => (riscv_f64Mul rm_3b op1 op2)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_div (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) : (bits_fflags × (BitVec k_m)) :=
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Div rm_3b op1 op2)
    | 32 => (riscv_f32Div rm_3b op1 op2)
    | _ => (riscv_f64Div rm_3b op1 op2)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_muladd (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) (opadd : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) : (bits_fflags × (BitVec k_m)) :=
    match (Sail.BitVec.length opadd) with
    | 16 => (riscv_f16MulAdd rm_3b op1 op2 opadd)
    | 32 => (riscv_f32MulAdd rm_3b op1 op2 opadd)
    | _ => (riscv_f64MulAdd rm_3b op1 op2 opadd)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_nmuladd (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) (opadd : (BitVec k_m)) : SailM (BitVec k_m) := do
  let op1 := (negate_fp op1)
  let (fflags, result_val) : (bits_fflags × (BitVec k_m)) :=
    match (Sail.BitVec.length opadd) with
    | 16 => (riscv_f16MulAdd rm_3b op1 op2 opadd)
    | 32 => (riscv_f32MulAdd rm_3b op1 op2 opadd)
    | _ => (riscv_f64MulAdd rm_3b op1 op2 opadd)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_mulsub (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) (opsub : (BitVec k_m)) : SailM (BitVec k_m) := do
  let opsub := (negate_fp opsub)
  let (fflags, result_val) : (bits_fflags × (BitVec k_m)) :=
    match (Sail.BitVec.length opsub) with
    | 16 => (riscv_f16MulAdd rm_3b op1 op2 opsub)
    | 32 => (riscv_f32MulAdd rm_3b op1 op2 opsub)
    | _ => (riscv_f64MulAdd rm_3b op1 op2 opsub)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def fp_nmulsub (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) (opsub : (BitVec k_m)) : SailM (BitVec k_m) := do
  let opsub := (negate_fp opsub)
  let op1 := (negate_fp op1)
  let (fflags, result_val) : (bits_fflags × (BitVec k_m)) :=
    match (Sail.BitVec.length opsub) with
    | 16 => (riscv_f16MulAdd rm_3b op1 op2 opsub)
    | 32 => (riscv_f32MulAdd rm_3b op1 op2 opsub)
    | _ => (riscv_f64MulAdd rm_3b op1 op2 opsub)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32] -/
def fp_widen (nval : (BitVec k_m)) : SailM (BitVec (k_m * 2)) := do
  let rm_3b ← do (pure (_get_Fcsr_FRM (← readReg fcsr)))
  let (fflags, wval) : (bits_fflags × (BitVec (k_m * 2))) :=
    match (Sail.BitVec.length nval) with
    | 16 => (riscv_f16ToF32 rm_3b nval)
    | _ => (riscv_f32ToF64 rm_3b nval)
  (accrue_fflags fflags)
  (pure wval)

def riscv_f16ToI16 (rm : (BitVec 3)) (v : (BitVec 16)) : ((BitVec 5) × (BitVec 16)) :=
  let (flag, sig32) := (riscv_f16ToI32 rm v)
  if (((BitVec.toInt sig32) >b (BitVec.toInt (0#1 +++ (ones (n := 15))))) : Bool)
  then ((nvFlag ()), (0#1 +++ (ones (n := 15))))
  else
    (if (((BitVec.toInt sig32) <b (BitVec.toInt (1#1 +++ (zeros (n := 15))))) : Bool)
    then ((nvFlag ()), (1#1 +++ (zeros (n := 15))))
    else (flag, (Sail.BitVec.extractLsb sig32 15 0)))

def riscv_f16ToI8 (rm : (BitVec 3)) (v : (BitVec 16)) : ((BitVec 5) × (BitVec 8)) :=
  let (flag, sig32) := (riscv_f16ToI32 rm v)
  if (((BitVec.toInt sig32) >b (BitVec.toInt (0#1 +++ (ones (n := 7))))) : Bool)
  then ((nvFlag ()), (0#1 +++ (ones (n := 7))))
  else
    (if (((BitVec.toInt sig32) <b (BitVec.toInt (1#1 +++ (zeros (n := 7))))) : Bool)
    then ((nvFlag ()), (1#1 +++ (zeros (n := 7))))
    else (flag, (Sail.BitVec.extractLsb sig32 7 0)))

def riscv_f32ToI16 (rm : (BitVec 3)) (v : (BitVec 32)) : ((BitVec 5) × (BitVec 16)) :=
  let (flag, sig32) := (riscv_f32ToI32 rm v)
  if (((BitVec.toInt sig32) >b (BitVec.toInt (0#1 +++ (ones (n := 15))))) : Bool)
  then ((nvFlag ()), (0#1 +++ (ones (n := 15))))
  else
    (if (((BitVec.toInt sig32) <b (BitVec.toInt (1#1 +++ (zeros (n := 15))))) : Bool)
    then ((nvFlag ()), (1#1 +++ (zeros (n := 15))))
    else (flag, (Sail.BitVec.extractLsb sig32 15 0)))

def riscv_f16ToUi16 (rm : (BitVec 3)) (v : (BitVec 16)) : ((BitVec 5) × (BitVec 16)) :=
  let (flag, sig32) := (riscv_f16ToUi32 rm v)
  if (((BitVec.toNatInt sig32) >b (BitVec.toNatInt (ones (n := 16)))) : Bool)
  then ((nvFlag ()), (ones (n := 16)))
  else (flag, (Sail.BitVec.extractLsb sig32 15 0))

def riscv_f16ToUi8 (rm : (BitVec 3)) (v : (BitVec 16)) : ((BitVec 5) × (BitVec 8)) :=
  let (flag, sig32) := (riscv_f16ToUi32 rm v)
  if (((BitVec.toNatInt sig32) >b (BitVec.toNatInt (ones (n := 8)))) : Bool)
  then ((nvFlag ()), (ones (n := 8)))
  else (flag, (Sail.BitVec.extractLsb sig32 7 0))

def riscv_f32ToUi16 (rm : (BitVec 3)) (v : (BitVec 32)) : ((BitVec 5) × (BitVec 16)) :=
  let (flag, sig32) := (riscv_f32ToUi32 rm v)
  if (((BitVec.toNatInt sig32) >b (BitVec.toNatInt (ones (n := 16)))) : Bool)
  then ((nvFlag ()), (ones (n := 16)))
  else (flag, (Sail.BitVec.extractLsb sig32 15 0))

/-- Type quantifiers: k_ex1822369_ : Bool, k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def rsqrt7 (v : (BitVec k_m)) (sub : Bool) : SailM (BitVec 64) := do
  let (sig, exp, sign, e, s) : ((BitVec 64) × (BitVec 64) × (BitVec 1) × Int × Int) :=
    match (Sail.BitVec.length v) with
    | 16 =>
      ((zero_extend (m := 64) (Sail.BitVec.extractLsb v 9 0)), (zero_extend (m := 64)
        (Sail.BitVec.extractLsb v 14 10)), (BitVec.join1 [(BitVec.access v 15)]), 5, 10)
    | 32 =>
      ((zero_extend (m := 64) (Sail.BitVec.extractLsb v 22 0)), (zero_extend (m := 64)
        (Sail.BitVec.extractLsb v 30 23)), (BitVec.join1 [(BitVec.access v 31)]), 8, 23)
    | _ =>
      ((zero_extend (m := 64) (Sail.BitVec.extractLsb v 51 0)), (zero_extend (m := 64)
        (Sail.BitVec.extractLsb v 62 52)), (BitVec.join1 [(BitVec.access v 63)]), 11, 52)
  let table : (Vector Int 128) :=
    #v[53, 54, 55, 56, 56, 57, 58, 59, 59, 60, 61, 62, 63, 63, 64, 65, 66, 67, 68, 69, 70, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 90, 91, 92, 93, 95, 96, 97, 99, 100, 102, 103, 105, 106, 108, 109, 111, 113, 114, 116, 118, 119, 121, 123, 125, 127, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 6, 6, 7, 7, 8, 9, 9, 10, 10, 11, 12, 12, 13, 14, 14, 15, 16, 16, 17, 18, 19, 19, 20, 21, 22, 23, 23, 24, 25, 26, 27, 28, 29, 30, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 50, 51, 52]
  let (normalized_exp, normalized_sig) ← do
    if (sub : Bool)
    then
      (do
        let nr_leadingzeros := (BitVec.countLeadingZeros (Sail.BitVec.extractLsb sig (s -i 1) 0))
        «assert» (nr_leadingzeros ≥b 0) "extensions/V/vext_fp_utils_insts.sail:445.35-445.36"
        (pure ((to_bits_unsafe (l := 64) (0 -i nr_leadingzeros)), (zero_extend (m := 64)
            ((Sail.BitVec.extractLsb sig (s -i 1) 0) <<< (1 +i nr_leadingzeros))))))
    else (pure (exp, sig))
  let idx : Nat :=
    match (Sail.BitVec.length v) with
    | 16 =>
      (BitVec.toNatInt
        ((BitVec.join1 [(BitVec.access normalized_exp 0)]) +++ (Sail.BitVec.extractLsb
            normalized_sig 9 4)))
    | 32 =>
      (BitVec.toNatInt
        ((BitVec.join1 [(BitVec.access normalized_exp 0)]) +++ (Sail.BitVec.extractLsb
            normalized_sig 22 17)))
    | _ =>
      (BitVec.toNatInt
        ((BitVec.join1 [(BitVec.access normalized_exp 0)]) +++ (Sail.BitVec.extractLsb
            normalized_sig 51 46)))
  «assert» ((idx ≥b 0) && (idx <b 128)) "extensions/V/vext_fp_utils_insts.sail:456.29-456.30"
  let out_sig := ((to_bits_unsafe (l := s) (GetElem?.getElem! table (127 -i idx))) <<< (s -i 7))
  let out_exp :=
    (to_bits_unsafe (l := e)
      (Int.tdiv (((3 *i ((2 ^i (e -i 1)) -i 1)) -i 1) -i (BitVec.toInt normalized_exp)) 2))
  (pure (zero_extend (m := 64) (sign +++ (out_exp +++ out_sig))))

def riscv_f16Rsqrte7 (_rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  match (← (float_classify v)) with
  | .float_class_negative_inf => (pure ((nvFlag ()), 0x7E00#16))
  | .float_class_negative_normal => (pure ((nvFlag ()), 0x7E00#16))
  | .float_class_negative_subnormal => (pure ((nvFlag ()), 0x7E00#16))
  | .float_class_snan => (pure ((nvFlag ()), 0x7E00#16))
  | .float_class_qnan => (pure ((zeros (n := 5)), 0x7E00#16))
  | .float_class_negative_zero => (pure ((dzFlag ()), 0xFC00#16))
  | .float_class_positive_zero => (pure ((dzFlag ()), 0x7C00#16))
  | .float_class_positive_inf => (pure ((zeros (n := 5)), 0x0000#16))
  | .float_class_positive_subnormal =>
    (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb (← (rsqrt7 v true)) 15 0)))
  | .float_class_positive_normal =>
    (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb (← (rsqrt7 v false)) 15 0)))

def riscv_f32Rsqrte7 (_rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  match (← (float_classify v)) with
  | .float_class_negative_inf => (pure ((nvFlag ()), 0x7FC00000#32))
  | .float_class_negative_normal => (pure ((nvFlag ()), 0x7FC00000#32))
  | .float_class_negative_subnormal => (pure ((nvFlag ()), 0x7FC00000#32))
  | .float_class_snan => (pure ((nvFlag ()), 0x7FC00000#32))
  | .float_class_qnan => (pure ((zeros (n := 5)), 0x7FC00000#32))
  | .float_class_negative_zero => (pure ((dzFlag ()), 0xFF800000#32))
  | .float_class_positive_zero => (pure ((dzFlag ()), 0x7F800000#32))
  | .float_class_positive_inf => (pure ((zeros (n := 5)), 0x00000000#32))
  | .float_class_positive_subnormal =>
    (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb (← (rsqrt7 v true)) 31 0)))
  | .float_class_positive_normal =>
    (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb (← (rsqrt7 v false)) 31 0)))

def riscv_f64Rsqrte7 (_rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  match (← (float_classify v)) with
  | .float_class_negative_inf => (pure ((nvFlag ()), 0x7FF8000000000000#64))
  | .float_class_negative_normal => (pure ((nvFlag ()), 0x7FF8000000000000#64))
  | .float_class_negative_subnormal => (pure ((nvFlag ()), 0x7FF8000000000000#64))
  | .float_class_snan => (pure ((nvFlag ()), 0x7FF8000000000000#64))
  | .float_class_qnan => (pure ((zeros (n := 5)), 0x7FF8000000000000#64))
  | .float_class_negative_zero => (pure ((dzFlag ()), 0xFFF0000000000000#64))
  | .float_class_positive_zero => (pure ((dzFlag ()), 0x7FF0000000000000#64))
  | .float_class_positive_inf => (pure ((zeros (n := 5)), (zeros (n := 64))))
  | .float_class_positive_subnormal =>
    (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb (← (rsqrt7 v true)) 63 0)))
  | .float_class_positive_normal =>
    (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb (← (rsqrt7 v false)) 63 0)))

/-- Type quantifiers: k_ex1822370_ : Bool, k_m : Nat, k_m ≥ 0, List.elem k_m [16, 32, 64] -/
def recip7 (v : (BitVec k_m)) (rm_3b : (BitVec 3)) (sub : Bool) : SailM (Bool × (BitVec 64)) := do
  let (sig, exp, sign, e, s) : ((BitVec 64) × (BitVec 64) × (BitVec 1) × Int × Int) :=
    match (Sail.BitVec.length v) with
    | 16 =>
      ((zero_extend (m := 64) (Sail.BitVec.extractLsb v 9 0)), (zero_extend (m := 64)
        (Sail.BitVec.extractLsb v 14 10)), (BitVec.join1 [(BitVec.access v 15)]), 5, 10)
    | 32 =>
      ((zero_extend (m := 64) (Sail.BitVec.extractLsb v 22 0)), (zero_extend (m := 64)
        (Sail.BitVec.extractLsb v 30 23)), (BitVec.join1 [(BitVec.access v 31)]), 8, 23)
    | _ =>
      ((zero_extend (m := 64) (Sail.BitVec.extractLsb v 51 0)), (zero_extend (m := 64)
        (Sail.BitVec.extractLsb v 62 52)), (BitVec.join1 [(BitVec.access v 63)]), 11, 52)
  let table : (Vector Int 128) :=
    #v[0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 7, 8, 8, 9, 9, 10, 11, 11, 12, 12, 13, 14, 14, 15, 15, 16, 17, 17, 18, 19, 19, 20, 21, 21, 22, 23, 23, 24, 25, 25, 26, 27, 28, 28, 29, 30, 31, 31, 32, 33, 34, 35, 35, 36, 37, 38, 39, 40, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 69, 70, 71, 72, 74, 75, 76, 77, 79, 80, 81, 83, 84, 85, 87, 88, 90, 91, 93, 94, 96, 97, 99, 100, 102, 104, 105, 107, 109, 110, 112, 114, 116, 117, 119, 121, 123, 125, 127]
  let nr_leadingzeros := (BitVec.countLeadingZeros (Sail.BitVec.extractLsb sig (s -i 1) 0))
  «assert» (nr_leadingzeros ≥b 0) "extensions/V/vext_fp_utils_insts.sail:534.29-534.30"
  let (normalized_exp, normalized_sig) :=
    if (sub : Bool)
    then
      ((to_bits_unsafe (l := 64) (0 -i nr_leadingzeros)), (zero_extend (m := 64)
        ((Sail.BitVec.extractLsb sig (s -i 1) 0) <<< (1 +i nr_leadingzeros))))
    else (exp, sig)
  let idx : Nat :=
    match (Sail.BitVec.length v) with
    | 16 => (BitVec.toNatInt (Sail.BitVec.extractLsb normalized_sig 9 3))
    | 32 => (BitVec.toNatInt (Sail.BitVec.extractLsb normalized_sig 22 16))
    | _ => (BitVec.toNatInt (Sail.BitVec.extractLsb normalized_sig 51 45))
  «assert» ((idx ≥b 0) && (idx <b 128)) "extensions/V/vext_fp_utils_insts.sail:547.29-547.30"
  let mid_exp :=
    (to_bits_unsafe (l := e) (((2 *i ((2 ^i (e -i 1)) -i 1)) -i 1) -i (BitVec.toInt normalized_exp)))
  let mid_sig := ((to_bits_unsafe (l := s) (GetElem?.getElem! table (127 -i idx))) <<< (s -i 7))
  let (out_exp, out_sig) :=
    if ((mid_exp == (zeros (n := e))) : Bool)
    then (mid_exp, ((mid_sig >>> 1) ||| (1#1 +++ (zeros (n := (s -i 1))))))
    else
      (if ((mid_exp == (ones (n := e))) : Bool)
      then ((zeros (n := e)), ((mid_sig >>> 2) ||| (0b01#2 +++ (zeros (n := (s -i 2))))))
      else (mid_exp, mid_sig))
  if ((sub && (nr_leadingzeros >b 1)) : Bool)
  then
    (if (((rm_3b == 0b001#3) || (((rm_3b == 0b010#3) && (sign == 0#1)) || ((rm_3b == 0b011#3) && (sign == 1#1)))) : Bool)
    then
      (pure (true, (zero_extend (m := 64)
          (sign +++ ((ones (n := (e -i 1))) +++ (0#1 +++ (ones (n := s))))))))
    else (pure (true, (zero_extend (m := 64) (sign +++ ((ones (n := e)) +++ (zeros (n := s))))))))
  else (pure (false, (zero_extend (m := 64) (sign +++ (out_exp +++ out_sig)))))

def riscv_f16Recip7 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (round_abnormal_true, res_true) ← do (recip7 v rm true)
  let (round_abnormal_false, res_false) ← do (recip7 v rm false)
  match (← (float_classify v)) with
  | .float_class_negative_inf => (pure ((zeros (n := 5)), 0x8000#16))
  | .float_class_positive_inf => (pure ((zeros (n := 5)), 0x0000#16))
  | .float_class_negative_zero => (pure ((dzFlag ()), 0xFC00#16))
  | .float_class_positive_zero => (pure ((dzFlag ()), 0x7C00#16))
  | .float_class_snan => (pure ((nvFlag ()), 0x7E00#16))
  | .float_class_qnan => (pure ((zeros (n := 5)), 0x7E00#16))
  | .float_class_negative_subnormal =>
    (if (round_abnormal_true : Bool)
    then (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_true 15 0)))
    else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_true 15 0))))
  | .float_class_positive_subnormal =>
    (if (round_abnormal_true : Bool)
    then (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_true 15 0)))
    else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_true 15 0))))
  | _ =>
    (if (round_abnormal_false : Bool)
    then (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_false 15 0)))
    else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_false 15 0))))

def riscv_f32Recip7 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let (round_abnormal_true, res_true) ← do (recip7 v rm true)
  let (round_abnormal_false, res_false) ← do (recip7 v rm false)
  match (← (float_classify v)) with
  | .float_class_negative_inf => (pure ((zeros (n := 5)), 0x80000000#32))
  | .float_class_positive_inf => (pure ((zeros (n := 5)), 0x00000000#32))
  | .float_class_negative_zero => (pure ((dzFlag ()), 0xFF800000#32))
  | .float_class_positive_zero => (pure ((dzFlag ()), 0x7F800000#32))
  | .float_class_snan => (pure ((nvFlag ()), 0x7FC00000#32))
  | .float_class_qnan => (pure ((zeros (n := 5)), 0x7FC00000#32))
  | .float_class_negative_subnormal =>
    (if (round_abnormal_true : Bool)
    then (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_true 31 0)))
    else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_true 31 0))))
  | .float_class_positive_subnormal =>
    (if (round_abnormal_true : Bool)
    then (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_true 31 0)))
    else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_true 31 0))))
  | _ =>
    (if (round_abnormal_false : Bool)
    then (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_false 31 0)))
    else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_false 31 0))))

def riscv_f64Recip7 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let (round_abnormal_true, res_true) ← do (recip7 v rm true)
  let (round_abnormal_false, res_false) ← do (recip7 v rm false)
  match (← (float_classify v)) with
  | .float_class_negative_inf => (pure ((zeros (n := 5)), 0x8000000000000000#64))
  | .float_class_positive_inf => (pure ((zeros (n := 5)), 0x0000000000000000#64))
  | .float_class_negative_zero => (pure ((dzFlag ()), 0xFFF0000000000000#64))
  | .float_class_positive_zero => (pure ((dzFlag ()), 0x7FF0000000000000#64))
  | .float_class_snan => (pure ((nvFlag ()), 0x7FF8000000000000#64))
  | .float_class_qnan => (pure ((zeros (n := 5)), 0x7FF8000000000000#64))
  | .float_class_negative_subnormal =>
    (if (round_abnormal_true : Bool)
    then (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_true 63 0)))
    else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_true 63 0))))
  | .float_class_positive_subnormal =>
    (if (round_abnormal_true : Bool)
    then (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_true 63 0)))
    else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_true 63 0))))
  | _ =>
    (if (round_abnormal_false : Bool)
    then (pure (((nxFlag ()) ||| (ofFlag ())), (Sail.BitVec.extractLsb res_false 63 0)))
    else (pure ((zeros (n := 5)), (Sail.BitVec.extractLsb res_false 63 0))))

