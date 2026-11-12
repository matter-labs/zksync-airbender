import SailRV32.Prelude

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

def zero_freg : fregtype := (zeros (n := (8 *i 8)))

def FRegStr (r : (BitVec (if ( true  : Bool) then 8 else 4 * 8))) : String :=
  (BitVec.toFormatted r)

def fregval_from_freg (r : (BitVec (if ( true  : Bool) then 8 else 4 * 8))) : (BitVec (if ( true  : Bool) then 8 else 4 * 8)) :=
  r

def fregval_into_freg (v : (BitVec (if ( true  : Bool) then 8 else 4 * 8))) : (BitVec (if ( true  : Bool) then 8 else 4 * 8)) :=
  v

def undefined_f_madd_op_H (_ : Unit) : SailM f_madd_op_H := do
  (internal_pick [FMADD_H, FMSUB_H, FNMSUB_H, FNMADD_H])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def f_madd_op_H_of_num (arg_ : Nat) : f_madd_op_H :=
  match arg_ with
  | 0 => FMADD_H
  | 1 => FMSUB_H
  | 2 => FNMSUB_H
  | _ => FNMADD_H

def num_of_f_madd_op_H (arg_ : f_madd_op_H) : Int :=
  match arg_ with
  | .FMADD_H => 0
  | .FMSUB_H => 1
  | .FNMSUB_H => 2
  | .FNMADD_H => 3

def undefined_f_bin_rm_op_H (_ : Unit) : SailM f_bin_rm_op_H := do
  (internal_pick [FADD_H, FSUB_H, FMUL_H, FDIV_H])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def f_bin_rm_op_H_of_num (arg_ : Nat) : f_bin_rm_op_H :=
  match arg_ with
  | 0 => FADD_H
  | 1 => FSUB_H
  | 2 => FMUL_H
  | _ => FDIV_H

def num_of_f_bin_rm_op_H (arg_ : f_bin_rm_op_H) : Int :=
  match arg_ with
  | .FADD_H => 0
  | .FSUB_H => 1
  | .FMUL_H => 2
  | .FDIV_H => 3

def undefined_f_un_rm_ff_op_H (_ : Unit) : SailM f_un_rm_ff_op_H := do
  (internal_pick [FSQRT_H, FCVT_H_S, FCVT_H_D, FCVT_S_H, FCVT_D_H])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def f_un_rm_ff_op_H_of_num (arg_ : Nat) : f_un_rm_ff_op_H :=
  match arg_ with
  | 0 => FSQRT_H
  | 1 => FCVT_H_S
  | 2 => FCVT_H_D
  | 3 => FCVT_S_H
  | _ => FCVT_D_H

def num_of_f_un_rm_ff_op_H (arg_ : f_un_rm_ff_op_H) : Int :=
  match arg_ with
  | .FSQRT_H => 0
  | .FCVT_H_S => 1
  | .FCVT_H_D => 2
  | .FCVT_S_H => 3
  | .FCVT_D_H => 4

def undefined_f_un_rm_fx_op_H (_ : Unit) : SailM f_un_rm_fx_op_H := do
  (internal_pick [FCVT_W_H, FCVT_WU_H, FCVT_L_H, FCVT_LU_H])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def f_un_rm_fx_op_H_of_num (arg_ : Nat) : f_un_rm_fx_op_H :=
  match arg_ with
  | 0 => FCVT_W_H
  | 1 => FCVT_WU_H
  | 2 => FCVT_L_H
  | _ => FCVT_LU_H

def num_of_f_un_rm_fx_op_H (arg_ : f_un_rm_fx_op_H) : Int :=
  match arg_ with
  | .FCVT_W_H => 0
  | .FCVT_WU_H => 1
  | .FCVT_L_H => 2
  | .FCVT_LU_H => 3

def undefined_f_un_rm_xf_op_H (_ : Unit) : SailM f_un_rm_xf_op_H := do
  (internal_pick [FCVT_H_W, FCVT_H_WU, FCVT_H_L, FCVT_H_LU])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def f_un_rm_xf_op_H_of_num (arg_ : Nat) : f_un_rm_xf_op_H :=
  match arg_ with
  | 0 => FCVT_H_W
  | 1 => FCVT_H_WU
  | 2 => FCVT_H_L
  | _ => FCVT_H_LU

def num_of_f_un_rm_xf_op_H (arg_ : f_un_rm_xf_op_H) : Int :=
  match arg_ with
  | .FCVT_H_W => 0
  | .FCVT_H_WU => 1
  | .FCVT_H_L => 2
  | .FCVT_H_LU => 3

def undefined_f_un_x_op_H (_ : Unit) : SailM f_un_x_op_H := do
  (internal_pick [FCLASS_H, FMV_X_H])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def f_un_x_op_H_of_num (arg_ : Nat) : f_un_x_op_H :=
  match arg_ with
  | 0 => FCLASS_H
  | _ => FMV_X_H

def num_of_f_un_x_op_H (arg_ : f_un_x_op_H) : Int :=
  match arg_ with
  | .FCLASS_H => 0
  | .FMV_X_H => 1

def undefined_f_un_f_op_H (_ : Unit) : SailM f_un_f_op_H := do
  (internal_pick [FMV_H_X])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 0 -/
def f_un_f_op_H_of_num (arg_ : Nat) : f_un_f_op_H :=
  match arg_ with
  | _ => FMV_H_X

def num_of_f_un_f_op_H (arg_ : f_un_f_op_H) : Int :=
  match arg_ with
  | .FMV_H_X => 0

def undefined_f_bin_f_op_H (_ : Unit) : SailM f_bin_f_op_H := do
  (internal_pick [FSGNJ_H, FSGNJN_H, FSGNJX_H, FMIN_H, FMAX_H])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def f_bin_f_op_H_of_num (arg_ : Nat) : f_bin_f_op_H :=
  match arg_ with
  | 0 => FSGNJ_H
  | 1 => FSGNJN_H
  | 2 => FSGNJX_H
  | 3 => FMIN_H
  | _ => FMAX_H

def num_of_f_bin_f_op_H (arg_ : f_bin_f_op_H) : Int :=
  match arg_ with
  | .FSGNJ_H => 0
  | .FSGNJN_H => 1
  | .FSGNJX_H => 2
  | .FMIN_H => 3
  | .FMAX_H => 4

def undefined_f_bin_x_op_H (_ : Unit) : SailM f_bin_x_op_H := do
  (internal_pick [FEQ_H, FLT_H, FLE_H])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def f_bin_x_op_H_of_num (arg_ : Nat) : f_bin_x_op_H :=
  match arg_ with
  | 0 => FEQ_H
  | 1 => FLT_H
  | _ => FLE_H

def num_of_f_bin_x_op_H (arg_ : f_bin_x_op_H) : Int :=
  match arg_ with
  | .FEQ_H => 0
  | .FLT_H => 1
  | .FLE_H => 2

def undefined_rounding_mode (_ : Unit) : SailM rounding_mode := do
  (internal_pick [RM_RNE, RM_RTZ, RM_RDN, RM_RUP, RM_RMM, RM_DYN])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def rounding_mode_of_num (arg_ : Nat) : rounding_mode :=
  match arg_ with
  | 0 => RM_RNE
  | 1 => RM_RTZ
  | 2 => RM_RDN
  | 3 => RM_RUP
  | 4 => RM_RMM
  | _ => RM_DYN

def num_of_rounding_mode (arg_ : rounding_mode) : Int :=
  match arg_ with
  | .RM_RNE => 0
  | .RM_RTZ => 1
  | .RM_RDN => 2
  | .RM_RUP => 3
  | .RM_RMM => 4
  | .RM_DYN => 5

def undefined_f_madd_op_S (_ : Unit) : SailM f_madd_op_S := do
  (internal_pick [FMADD_S, FMSUB_S, FNMSUB_S, FNMADD_S])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def f_madd_op_S_of_num (arg_ : Nat) : f_madd_op_S :=
  match arg_ with
  | 0 => FMADD_S
  | 1 => FMSUB_S
  | 2 => FNMSUB_S
  | _ => FNMADD_S

def num_of_f_madd_op_S (arg_ : f_madd_op_S) : Int :=
  match arg_ with
  | .FMADD_S => 0
  | .FMSUB_S => 1
  | .FNMSUB_S => 2
  | .FNMADD_S => 3

def undefined_f_bin_rm_op_S (_ : Unit) : SailM f_bin_rm_op_S := do
  (internal_pick [FADD_S, FSUB_S, FMUL_S, FDIV_S])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def f_bin_rm_op_S_of_num (arg_ : Nat) : f_bin_rm_op_S :=
  match arg_ with
  | 0 => FADD_S
  | 1 => FSUB_S
  | 2 => FMUL_S
  | _ => FDIV_S

def num_of_f_bin_rm_op_S (arg_ : f_bin_rm_op_S) : Int :=
  match arg_ with
  | .FADD_S => 0
  | .FSUB_S => 1
  | .FMUL_S => 2
  | .FDIV_S => 3

def undefined_f_un_rm_ff_op_S (_ : Unit) : SailM f_un_rm_ff_op_S := do
  (internal_pick [FSQRT_S])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 0 -/
def f_un_rm_ff_op_S_of_num (arg_ : Nat) : f_un_rm_ff_op_S :=
  match arg_ with
  | _ => FSQRT_S

def num_of_f_un_rm_ff_op_S (arg_ : f_un_rm_ff_op_S) : Int :=
  match arg_ with
  | .FSQRT_S => 0

def undefined_f_un_rm_fx_op_S (_ : Unit) : SailM f_un_rm_fx_op_S := do
  (internal_pick [FCVT_W_S, FCVT_WU_S, FCVT_L_S, FCVT_LU_S])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def f_un_rm_fx_op_S_of_num (arg_ : Nat) : f_un_rm_fx_op_S :=
  match arg_ with
  | 0 => FCVT_W_S
  | 1 => FCVT_WU_S
  | 2 => FCVT_L_S
  | _ => FCVT_LU_S

def num_of_f_un_rm_fx_op_S (arg_ : f_un_rm_fx_op_S) : Int :=
  match arg_ with
  | .FCVT_W_S => 0
  | .FCVT_WU_S => 1
  | .FCVT_L_S => 2
  | .FCVT_LU_S => 3

def undefined_f_un_rm_xf_op_S (_ : Unit) : SailM f_un_rm_xf_op_S := do
  (internal_pick [FCVT_S_W, FCVT_S_WU, FCVT_S_L, FCVT_S_LU])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def f_un_rm_xf_op_S_of_num (arg_ : Nat) : f_un_rm_xf_op_S :=
  match arg_ with
  | 0 => FCVT_S_W
  | 1 => FCVT_S_WU
  | 2 => FCVT_S_L
  | _ => FCVT_S_LU

def num_of_f_un_rm_xf_op_S (arg_ : f_un_rm_xf_op_S) : Int :=
  match arg_ with
  | .FCVT_S_W => 0
  | .FCVT_S_WU => 1
  | .FCVT_S_L => 2
  | .FCVT_S_LU => 3

def undefined_f_un_op_f_S (_ : Unit) : SailM f_un_op_f_S := do
  (internal_pick [FMV_W_X])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 0 -/
def f_un_op_f_S_of_num (arg_ : Nat) : f_un_op_f_S :=
  match arg_ with
  | _ => FMV_W_X

def num_of_f_un_op_f_S (arg_ : f_un_op_f_S) : Int :=
  match arg_ with
  | .FMV_W_X => 0

def undefined_f_un_op_x_S (_ : Unit) : SailM f_un_op_x_S := do
  (internal_pick [FCLASS_S, FMV_X_W])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def f_un_op_x_S_of_num (arg_ : Nat) : f_un_op_x_S :=
  match arg_ with
  | 0 => FCLASS_S
  | _ => FMV_X_W

def num_of_f_un_op_x_S (arg_ : f_un_op_x_S) : Int :=
  match arg_ with
  | .FCLASS_S => 0
  | .FMV_X_W => 1

def undefined_f_bin_op_f_S (_ : Unit) : SailM f_bin_op_f_S := do
  (internal_pick [FSGNJ_S, FSGNJN_S, FSGNJX_S, FMIN_S, FMAX_S])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def f_bin_op_f_S_of_num (arg_ : Nat) : f_bin_op_f_S :=
  match arg_ with
  | 0 => FSGNJ_S
  | 1 => FSGNJN_S
  | 2 => FSGNJX_S
  | 3 => FMIN_S
  | _ => FMAX_S

def num_of_f_bin_op_f_S (arg_ : f_bin_op_f_S) : Int :=
  match arg_ with
  | .FSGNJ_S => 0
  | .FSGNJN_S => 1
  | .FSGNJX_S => 2
  | .FMIN_S => 3
  | .FMAX_S => 4

def undefined_f_bin_op_x_S (_ : Unit) : SailM f_bin_op_x_S := do
  (internal_pick [FEQ_S, FLT_S, FLE_S])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def f_bin_op_x_S_of_num (arg_ : Nat) : f_bin_op_x_S :=
  match arg_ with
  | 0 => FEQ_S
  | 1 => FLT_S
  | _ => FLE_S

def num_of_f_bin_op_x_S (arg_ : f_bin_op_x_S) : Int :=
  match arg_ with
  | .FEQ_S => 0
  | .FLT_S => 1
  | .FLE_S => 2

def undefined_f_madd_op_D (_ : Unit) : SailM f_madd_op_D := do
  (internal_pick [FMADD_D, FMSUB_D, FNMSUB_D, FNMADD_D])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def f_madd_op_D_of_num (arg_ : Nat) : f_madd_op_D :=
  match arg_ with
  | 0 => FMADD_D
  | 1 => FMSUB_D
  | 2 => FNMSUB_D
  | _ => FNMADD_D

def num_of_f_madd_op_D (arg_ : f_madd_op_D) : Int :=
  match arg_ with
  | .FMADD_D => 0
  | .FMSUB_D => 1
  | .FNMSUB_D => 2
  | .FNMADD_D => 3

def undefined_f_bin_rm_op_D (_ : Unit) : SailM f_bin_rm_op_D := do
  (internal_pick [FADD_D, FSUB_D, FMUL_D, FDIV_D])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def f_bin_rm_op_D_of_num (arg_ : Nat) : f_bin_rm_op_D :=
  match arg_ with
  | 0 => FADD_D
  | 1 => FSUB_D
  | 2 => FMUL_D
  | _ => FDIV_D

def num_of_f_bin_rm_op_D (arg_ : f_bin_rm_op_D) : Int :=
  match arg_ with
  | .FADD_D => 0
  | .FSUB_D => 1
  | .FMUL_D => 2
  | .FDIV_D => 3

def undefined_f_un_rm_ff_op_D (_ : Unit) : SailM f_un_rm_ff_op_D := do
  (internal_pick [FSQRT_D, FCVT_S_D, FCVT_D_S])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def f_un_rm_ff_op_D_of_num (arg_ : Nat) : f_un_rm_ff_op_D :=
  match arg_ with
  | 0 => FSQRT_D
  | 1 => FCVT_S_D
  | _ => FCVT_D_S

def num_of_f_un_rm_ff_op_D (arg_ : f_un_rm_ff_op_D) : Int :=
  match arg_ with
  | .FSQRT_D => 0
  | .FCVT_S_D => 1
  | .FCVT_D_S => 2

def undefined_f_un_rm_fx_op_D (_ : Unit) : SailM f_un_rm_fx_op_D := do
  (internal_pick [FCVT_W_D, FCVT_WU_D, FCVT_L_D, FCVT_LU_D])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def f_un_rm_fx_op_D_of_num (arg_ : Nat) : f_un_rm_fx_op_D :=
  match arg_ with
  | 0 => FCVT_W_D
  | 1 => FCVT_WU_D
  | 2 => FCVT_L_D
  | _ => FCVT_LU_D

def num_of_f_un_rm_fx_op_D (arg_ : f_un_rm_fx_op_D) : Int :=
  match arg_ with
  | .FCVT_W_D => 0
  | .FCVT_WU_D => 1
  | .FCVT_L_D => 2
  | .FCVT_LU_D => 3

def undefined_f_un_rm_xf_op_D (_ : Unit) : SailM f_un_rm_xf_op_D := do
  (internal_pick [FCVT_D_W, FCVT_D_WU, FCVT_D_L, FCVT_D_LU])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def f_un_rm_xf_op_D_of_num (arg_ : Nat) : f_un_rm_xf_op_D :=
  match arg_ with
  | 0 => FCVT_D_W
  | 1 => FCVT_D_WU
  | 2 => FCVT_D_L
  | _ => FCVT_D_LU

def num_of_f_un_rm_xf_op_D (arg_ : f_un_rm_xf_op_D) : Int :=
  match arg_ with
  | .FCVT_D_W => 0
  | .FCVT_D_WU => 1
  | .FCVT_D_L => 2
  | .FCVT_D_LU => 3

def undefined_f_bin_f_op_D (_ : Unit) : SailM f_bin_f_op_D := do
  (internal_pick [FSGNJ_D, FSGNJN_D, FSGNJX_D, FMIN_D, FMAX_D])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def f_bin_f_op_D_of_num (arg_ : Nat) : f_bin_f_op_D :=
  match arg_ with
  | 0 => FSGNJ_D
  | 1 => FSGNJN_D
  | 2 => FSGNJX_D
  | 3 => FMIN_D
  | _ => FMAX_D

def num_of_f_bin_f_op_D (arg_ : f_bin_f_op_D) : Int :=
  match arg_ with
  | .FSGNJ_D => 0
  | .FSGNJN_D => 1
  | .FSGNJX_D => 2
  | .FMIN_D => 3
  | .FMAX_D => 4

def undefined_f_bin_x_op_D (_ : Unit) : SailM f_bin_x_op_D := do
  (internal_pick [FEQ_D, FLT_D, FLE_D])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def f_bin_x_op_D_of_num (arg_ : Nat) : f_bin_x_op_D :=
  match arg_ with
  | 0 => FEQ_D
  | 1 => FLT_D
  | _ => FLE_D

def num_of_f_bin_x_op_D (arg_ : f_bin_x_op_D) : Int :=
  match arg_ with
  | .FEQ_D => 0
  | .FLT_D => 1
  | .FLE_D => 2

def undefined_f_un_x_op_D (_ : Unit) : SailM f_un_x_op_D := do
  (internal_pick [FCLASS_D, FMV_X_D])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def f_un_x_op_D_of_num (arg_ : Nat) : f_un_x_op_D :=
  match arg_ with
  | 0 => FCLASS_D
  | _ => FMV_X_D

def num_of_f_un_x_op_D (arg_ : f_un_x_op_D) : Int :=
  match arg_ with
  | .FCLASS_D => 0
  | .FMV_X_D => 1

def undefined_f_un_f_op_D (_ : Unit) : SailM f_un_f_op_D := do
  (internal_pick [FMV_D_X])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 0 -/
def f_un_f_op_D_of_num (arg_ : Nat) : f_un_f_op_D :=
  match arg_ with
  | _ => FMV_D_X

def num_of_f_un_f_op_D (arg_ : f_un_f_op_D) : Int :=
  match arg_ with
  | .FMV_D_X => 0

