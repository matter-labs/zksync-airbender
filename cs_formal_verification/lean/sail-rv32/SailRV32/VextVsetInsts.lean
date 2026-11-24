import SailRV32.Flow
import SailRV32.Prelude
import SailRV32.Errors
import SailRV32.Xlen
import SailRV32.Vlen
import SailRV32.PlatformConfig
import SailRV32.Callbacks
import SailRV32.Regs
import SailRV32.VextRegs
import SailRV32.InstsBegin
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

def sew_flag_forwards (arg_ : String) : SailM (BitVec 3) := do
  match arg_ with
  | "e8" => (pure 0b000#3)
  | "e16" => (pure 0b001#3)
  | "e32" => (pure 0b010#3)
  | "e64" => (pure 0b011#3)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def sew_flag_forwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "e8" => true
  | "e16" => true
  | "e32" => true
  | "e64" => true
  | _ => false

def sew_flag_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match arg_ with
  | 0b000 => true
  | 0b001 => true
  | 0b010 => true
  | 0b011 => true
  | _ => false

def maybe_lmul_flag_forwards (arg_ : String) : SailM (BitVec 3) := do
  match arg_ with
  | _ => throw Error.Exit

def maybe_lmul_flag_forwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit

def maybe_lmul_flag_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match arg_ with
  | 0b101 => true
  | 0b110 => true
  | 0b111 => true
  | 0b000 => true
  | 0b001 => true
  | 0b010 => true
  | 0b011 => true
  | _ => false

def ta_flag_forwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | _ => throw Error.Exit

def ta_flag_forwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit

def ta_flag_backwards_matches (arg_ : (BitVec 1)) : Bool :=
  match arg_ with
  | 1 => true
  | 0 => true
  | _ => false

def ma_flag_forwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | _ => throw Error.Exit

def ma_flag_forwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit

def ma_flag_backwards_matches (arg_ : (BitVec 1)) : Bool :=
  match arg_ with
  | 1 => true
  | 0 => true
  | _ => false

def vtr_mnemonic_forwards_matches (_vtr : (BitVec 3)) : Bool :=
  true

def vtype_assembly_backwards (arg_ : String) : SailM ((BitVec 3) × (BitVec 1) × (BitVec 1) × (BitVec 3) × (BitVec 3)) := do
  throw Error.Exit

def vtype_assembly_forwards_matches (arg_ : ((BitVec 3) × (BitVec 1) × (BitVec 1) × (BitVec 3) × (BitVec 3))) : Bool :=
  match arg_ with
  | (vtr, ma, ta, sew, lmul) =>
    (if ((((BitVec.access sew 2) != 1#1) && ((lmul != 0b100#3) && (vtr == 0b000#3))) : Bool)
    then true
    else true)

def vtype_assembly_backwards_matches (arg_ : String) : SailM Bool := do
  throw Error.Exit

def handle_illegal_vtype (rd : regidx) : SailM ExecutionResult := SailME.run do
  match illegal_vtype_reserved_behavior with
  | .IllegalVtype_Illegal => SailME.throw ((Illegal_Instruction ()) : ExecutionResult)
  | .IllegalVtype_Fatal => (reserved_behavior "unsupported or reserved vtype")
  | .IllegalVtype_SetVill => (pure ())
  writeReg vtype (1#1 +++ (zeros (n := (xlen -i 1))))
  writeReg vl (zeros (n := 32))
  (csr_name_write_callback "vtype" (← readReg vtype))
  (csr_name_write_callback "vl" (← readReg vl))
  (set_vstart (zeros (n := 16)))
  (wX_bits rd (← readReg vl))
  (pure RETIRE_SUCCESS)

def vl_use_ceil : Bool := false

/-- Type quantifiers: VLMAX : Nat, 1 ≤ VLMAX ∧ VLMAX ≤ (2 ^ 8) -/
def calculate_new_vl (AVL : (BitVec 32)) (VLMAX : Nat) : Nat :=
  let AVL := (BitVec.toNatInt AVL)
  if ((AVL ≤b VLMAX) : Bool)
  then AVL
  else
    (if ((AVL <b (2 *i VLMAX)) : Bool)
    then
      (if (vl_use_ceil : Bool)
      then (Int.tdiv (AVL +i 1) 2)
      else VLMAX)
    else VLMAX)

/-- Type quantifiers: k_ex1822374_ : Bool -/
def execute_vsetvl_type (ma : (BitVec 1)) (ta : (BitVec 1)) (sew : (BitVec 3)) (lmul : (BitVec 3)) (avl : (BitVec 32)) (requires_fixed_vlmax : Bool) (rd : regidx) : SailM ExecutionResult := do
  if (((is_invalid_lmul_pow lmul) || (is_invalid_sew_pow sew)) : Bool)
  then (handle_illegal_vtype rd)
  else
    (do
      let LMUL_pow_new := (BitVec.toInt lmul)
      let SEW_pow_new := ((BitVec.toNatInt sew) +i 3)
      let lmul_sew_ratio ← do (pure ((← (get_lmul_pow ())) -i (← (get_sew_pow ()))))
      let lmul_sew_ratio_new := (LMUL_pow_new -i SEW_pow_new)
      if (((SEW_pow_new >b elen_exp) || ((SEW_pow_new >b (LMUL_pow_new +i elen_exp)) || (requires_fixed_vlmax && ((lmul_sew_ratio != lmul_sew_ratio_new) || (not
                   (← (valid_vtype ()))))))) : Bool)
      then (handle_illegal_vtype rd)
      else
        (do
          let VLMAX := (2 ^i ((LMUL_pow_new +i vlen_exp) -i SEW_pow_new))
          writeReg vl (to_bits (l := 32) (calculate_new_vl avl VLMAX))
          (wX_bits rd (← readReg vl))
          writeReg vtype (_update_Vtype_vlmul
            (_update_Vtype_vsew
              (_update_Vtype_vta
                (_update_Vtype_vma (_update_Vtype_vill (Mk_Vtype (zeros (n := 32))) 0#1) ma) ta) sew)
            lmul)
          (set_vstart (zeros (n := 16)))
          (csr_name_write_callback "vtype" (← readReg vtype))
          (csr_name_write_callback "vl" (← readReg vl))
          (csr_name_write_callback "vstart" (← readReg vstart))
          (pure RETIRE_SUCCESS)))

