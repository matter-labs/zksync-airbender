import SailRV32.Prelude
import SailRV32.IsaVersion
import SailRV32.Xlen
import SailRV32.PlatformConfig
import SailRV32.SysRegs

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

def undefined_stateen_bit (_ : Unit) : SailM stateen_bit := do
  (internal_pick
    [STATEEN_FCSR, STATEEN_SRMCFG, STATEEN_P1P13, STATEEN_CONTEXT, STATEEN_ENVCFG, STATEEN_SE])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def stateen_bit_of_num (arg_ : Nat) : stateen_bit :=
  match arg_ with
  | 0 => STATEEN_FCSR
  | 1 => STATEEN_SRMCFG
  | 2 => STATEEN_P1P13
  | 3 => STATEEN_CONTEXT
  | 4 => STATEEN_ENVCFG
  | _ => STATEEN_SE

def num_of_stateen_bit (arg_ : stateen_bit) : Int :=
  match arg_ with
  | .STATEEN_FCSR => 0
  | .STATEEN_SRMCFG => 1
  | .STATEEN_P1P13 => 2
  | .STATEEN_CONTEXT => 3
  | .STATEEN_ENVCFG => 4
  | .STATEEN_SE => 5

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 63 -/
def stateen_bit_index_backwards (arg_ : Nat) : SailM stateen_bit := do
  match arg_ with
  | 63 => (pure STATEEN_SE)
  | 62 => (pure STATEEN_ENVCFG)
  | 57 => (pure STATEEN_CONTEXT)
  | 56 => (pure STATEEN_P1P13)
  | 55 => (pure STATEEN_SRMCFG)
  | 1 => (pure STATEEN_FCSR)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def stateen_bit_index_forwards_matches (arg_ : stateen_bit) : Bool :=
  match arg_ with
  | .STATEEN_SE => true
  | .STATEEN_ENVCFG => true
  | .STATEEN_CONTEXT => true
  | .STATEEN_P1P13 => true
  | .STATEEN_SRMCFG => true
  | .STATEEN_FCSR => true

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 63 -/
def stateen_bit_index_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 63 => true
  | 62 => true
  | 57 => true
  | 56 => true
  | 55 => true
  | 1 => true
  | _ => false

def undefined_Mstateen0 (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_Mstateen0_AIA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _update_Mstateen0_AIA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_Hstateen0_AIA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _set_Mstateen0_AIA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen0_AIA r v)

def _get_Hstateen0_AIA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _set_Hstateen0_AIA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen0_AIA r v)

def _get_Mstateen0_CONTEXT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)

def _update_Mstateen0_CONTEXT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_Hstateen0_CONTEXT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _set_Mstateen0_CONTEXT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen0_CONTEXT r v)

def _get_Hstateen0_CONTEXT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)

def _set_Hstateen0_CONTEXT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen0_CONTEXT r v)

def _get_Mstateen0_CSRIND (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _update_Mstateen0_CSRIND (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_Hstateen0_CSRIND (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _set_Mstateen0_CSRIND (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen0_CSRIND r v)

def _get_Hstateen0_CSRIND (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _set_Hstateen0_CSRIND (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen0_CSRIND r v)

def _get_Mstateen0_CTR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _update_Mstateen0_CTR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _update_Hstateen0_CTR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _set_Mstateen0_CTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen0_CTR r v)

def _get_Hstateen0_CTR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _set_Hstateen0_CTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen0_CTR r v)

def _get_Mstateen0_ENVCFG (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _update_Mstateen0_ENVCFG (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_Hstateen0_ENVCFG (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _set_Mstateen0_ENVCFG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen0_ENVCFG r v)

def _get_Hstateen0_ENVCFG (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _set_Hstateen0_ENVCFG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen0_ENVCFG r v)

def _get_Mstateen0_FCSR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Mstateen0_FCSR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_Hstateen0_FCSR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_Sstateen0_FCSR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Mstateen0_FCSR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen0_FCSR r v)

def _get_Hstateen0_FCSR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_Sstateen0_FCSR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _set_Hstateen0_FCSR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen0_FCSR r v)

def _set_Sstateen0_FCSR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstateen0_FCSR r v)

def _get_Mstateen0_IMSIC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _update_Mstateen0_IMSIC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _update_Hstateen0_IMSIC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _set_Mstateen0_IMSIC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen0_IMSIC r v)

def _get_Hstateen0_IMSIC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _set_Hstateen0_IMSIC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen0_IMSIC r v)

def _get_Mstateen0_JVT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_Mstateen0_JVT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_Hstateen0_JVT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_Sstateen0_JVT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _set_Mstateen0_JVT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen0_JVT r v)

def _get_Hstateen0_JVT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_Sstateen0_JVT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _set_Hstateen0_JVT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen0_JVT r v)

def _set_Sstateen0_JVT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstateen0_JVT r v)

def _get_Mstateen0_P1P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)

def _update_Mstateen0_P1P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _set_Mstateen0_P1P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen0_P1P13 r v)

def _get_Mstateen0_SE0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_Mstateen0_SE0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_Hstateen0_SE0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _set_Mstateen0_SE0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen0_SE0 r v)

def _get_Hstateen0_SE0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _set_Hstateen0_SE0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen0_SE0 r v)

def _get_Mstateen0_SRMCFG (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)

def _update_Mstateen0_SRMCFG (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _set_Mstateen0_SRMCFG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen0_SRMCFG r v)

def undefined_Mstateen1 (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_Mstateen1_SE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_Mstateen1_SE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_Hstateen1_SE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _set_Mstateen1_SE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen1_SE1 r v)

def _get_Hstateen1_SE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _set_Hstateen1_SE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen1_SE1 r v)

def undefined_Mstateen2 (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_Mstateen2_SE2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_Mstateen2_SE2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_Hstateen2_SE2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _set_Mstateen2_SE2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen2_SE2 r v)

def _get_Hstateen2_SE2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _set_Hstateen2_SE2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen2_SE2 r v)

def undefined_Mstateen3 (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_Mstateen3_SE3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_Mstateen3_SE3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_Hstateen3_SE3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _set_Mstateen3_SE3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen3_SE3 r v)

def _get_Hstateen3_SE3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _set_Hstateen3_SE3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen3_SE3 r v)

def legalize_mstateen0 (m : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_Mstateen0 v)
  (pure (_update_Mstateen0_C
      (_update_Mstateen0_FCSR
        (_update_Mstateen0_SRMCFG
          (_update_Mstateen0_P1P13
            (_update_Mstateen0_CONTEXT
              (_update_Mstateen0_ENVCFG (_update_Mstateen0_SE0 m (_get_Mstateen0_SE0 v))
                (← do
                  if ((← (currentlyEnabled Ext_S)) : Bool)
                  then (pure (_get_Mstateen0_ENVCFG v))
                  else (pure 0#1)))
              (← do
                if (((← (currentlyEnabled Ext_Sdtrig)) && (sdtrig_has_scontext || sdtrig_has_hcontext)) : Bool)
                then (pure (_get_Mstateen0_CONTEXT v))
                else (pure 0#1)))
            (← do
              if ((delegh_csrs_are_defined && ((← (currentlyEnabled Ext_H)) && (xlen == 32))) : Bool)
              then (pure (_get_Mstateen0_P1P13 v))
              else (pure 0#1)))
          (← do
            if ((← (currentlyEnabled Ext_Ssqosid)) : Bool)
            then (pure (_get_Mstateen0_SRMCFG v))
            else (pure 0#1)))
        (← do
          if (((hartSupports Ext_Zfinx) && ((_get_Misa_F (← readReg misa)) == 0#1)) : Bool)
          then (pure (_get_Mstateen0_FCSR v))
          else (pure 0#1))) 0#1))

def legalize_mstateen1 (m : (BitVec 64)) (_v : (BitVec 64)) : (BitVec 64) :=
  m

def legalize_mstateen2 (m : (BitVec 64)) (_v : (BitVec 64)) : (BitVec 64) :=
  m

def legalize_mstateen3 (m : (BitVec 64)) (_v : (BitVec 64)) : (BitVec 64) :=
  m

def undefined_Hstateen0 (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_Hstateen1 (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_Hstateen2 (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_Hstateen3 (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 3 -/
def get_hstateen_mask (idx : Nat) : SailM (BitVec 64) := do
  (get_mstateen idx)

def legalize_hstateen0 (h : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v ← do (pure (Mk_Hstateen0 (v &&& (← (get_hstateen_mask 0)))))
  (pure (_update_Hstateen0_C
      (_update_Hstateen0_FCSR
        (_update_Hstateen0_CONTEXT
          (_update_Hstateen0_ENVCFG (_update_Hstateen0_SE0 h (_get_Hstateen0_SE0 v))
            (← do
              if ((← (currentlyEnabled Ext_S)) : Bool)
              then (pure (_get_Hstateen0_ENVCFG v))
              else (pure 0#1)))
          (← do
            if (((← (currentlyEnabled Ext_Sdtrig)) && sdtrig_has_scontext) : Bool)
            then (pure (_get_Hstateen0_CONTEXT v))
            else (pure 0#1)))
        (← do
          if (((hartSupports Ext_Zfinx) && ((_get_Misa_F (← readReg misa)) == 0#1)) : Bool)
          then (pure (_get_Hstateen0_FCSR v))
          else (pure 0#1))) 0#1))

def legalize_hstateen1 (_h : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  (pure (Mk_Hstateen1 (v &&& (← (get_hstateen_mask 1)))))

def legalize_hstateen2 (_h : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  (pure (Mk_Hstateen2 (v &&& (← (get_hstateen_mask 2)))))

def legalize_hstateen3 (_h : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  (pure (Mk_Hstateen3 (v &&& (← (get_hstateen_mask 3)))))

def undefined_Sstateen0 (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_Sstateen1 (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_Sstateen2 (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_Sstateen3 (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 3 -/
def get_sstateen_mask (idx : Nat) : SailM (BitVec 64) := do
  (pure ((← (get_mstateen idx)) &&& (← (get_hstateen idx))))

def legalize_sstateen0 (s : (BitVec 32)) (v : (BitVec 32)) : SailM (BitVec 32) := do
  let v := (Mk_Sstateen0 v)
  let mask ← do (get_sstateen_mask 0)
  let legalized ← do
    (pure (_update_Sstateen0_C
        (_update_Sstateen0_FCSR s
          (← do
            if (((hartSupports Ext_Zfinx) && ((_get_Misa_F (← readReg misa)) == 0#1)) : Bool)
            then (pure (_get_Sstateen0_FCSR v))
            else (pure 0#1))) 0#1))
  (pure (Mk_Sstateen0 (legalized &&& (Sail.BitVec.extractLsb mask 31 0))))

def legalize_sstateen1 (s : (BitVec 32)) (_v : (BitVec 32)) : (BitVec 32) :=
  s

def legalize_sstateen2 (s : (BitVec 32)) (_v : (BitVec 32)) : (BitVec 32) :=
  s

def legalize_sstateen3 (s : (BitVec 32)) (_v : (BitVec 32)) : (BitVec 32) :=
  s

def reset_stateen (_ : Unit) : SailM Unit := do
  writeReg mstateen0 (zeros (n := 64))
  writeReg mstateen1 (zeros (n := 64))
  writeReg mstateen2 (zeros (n := 64))
  writeReg mstateen3 (zeros (n := 64))

