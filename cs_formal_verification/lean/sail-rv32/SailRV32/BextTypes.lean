import Sail
import SailRV32.Defs
import SailRV32.SpecializationArchSem
import SailRV32.FakeReal
import SailRV32.RiscvExtrasExecutable

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

def undefined_brop_zbb (_ : Unit) : SailM brop_zbb := do
  (internal_pick [ANDN, ORN, XNOR, MAX, MAXU, MIN, MINU, ROL, ROR])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 8 -/
def brop_zbb_of_num (arg_ : Nat) : brop_zbb :=
  match arg_ with
  | 0 => ANDN
  | 1 => ORN
  | 2 => XNOR
  | 3 => MAX
  | 4 => MAXU
  | 5 => MIN
  | 6 => MINU
  | 7 => ROL
  | _ => ROR

def num_of_brop_zbb (arg_ : brop_zbb) : Int :=
  match arg_ with
  | .ANDN => 0
  | .ORN => 1
  | .XNOR => 2
  | .MAX => 3
  | .MAXU => 4
  | .MIN => 5
  | .MINU => 6
  | .ROL => 7
  | .ROR => 8

def undefined_brop_zbkb (_ : Unit) : SailM brop_zbkb := do
  (internal_pick [PACK, PACKH])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def brop_zbkb_of_num (arg_ : Nat) : brop_zbkb :=
  match arg_ with
  | 0 => PACK
  | _ => PACKH

def num_of_brop_zbkb (arg_ : brop_zbkb) : Int :=
  match arg_ with
  | .PACK => 0
  | .PACKH => 1

def undefined_brop_zbs (_ : Unit) : SailM brop_zbs := do
  (internal_pick [BCLR, BEXT, BINV, BSET])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def brop_zbs_of_num (arg_ : Nat) : brop_zbs :=
  match arg_ with
  | 0 => BCLR
  | 1 => BEXT
  | 2 => BINV
  | _ => BSET

def num_of_brop_zbs (arg_ : brop_zbs) : Int :=
  match arg_ with
  | .BCLR => 0
  | .BEXT => 1
  | .BINV => 2
  | .BSET => 3

def undefined_bropw_zbb (_ : Unit) : SailM bropw_zbb := do
  (internal_pick [ROLW, RORW])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def bropw_zbb_of_num (arg_ : Nat) : bropw_zbb :=
  match arg_ with
  | 0 => ROLW
  | _ => RORW

def num_of_bropw_zbb (arg_ : bropw_zbb) : Int :=
  match arg_ with
  | .ROLW => 0
  | .RORW => 1

def undefined_biop_zbs (_ : Unit) : SailM biop_zbs := do
  (internal_pick [BCLRI, BEXTI, BINVI, BSETI])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def biop_zbs_of_num (arg_ : Nat) : biop_zbs :=
  match arg_ with
  | 0 => BCLRI
  | 1 => BEXTI
  | 2 => BINVI
  | _ => BSETI

def num_of_biop_zbs (arg_ : biop_zbs) : Int :=
  match arg_ with
  | .BCLRI => 0
  | .BEXTI => 1
  | .BINVI => 2
  | .BSETI => 3

def undefined_extop_zbb (_ : Unit) : SailM extop_zbb := do
  (internal_pick [SEXTB, SEXTH, ZEXTH])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def extop_zbb_of_num (arg_ : Nat) : extop_zbb :=
  match arg_ with
  | 0 => SEXTB
  | 1 => SEXTH
  | _ => ZEXTH

def num_of_extop_zbb (arg_ : extop_zbb) : Int :=
  match arg_ with
  | .SEXTB => 0
  | .SEXTH => 1
  | .ZEXTH => 2

