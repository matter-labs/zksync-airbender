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

def undefined_uop (_ : Unit) : SailM uop := do
  (internal_pick [LUI, AUIPC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def uop_of_num (arg_ : Nat) : uop :=
  match arg_ with
  | 0 => LUI
  | _ => AUIPC

def num_of_uop (arg_ : uop) : Int :=
  match arg_ with
  | .LUI => 0
  | .AUIPC => 1

def undefined_bop (_ : Unit) : SailM bop := do
  (internal_pick [BEQ, BNE, BLT, BGE, BLTU, BGEU])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def bop_of_num (arg_ : Nat) : bop :=
  match arg_ with
  | 0 => BEQ
  | 1 => BNE
  | 2 => BLT
  | 3 => BGE
  | 4 => BLTU
  | _ => BGEU

def num_of_bop (arg_ : bop) : Int :=
  match arg_ with
  | .BEQ => 0
  | .BNE => 1
  | .BLT => 2
  | .BGE => 3
  | .BLTU => 4
  | .BGEU => 5

def undefined_iop (_ : Unit) : SailM iop := do
  (internal_pick [ADDI, SLTI, SLTIU, XORI, ORI, ANDI])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def iop_of_num (arg_ : Nat) : iop :=
  match arg_ with
  | 0 => ADDI
  | 1 => SLTI
  | 2 => SLTIU
  | 3 => XORI
  | 4 => ORI
  | _ => ANDI

def num_of_iop (arg_ : iop) : Int :=
  match arg_ with
  | .ADDI => 0
  | .SLTI => 1
  | .SLTIU => 2
  | .XORI => 3
  | .ORI => 4
  | .ANDI => 5

def undefined_sop (_ : Unit) : SailM sop := do
  (internal_pick [SLLI, SRLI, SRAI])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def sop_of_num (arg_ : Nat) : sop :=
  match arg_ with
  | 0 => SLLI
  | 1 => SRLI
  | _ => SRAI

def num_of_sop (arg_ : sop) : Int :=
  match arg_ with
  | .SLLI => 0
  | .SRLI => 1
  | .SRAI => 2

def undefined_rop (_ : Unit) : SailM rop := do
  (internal_pick [ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 9 -/
def rop_of_num (arg_ : Nat) : rop :=
  match arg_ with
  | 0 => ADD
  | 1 => SUB
  | 2 => SLL
  | 3 => SLT
  | 4 => SLTU
  | 5 => XOR
  | 6 => SRL
  | 7 => SRA
  | 8 => OR
  | _ => AND

def num_of_rop (arg_ : rop) : Int :=
  match arg_ with
  | .ADD => 0
  | .SUB => 1
  | .SLL => 2
  | .SLT => 3
  | .SLTU => 4
  | .XOR => 5
  | .SRL => 6
  | .SRA => 7
  | .OR => 8
  | .AND => 9

def undefined_ropw (_ : Unit) : SailM ropw := do
  (internal_pick [ADDW, SUBW, SLLW, SRLW, SRAW])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def ropw_of_num (arg_ : Nat) : ropw :=
  match arg_ with
  | 0 => ADDW
  | 1 => SUBW
  | 2 => SLLW
  | 3 => SRLW
  | _ => SRAW

def num_of_ropw (arg_ : ropw) : Int :=
  match arg_ with
  | .ADDW => 0
  | .SUBW => 1
  | .SLLW => 2
  | .SRLW => 3
  | .SRAW => 4

def undefined_sopw (_ : Unit) : SailM sopw := do
  (internal_pick [SLLIW, SRLIW, SRAIW])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def sopw_of_num (arg_ : Nat) : sopw :=
  match arg_ with
  | 0 => SLLIW
  | 1 => SRLIW
  | _ => SRAIW

def num_of_sopw (arg_ : sopw) : Int :=
  match arg_ with
  | .SLLIW => 0
  | .SRLIW => 1
  | .SRAIW => 2

