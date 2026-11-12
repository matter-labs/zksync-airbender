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

def undefined_amoop (_ : Unit) : SailM amoop := do
  (internal_pick [AMOSWAP, AMOAND, AMOOR, AMOXOR, AMOADD, AMOMIN, AMOMAX, AMOMINU, AMOMAXU, AMOCAS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 9 -/
def amoop_of_num (arg_ : Nat) : amoop :=
  match arg_ with
  | 0 => AMOSWAP
  | 1 => AMOAND
  | 2 => AMOOR
  | 3 => AMOXOR
  | 4 => AMOADD
  | 5 => AMOMIN
  | 6 => AMOMAX
  | 7 => AMOMINU
  | 8 => AMOMAXU
  | _ => AMOCAS

def num_of_amoop (arg_ : amoop) : Int :=
  match arg_ with
  | .AMOSWAP => 0
  | .AMOAND => 1
  | .AMOOR => 2
  | .AMOXOR => 3
  | .AMOADD => 4
  | .AMOMIN => 5
  | .AMOMAX => 6
  | .AMOMINU => 7
  | .AMOMAXU => 8
  | .AMOCAS => 9

def amo_mnemonic_forwards (arg_ : amoop) : String :=
  match arg_ with
  | .AMOSWAP => "amoswap"
  | .AMOAND => "amoand"
  | .AMOOR => "amoor"
  | .AMOXOR => "amoxor"
  | .AMOADD => "amoadd"
  | .AMOMIN => "amomin"
  | .AMOMAX => "amomax"
  | .AMOMINU => "amominu"
  | .AMOMAXU => "amomaxu"
  | .AMOCAS => "amocas"

def amo_mnemonic_backwards (arg_ : String) : SailM amoop := do
  match arg_ with
  | "amoswap" => (pure AMOSWAP)
  | "amoand" => (pure AMOAND)
  | "amoor" => (pure AMOOR)
  | "amoxor" => (pure AMOXOR)
  | "amoadd" => (pure AMOADD)
  | "amomin" => (pure AMOMIN)
  | "amomax" => (pure AMOMAX)
  | "amominu" => (pure AMOMINU)
  | "amomaxu" => (pure AMOMAXU)
  | "amocas" => (pure AMOCAS)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def amo_mnemonic_forwards_matches (arg_ : amoop) : Bool :=
  match arg_ with
  | .AMOSWAP => true
  | .AMOAND => true
  | .AMOOR => true
  | .AMOXOR => true
  | .AMOADD => true
  | .AMOMIN => true
  | .AMOMAX => true
  | .AMOMINU => true
  | .AMOMAXU => true
  | .AMOCAS => true

def amo_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "amoswap" => true
  | "amoand" => true
  | "amoor" => true
  | "amoxor" => true
  | "amoadd" => true
  | "amomin" => true
  | "amomax" => true
  | "amominu" => true
  | "amomaxu" => true
  | "amocas" => true
  | _ => false

def maybe_aqrl_forwards (arg_ : (Bool × Bool)) : String :=
  match arg_ with
  | (true, true) => ".aqrl"
  | (true, false) => ".aq"
  | (false, true) => ".rl"
  | (false, false) => ""

def maybe_aqrl_backwards (arg_ : String) : SailM (Bool × Bool) := do
  match arg_ with
  | ".aqrl" => (pure (true, true))
  | ".aq" => (pure (true, false))
  | ".rl" => (pure (false, true))
  | "" => (pure (false, false))
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def maybe_aqrl_forwards_matches (arg_ : (Bool × Bool)) : Bool :=
  match arg_ with
  | (true, true) => true
  | (true, false) => true
  | (false, true) => true
  | (false, false) => true

def maybe_aqrl_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | ".aqrl" => true
  | ".aq" => true
  | ".rl" => true
  | "" => true
  | _ => false

