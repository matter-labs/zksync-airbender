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

def encdec_vaesdf_backwards (arg_ : (BitVec 6)) : SailM zvk_vaesdf_funct6 := do
  match arg_ with
  | 0b101000 => (pure ZVK_VAESDF_VV)
  | 0b101001 => (pure ZVK_VAESDF_VS)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_vaesdf_forwards_matches (arg_ : zvk_vaesdf_funct6) : Bool :=
  match arg_ with
  | .ZVK_VAESDF_VV => true
  | .ZVK_VAESDF_VS => true

def encdec_vaesdf_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b101000 => true
  | 0b101001 => true
  | _ => false

def vaesdf_mnemonic_backwards (arg_ : String) : SailM zvk_vaesdf_funct6 := do
  match arg_ with
  | "vaesdf.vv" => (pure ZVK_VAESDF_VV)
  | "vaesdf.vs" => (pure ZVK_VAESDF_VS)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def vaesdf_mnemonic_forwards_matches (arg_ : zvk_vaesdf_funct6) : Bool :=
  match arg_ with
  | .ZVK_VAESDF_VV => true
  | .ZVK_VAESDF_VS => true

def vaesdf_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vaesdf.vv" => true
  | "vaesdf.vs" => true
  | _ => false

def encdec_vaesdm_backwards (arg_ : (BitVec 6)) : SailM zvk_vaesdm_funct6 := do
  match arg_ with
  | 0b101000 => (pure ZVK_VAESDM_VV)
  | 0b101001 => (pure ZVK_VAESDM_VS)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_vaesdm_forwards_matches (arg_ : zvk_vaesdm_funct6) : Bool :=
  match arg_ with
  | .ZVK_VAESDM_VV => true
  | .ZVK_VAESDM_VS => true

def encdec_vaesdm_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b101000 => true
  | 0b101001 => true
  | _ => false

def vaesdm_mnemonic_backwards (arg_ : String) : SailM zvk_vaesdm_funct6 := do
  match arg_ with
  | "vaesdm.vv" => (pure ZVK_VAESDM_VV)
  | "vaesdm.vs" => (pure ZVK_VAESDM_VS)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def vaesdm_mnemonic_forwards_matches (arg_ : zvk_vaesdm_funct6) : Bool :=
  match arg_ with
  | .ZVK_VAESDM_VV => true
  | .ZVK_VAESDM_VS => true

def vaesdm_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vaesdm.vv" => true
  | "vaesdm.vs" => true
  | _ => false

def encdec_vaesef_backwards (arg_ : (BitVec 6)) : SailM zvk_vaesef_funct6 := do
  match arg_ with
  | 0b101000 => (pure ZVK_VAESEF_VV)
  | 0b101001 => (pure ZVK_VAESEF_VS)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_vaesef_forwards_matches (arg_ : zvk_vaesef_funct6) : Bool :=
  match arg_ with
  | .ZVK_VAESEF_VV => true
  | .ZVK_VAESEF_VS => true

def encdec_vaesef_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b101000 => true
  | 0b101001 => true
  | _ => false

def vaesef_mnemonic_backwards (arg_ : String) : SailM zvk_vaesef_funct6 := do
  match arg_ with
  | "vaesef.vv" => (pure ZVK_VAESEF_VV)
  | "vaesef.vs" => (pure ZVK_VAESEF_VS)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def vaesef_mnemonic_forwards_matches (arg_ : zvk_vaesef_funct6) : Bool :=
  match arg_ with
  | .ZVK_VAESEF_VV => true
  | .ZVK_VAESEF_VS => true

def vaesef_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vaesef.vv" => true
  | "vaesef.vs" => true
  | _ => false

def encdec_vaesem_backwards (arg_ : (BitVec 6)) : SailM zvk_vaesem_funct6 := do
  match arg_ with
  | 0b101000 => (pure ZVK_VAESEM_VV)
  | 0b101001 => (pure ZVK_VAESEM_VS)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_vaesem_forwards_matches (arg_ : zvk_vaesem_funct6) : Bool :=
  match arg_ with
  | .ZVK_VAESEM_VV => true
  | .ZVK_VAESEM_VS => true

def encdec_vaesem_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b101000 => true
  | 0b101001 => true
  | _ => false

def vaesem_mnemonic_backwards (arg_ : String) : SailM zvk_vaesem_funct6 := do
  match arg_ with
  | "vaesem.vv" => (pure ZVK_VAESEM_VV)
  | "vaesem.vs" => (pure ZVK_VAESEM_VS)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def vaesem_mnemonic_forwards_matches (arg_ : zvk_vaesem_funct6) : Bool :=
  match arg_ with
  | .ZVK_VAESEM_VV => true
  | .ZVK_VAESEM_VS => true

def vaesem_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vaesem.vv" => true
  | "vaesem.vs" => true
  | _ => false

