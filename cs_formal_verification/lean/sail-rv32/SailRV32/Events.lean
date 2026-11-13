import SailRV32.Prelude
import SailRV32.PlatformConfig

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

def undefined_Event (_ : Unit) : SailM Event := do
  (internal_pick
    [EV_FENCE, EV_TLB_MISS, EV_MISALIGNED_LOAD_EXCEPTION, EV_MISALIGNED_STORE_EXCEPTION])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def Event_of_num (arg_ : Nat) : Event :=
  match arg_ with
  | 0 => EV_FENCE
  | 1 => EV_TLB_MISS
  | 2 => EV_MISALIGNED_LOAD_EXCEPTION
  | _ => EV_MISALIGNED_STORE_EXCEPTION

def num_of_Event (arg_ : Event) : Int :=
  match arg_ with
  | .EV_FENCE => 0
  | .EV_TLB_MISS => 1
  | .EV_MISALIGNED_LOAD_EXCEPTION => 2
  | .EV_MISALIGNED_STORE_EXCEPTION => 3

def event_name_forwards (arg_ : Event) : String :=
  match arg_ with
  | .EV_FENCE => "fence"
  | .EV_TLB_MISS => "TLB miss"
  | .EV_MISALIGNED_LOAD_EXCEPTION => "misaligned load exception"
  | .EV_MISALIGNED_STORE_EXCEPTION => "misaligned store exception"

def event_name_backwards (arg_ : String) : SailM Event := do
  match arg_ with
  | "fence" => (pure EV_FENCE)
  | "TLB miss" => (pure EV_TLB_MISS)
  | "misaligned load exception" => (pure EV_MISALIGNED_LOAD_EXCEPTION)
  | "misaligned store exception" => (pure EV_MISALIGNED_STORE_EXCEPTION)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def event_name_forwards_matches (arg_ : Event) : Bool :=
  match arg_ with
  | .EV_FENCE => true
  | .EV_TLB_MISS => true
  | .EV_MISALIGNED_LOAD_EXCEPTION => true
  | .EV_MISALIGNED_STORE_EXCEPTION => true

def event_name_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fence" => true
  | "TLB miss" => true
  | "misaligned load exception" => true
  | "misaligned store exception" => true
  | _ => false

def name_of_event (event : Event) : String :=
  (event_name_forwards event)

def event_callback (x_0 : Event) (x_1 : Privilege) : SailM Unit := do
  (pure ())

def generate_event (event : Event) : SailM Unit := do
  (event_callback event (← readReg cur_privilege))

def generate_trap_event (trap : TrapCause) : SailM Unit := do
  match trap with
  | .Exception { trap := .E_Load_Addr_Align (), ext := _, excinst_offset := _, excinst := _, excinfo_is_gva := _, excinfo2 := _, excinfo := _ } =>
    (generate_event EV_MISALIGNED_LOAD_EXCEPTION)
  | .Exception { trap := .E_SAMO_Addr_Align (), ext := _, excinst_offset := _, excinst := _, excinfo_is_gva := _, excinfo2 := _, excinfo := _ } =>
    (generate_event EV_MISALIGNED_STORE_EXCEPTION)
  | _ => (pure ())

def undefined_event_selector (_ : Unit) : SailM event_selector := do
  (pure { event := ← (undefined_Event ())
          selector := ← (undefined_bitvector 64) })

def platform_event_selectors : (List event_selector) :=
  [{ event := EV_FENCE
     selector := 0b0000000000000000000000000000000000000000000000000000000000000001#64 }, { event := EV_MISALIGNED_LOAD_EXCEPTION
                                                                                            selector := 0b0000000000000000000000000000000000000000000000000000000000000010#64 }, { event := EV_MISALIGNED_STORE_EXCEPTION
                                                                                                                                                                                   selector := 0b0000000000000000000000000000000000000000000000000000000000000011#64 }]

def event_selector_width (_ : Unit) : Nat :=
  plat_hpmevent_width_bits

def selector_value (event_code : (BitVec 64)) : (BitVec 64) :=
  (zero_extend (m := 64) (Sail.BitVec.extractLsb event_code (plat_hpmevent_width_bits -i 1) 0))

def dispatch_events (_ : Unit) : SailM Unit := do
  (pure ())

