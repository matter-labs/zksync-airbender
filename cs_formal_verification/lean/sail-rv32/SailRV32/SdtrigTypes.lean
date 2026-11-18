import SailRV32.Vector
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

def undefined_Trig_Type (_ : Unit) : SailM Trig_Type := do
  (internal_pick
    [TT_none, TT_legacy, TT_mcontrol, TT_icount, TT_itrigger, TT_etrigger, TT_mcontrol6, TT_tmexttrigger, TT_custom, TT_disabled, TT_reserved])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 10 -/
def Trig_Type_of_num (arg_ : Nat) : Trig_Type :=
  match arg_ with
  | 0 => TT_none
  | 1 => TT_legacy
  | 2 => TT_mcontrol
  | 3 => TT_icount
  | 4 => TT_itrigger
  | 5 => TT_etrigger
  | 6 => TT_mcontrol6
  | 7 => TT_tmexttrigger
  | 8 => TT_custom
  | 9 => TT_disabled
  | _ => TT_reserved

def num_of_Trig_Type (arg_ : Trig_Type) : Int :=
  match arg_ with
  | .TT_none => 0
  | .TT_legacy => 1
  | .TT_mcontrol => 2
  | .TT_icount => 3
  | .TT_itrigger => 4
  | .TT_etrigger => 5
  | .TT_mcontrol6 => 6
  | .TT_tmexttrigger => 7
  | .TT_custom => 8
  | .TT_disabled => 9
  | .TT_reserved => 10

def trig_type_bits_forwards (arg_ : (BitVec 4)) : Trig_Type :=
  match arg_ with
  | 0b0000 => TT_none
  | 0b0001 => TT_legacy
  | 0b0010 => TT_mcontrol
  | 0b0011 => TT_icount
  | 0b0100 => TT_itrigger
  | 0b0101 => TT_etrigger
  | 0b0110 => TT_mcontrol6
  | 0b0111 => TT_tmexttrigger
  | 0b1111 => TT_disabled
  | 0b1100 => TT_custom
  | 0b1101 => TT_custom
  | 0b1110 => TT_custom
  | 0b1000 => TT_reserved
  | 0b1001 => TT_reserved
  | 0b1010 => TT_reserved
  | _ => TT_reserved

def trig_type_bits_backwards (arg_ : Trig_Type) : SailM (BitVec 4) := do
  match arg_ with
  | .TT_none => (pure 0b0000#4)
  | .TT_legacy => (pure 0b0001#4)
  | .TT_mcontrol => (pure 0b0010#4)
  | .TT_icount => (pure 0b0011#4)
  | .TT_itrigger => (pure 0b0100#4)
  | .TT_etrigger => (pure 0b0101#4)
  | .TT_mcontrol6 => (pure 0b0110#4)
  | .TT_tmexttrigger => (pure 0b0111#4)
  | .TT_disabled => (pure 0b1111#4)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def trig_type_bits_forwards_matches (arg_ : (BitVec 4)) : Bool :=
  match arg_ with
  | 0b0000 => true
  | 0b0001 => true
  | 0b0010 => true
  | 0b0011 => true
  | 0b0100 => true
  | 0b0101 => true
  | 0b0110 => true
  | 0b0111 => true
  | 0b1111 => true
  | 0b1100 => true
  | 0b1101 => true
  | 0b1110 => true
  | 0b1000 => true
  | 0b1001 => true
  | 0b1010 => true
  | 0b1011 => true
  | _ => false

def trig_type_bits_backwards_matches (arg_ : Trig_Type) : Bool :=
  match arg_ with
  | .TT_none => true
  | .TT_legacy => true
  | .TT_mcontrol => true
  | .TT_icount => true
  | .TT_itrigger => true
  | .TT_etrigger => true
  | .TT_mcontrol6 => true
  | .TT_tmexttrigger => true
  | .TT_disabled => true
  | _ => false

def trig_type_name_forwards (arg_ : Trig_Type) : String :=
  match arg_ with
  | .TT_none => "none"
  | .TT_legacy => "legacy"
  | .TT_mcontrol => "mcontrol"
  | .TT_icount => "icount"
  | .TT_itrigger => "itrigger"
  | .TT_etrigger => "etrigger"
  | .TT_mcontrol6 => "mcontrol6"
  | .TT_tmexttrigger => "tmexttrigger"
  | .TT_custom => "custom"
  | .TT_disabled => "disabled"
  | .TT_reserved => "reserved"

def trig_type_name_backwards (arg_ : String) : SailM Trig_Type := do
  match arg_ with
  | "none" => (pure TT_none)
  | "legacy" => (pure TT_legacy)
  | "mcontrol" => (pure TT_mcontrol)
  | "icount" => (pure TT_icount)
  | "itrigger" => (pure TT_itrigger)
  | "etrigger" => (pure TT_etrigger)
  | "mcontrol6" => (pure TT_mcontrol6)
  | "tmexttrigger" => (pure TT_tmexttrigger)
  | "custom" => (pure TT_custom)
  | "disabled" => (pure TT_disabled)
  | "reserved" => (pure TT_reserved)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def trig_type_name_forwards_matches (arg_ : Trig_Type) : Bool :=
  match arg_ with
  | .TT_none => true
  | .TT_legacy => true
  | .TT_mcontrol => true
  | .TT_icount => true
  | .TT_itrigger => true
  | .TT_etrigger => true
  | .TT_mcontrol6 => true
  | .TT_tmexttrigger => true
  | .TT_custom => true
  | .TT_disabled => true
  | .TT_reserved => true

def trig_type_name_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "none" => true
  | "legacy" => true
  | "mcontrol" => true
  | "icount" => true
  | "itrigger" => true
  | "etrigger" => true
  | "mcontrol6" => true
  | "tmexttrigger" => true
  | "custom" => true
  | "disabled" => true
  | "reserved" => true
  | _ => false

def is_supported_trigger_type (tt : (BitVec 4)) : Bool :=
  if ((not (trig_type_bits_forwards_matches tt)) : Bool)
  then false
  else
    (let typ := (trig_type_bits_forwards tt)
    ((typ == TT_none) || ((typ == TT_disabled) || (((typ == TT_icount) && sdtrig_has_icount) || (((typ == TT_etrigger) && sdtrig_has_etrigger) || ((typ == TT_itrigger) && sdtrig_has_itrigger))))))

def supported_triggers_info (_ : Unit) : SailM (BitVec 16) := do
  let flag := (zero_extend (m := 16) 1#1)
  let info ← (( do
    (pure (flag <<< (BitVec.toNatInt (← (trig_type_bits_backwards TT_disabled))))) ) : SailM
    (BitVec 16) )
  let info ← (( do
    if (sdtrig_has_icount : Bool)
    then
      (do
        (pure (info ||| (flag <<< (BitVec.toNatInt (← (trig_type_bits_backwards TT_icount)))))))
    else (pure info) ) : SailM (BitVec 16) )
  let info ← (( do
    if (sdtrig_has_etrigger : Bool)
    then
      (do
        (pure (info ||| (flag <<< (BitVec.toNatInt (← (trig_type_bits_backwards TT_etrigger)))))))
    else (pure info) ) : SailM (BitVec 16) )
  if (sdtrig_has_itrigger : Bool)
  then
    (do
      (pure (info ||| (flag <<< (BitVec.toNatInt (← (trig_type_bits_backwards TT_itrigger)))))))
  else (pure info)

def undefined_Trig_Action (_ : Unit) : SailM Trig_Action := do
  (internal_pick
    [TA_Breakpoint, TA_Enter_Debug, TA_Trace_On, TA_Trace_Off, TA_Trace_Notify, TA_Ext_Trigger_0, TA_Ext_Trigger_1])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def Trig_Action_of_num (arg_ : Nat) : Trig_Action :=
  match arg_ with
  | 0 => TA_Breakpoint
  | 1 => TA_Enter_Debug
  | 2 => TA_Trace_On
  | 3 => TA_Trace_Off
  | 4 => TA_Trace_Notify
  | 5 => TA_Ext_Trigger_0
  | _ => TA_Ext_Trigger_1

def num_of_Trig_Action (arg_ : Trig_Action) : Int :=
  match arg_ with
  | .TA_Breakpoint => 0
  | .TA_Enter_Debug => 1
  | .TA_Trace_On => 2
  | .TA_Trace_Off => 3
  | .TA_Trace_Notify => 4
  | .TA_Ext_Trigger_0 => 5
  | .TA_Ext_Trigger_1 => 6

def trig_action_forwards (arg_ : (BitVec 6)) : SailM Trig_Action := do
  match arg_ with
  | 0b000000 => (pure TA_Breakpoint)
  | 0b000001 => (pure TA_Enter_Debug)
  | 0b000010 => (pure TA_Trace_On)
  | 0b000011 => (pure TA_Trace_Off)
  | 0b000100 => (pure TA_Trace_Notify)
  | 0b001000 => (pure TA_Ext_Trigger_0)
  | 0b001001 => (pure TA_Ext_Trigger_1)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def trig_action_backwards (arg_ : Trig_Action) : (BitVec 6) :=
  match arg_ with
  | .TA_Breakpoint => 0b000000#6
  | .TA_Enter_Debug => 0b000001#6
  | .TA_Trace_On => 0b000010#6
  | .TA_Trace_Off => 0b000011#6
  | .TA_Trace_Notify => 0b000100#6
  | .TA_Ext_Trigger_0 => 0b001000#6
  | .TA_Ext_Trigger_1 => 0b001001#6

def trig_action_forwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b000000 => true
  | 0b000001 => true
  | 0b000010 => true
  | 0b000011 => true
  | 0b000100 => true
  | 0b001000 => true
  | 0b001001 => true
  | _ => false

def trig_action_backwards_matches (arg_ : Trig_Action) : Bool :=
  match arg_ with
  | .TA_Breakpoint => true
  | .TA_Enter_Debug => true
  | .TA_Trace_On => true
  | .TA_Trace_Off => true
  | .TA_Trace_Notify => true
  | .TA_Ext_Trigger_0 => true
  | .TA_Ext_Trigger_1 => true

def trigger_action_name_forwards (arg_ : Trig_Action) : String :=
  match arg_ with
  | .TA_Breakpoint => "Breakpoint"
  | .TA_Enter_Debug => "Enter Debug"
  | .TA_Trace_On => "Trace On"
  | .TA_Trace_Off => "Trace Off"
  | .TA_Trace_Notify => "Trace Notify"
  | .TA_Ext_Trigger_0 => "External Trigger Output 0"
  | .TA_Ext_Trigger_1 => "External Trigger Output 1"

def trigger_action_name_backwards (arg_ : String) : SailM Trig_Action := do
  match arg_ with
  | "Breakpoint" => (pure TA_Breakpoint)
  | "Enter Debug" => (pure TA_Enter_Debug)
  | "Trace On" => (pure TA_Trace_On)
  | "Trace Off" => (pure TA_Trace_Off)
  | "Trace Notify" => (pure TA_Trace_Notify)
  | "External Trigger Output 0" => (pure TA_Ext_Trigger_0)
  | "External Trigger Output 1" => (pure TA_Ext_Trigger_1)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def trigger_action_name_forwards_matches (arg_ : Trig_Action) : Bool :=
  match arg_ with
  | .TA_Breakpoint => true
  | .TA_Enter_Debug => true
  | .TA_Trace_On => true
  | .TA_Trace_Off => true
  | .TA_Trace_Notify => true
  | .TA_Ext_Trigger_0 => true
  | .TA_Ext_Trigger_1 => true

def trigger_action_name_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "Breakpoint" => true
  | "Enter Debug" => true
  | "Trace On" => true
  | "Trace Off" => true
  | "Trace Notify" => true
  | "External Trigger Output 0" => true
  | "External Trigger Output 1" => true
  | _ => false

def is_supported_action (a : (BitVec 6)) : SailM Bool := do
  if ((not (trig_action_forwards_matches a)) : Bool)
  then (pure false)
  else
    (do
      let act ← do (trig_action_forwards a)
      (pure (act == TA_Breakpoint)))

def undefined_Hit (_ : Unit) : SailM Hit := do
  (internal_pick [Hit_false, Hit_before, Hit_after, Hit_imm_after])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def Hit_of_num (arg_ : Nat) : Hit :=
  match arg_ with
  | 0 => Hit_false
  | 1 => Hit_before
  | 2 => Hit_after
  | _ => Hit_imm_after

def num_of_Hit (arg_ : Hit) : Int :=
  match arg_ with
  | .Hit_false => 0
  | .Hit_before => 1
  | .Hit_after => 2
  | .Hit_imm_after => 3

def hit_bits_forwards (arg_ : (BitVec 2)) : Hit :=
  match arg_ with
  | 0b00 => Hit_false
  | 0b01 => Hit_before
  | 0b10 => Hit_after
  | _ => Hit_imm_after

def hit_bits_backwards (arg_ : Hit) : (BitVec 2) :=
  match arg_ with
  | .Hit_false => 0b00#2
  | .Hit_before => 0b01#2
  | .Hit_after => 0b10#2
  | .Hit_imm_after => 0b11#2

def hit_bits_forwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

def hit_bits_backwards_matches (arg_ : Hit) : Bool :=
  match arg_ with
  | .Hit_false => true
  | .Hit_before => true
  | .Hit_after => true
  | .Hit_imm_after => true

def hit_name_forwards (arg_ : Hit) : String :=
  match arg_ with
  | .Hit_false => "not-hit"
  | .Hit_before => "hit-before"
  | .Hit_after => "hit-after"
  | .Hit_imm_after => "hit-imm-after"

def hit_name_backwards (arg_ : String) : SailM Hit := do
  match arg_ with
  | "not-hit" => (pure Hit_false)
  | "hit-before" => (pure Hit_before)
  | "hit-after" => (pure Hit_after)
  | "hit-imm-after" => (pure Hit_imm_after)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hit_name_forwards_matches (arg_ : Hit) : Bool :=
  match arg_ with
  | .Hit_false => true
  | .Hit_before => true
  | .Hit_after => true
  | .Hit_imm_after => true

def hit_name_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "not-hit" => true
  | "hit-before" => true
  | "hit-after" => true
  | "hit-imm-after" => true
  | _ => false

def undefined_Compare_Selection (_ : Unit) : SailM Compare_Selection := do
  (internal_pick [Compare_Address, Compare_Data])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def Compare_Selection_of_num (arg_ : Nat) : Compare_Selection :=
  match arg_ with
  | 0 => Compare_Address
  | _ => Compare_Data

def num_of_Compare_Selection (arg_ : Compare_Selection) : Int :=
  match arg_ with
  | .Compare_Address => 0
  | .Compare_Data => 1

def compare_select_bits_forwards (arg_ : (BitVec 1)) : Compare_Selection :=
  match arg_ with
  | 0 => Compare_Address
  | _ => Compare_Data

def compare_select_bits_backwards (arg_ : Compare_Selection) : (BitVec 1) :=
  match arg_ with
  | .Compare_Address => 0#1
  | .Compare_Data => 1#1

def compare_select_bits_forwards_matches (arg_ : (BitVec 1)) : Bool :=
  match arg_ with
  | 0 => true
  | 1 => true
  | _ => false

def compare_select_bits_backwards_matches (arg_ : Compare_Selection) : Bool :=
  match arg_ with
  | .Compare_Address => true
  | .Compare_Data => true

def trig_match_size_forwards (arg_ : (BitVec 3)) : SailM Int := do
  match arg_ with
  | 0b000 => (pure 0)
  | 0b001 => (pure 8)
  | 0b010 => (pure 16)
  | 0b011 => (pure 32)
  | 0b100 => (pure 48)
  | 0b101 => (pure 64)
  | 0b110 => (pure 128)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [0, 8, 16, 32, 48, 64, 128] -/
def trig_match_size_backwards (arg_ : Nat) : (BitVec 3) :=
  match arg_ with
  | 0 => 0b000#3
  | 8 => 0b001#3
  | 16 => 0b010#3
  | 32 => 0b011#3
  | 48 => 0b100#3
  | 64 => 0b101#3
  | _ => 0b110#3

def trig_match_size_forwards_matches (arg_ : (BitVec 3)) : Bool :=
  match arg_ with
  | 0b000 => true
  | 0b001 => true
  | 0b010 => true
  | 0b011 => true
  | 0b100 => true
  | 0b101 => true
  | 0b110 => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [0, 8, 16, 32, 48, 64, 128] -/
def trig_match_size_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 0 => true
  | 8 => true
  | 16 => true
  | 32 => true
  | 48 => true
  | 64 => true
  | 128 => true
  | _ => false

def is_supported_match_size (s : (BitVec 3)) : Bool :=
  (trig_match_size_forwards_matches s)

def undefined_Trig_Match (_ : Unit) : SailM Trig_Match := do
  (internal_pick
    [TM_EQ, TM_NAPOT, TM_GE, TM_LT, TM_MASK_LO, TM_MASK_HI, TM_NEQ, TM_NOT_NAPOT, TM_NOT_MASK_LO, TM_NOT_MASK_HI])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 9 -/
def Trig_Match_of_num (arg_ : Nat) : Trig_Match :=
  match arg_ with
  | 0 => TM_EQ
  | 1 => TM_NAPOT
  | 2 => TM_GE
  | 3 => TM_LT
  | 4 => TM_MASK_LO
  | 5 => TM_MASK_HI
  | 6 => TM_NEQ
  | 7 => TM_NOT_NAPOT
  | 8 => TM_NOT_MASK_LO
  | _ => TM_NOT_MASK_HI

def num_of_Trig_Match (arg_ : Trig_Match) : Int :=
  match arg_ with
  | .TM_EQ => 0
  | .TM_NAPOT => 1
  | .TM_GE => 2
  | .TM_LT => 3
  | .TM_MASK_LO => 4
  | .TM_MASK_HI => 5
  | .TM_NEQ => 6
  | .TM_NOT_NAPOT => 7
  | .TM_NOT_MASK_LO => 8
  | .TM_NOT_MASK_HI => 9

def trig_match_val_forwards (arg_ : (BitVec 4)) : SailM Trig_Match := do
  match arg_ with
  | 0b0000 => (pure TM_EQ)
  | 0b0001 => (pure TM_NAPOT)
  | 0b0010 => (pure TM_GE)
  | 0b0011 => (pure TM_LT)
  | 0b0100 => (pure TM_MASK_LO)
  | 0b0101 => (pure TM_MASK_HI)
  | 0b1000 => (pure TM_NEQ)
  | 0b1001 => (pure TM_NOT_NAPOT)
  | 0b1100 => (pure TM_NOT_MASK_LO)
  | 0b1101 => (pure TM_NOT_MASK_HI)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def trig_match_val_backwards (arg_ : Trig_Match) : (BitVec 4) :=
  match arg_ with
  | .TM_EQ => 0b0000#4
  | .TM_NAPOT => 0b0001#4
  | .TM_GE => 0b0010#4
  | .TM_LT => 0b0011#4
  | .TM_MASK_LO => 0b0100#4
  | .TM_MASK_HI => 0b0101#4
  | .TM_NEQ => 0b1000#4
  | .TM_NOT_NAPOT => 0b1001#4
  | .TM_NOT_MASK_LO => 0b1100#4
  | .TM_NOT_MASK_HI => 0b1101#4

def trig_match_val_forwards_matches (arg_ : (BitVec 4)) : Bool :=
  match arg_ with
  | 0b0000 => true
  | 0b0001 => true
  | 0b0010 => true
  | 0b0011 => true
  | 0b0100 => true
  | 0b0101 => true
  | 0b1000 => true
  | 0b1001 => true
  | 0b1100 => true
  | 0b1101 => true
  | _ => false

def trig_match_val_backwards_matches (arg_ : Trig_Match) : Bool :=
  match arg_ with
  | .TM_EQ => true
  | .TM_NAPOT => true
  | .TM_GE => true
  | .TM_LT => true
  | .TM_MASK_LO => true
  | .TM_MASK_HI => true
  | .TM_NEQ => true
  | .TM_NOT_NAPOT => true
  | .TM_NOT_MASK_LO => true
  | .TM_NOT_MASK_HI => true

def is_supported_match_val (m : (BitVec 4)) : Bool :=
  (trig_match_val_forwards_matches m)

def undefined_TDisabled (_ : Unit) : SailM TDisabled := do
  (pure { dmode := ← (undefined_bool ())
          data := ← (undefined_bitvector (32 -i 5))
          tdata2 := ← (undefined_bitvector 32)
          tdata3 := ← (undefined_bitvector 32) })

def undefined_TDisabled_bits (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_TDisabled_bits (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_TDisabled_bits_data (v : (BitVec 32)) : (BitVec (32 - 5)) :=
  (Sail.BitVec.extractLsb v (32 -i 6) 0)

def _update_TDisabled_bits_data (v : (BitVec 32)) (x : (BitVec (32 - 5))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 6) 0 x)

def _update_SContext_data (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_TData1_data (v : (BitVec 32)) (x : (BitVec (32 - 5))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 6) 0 x)

def _set_TDisabled_bits_data (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 5))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TDisabled_bits_data r v)

def _get_SContext_data (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _get_TData1_data (v : (BitVec 32)) : (BitVec (32 - 5)) :=
  (Sail.BitVec.extractLsb v (32 -i 6) 0)

def _set_SContext_data (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SContext_data r v)

def _set_TData1_data (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 5))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TData1_data r v)

def _get_TDisabled_bits_dmode (v : (BitVec 32)) : (BitVec (32 - 5 - (32 - 5) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 5) (32 -i 5))

def _update_TDisabled_bits_dmode (v : (BitVec 32)) (x : (BitVec (32 - 5 - (32 - 5) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 5) (32 -i 5) x)

def _update_External_Trigger_dmode (v : (BitVec 32)) (x : (BitVec (32 - 5 - (32 - 5) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 5) (32 -i 5) x)

def _update_ICount_bits_dmode (v : (BitVec 32)) (x : (BitVec (32 - 5 - (32 - 5) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 5) (32 -i 5) x)

def _update_IETrigger_bits_dmode (v : (BitVec 32)) (x : (BitVec (32 - 5 - (32 - 5) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 5) (32 -i 5) x)

def _update_MControl6_bits_dmode (v : (BitVec 32)) (x : (BitVec (32 - 5 - (32 - 5) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 5) (32 -i 5) x)

def _update_TData1_dmode (v : (BitVec 32)) (x : (BitVec (32 - 5 - (32 - 5) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 5) (32 -i 5) x)

def _set_TDisabled_bits_dmode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 5 - (32 - 5) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TDisabled_bits_dmode r v)

def _get_External_Trigger_dmode (v : (BitVec 32)) : (BitVec (32 - 5 - (32 - 5) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 5) (32 -i 5))

def _get_ICount_bits_dmode (v : (BitVec 32)) : (BitVec (32 - 5 - (32 - 5) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 5) (32 -i 5))

def _get_IETrigger_bits_dmode (v : (BitVec 32)) : (BitVec (32 - 5 - (32 - 5) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 5) (32 -i 5))

def _get_MControl6_bits_dmode (v : (BitVec 32)) : (BitVec (32 - 5 - (32 - 5) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 5) (32 -i 5))

def _get_TData1_dmode (v : (BitVec 32)) : (BitVec (32 - 5 - (32 - 5) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 5) (32 -i 5))

def _set_External_Trigger_dmode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 5 - (32 - 5) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_External_Trigger_dmode r v)

def _set_ICount_bits_dmode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 5 - (32 - 5) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICount_bits_dmode r v)

def _set_IETrigger_bits_dmode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 5 - (32 - 5) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IETrigger_bits_dmode r v)

def _set_MControl6_bits_dmode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 5 - (32 - 5) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_dmode r v)

def _set_TData1_dmode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 5 - (32 - 5) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TData1_dmode r v)

def _get_TDisabled_bits_trig_type (v : (BitVec 32)) : (BitVec (32 - 1 - (32 - 4) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 1) (32 -i 4))

def _update_TDisabled_bits_trig_type (v : (BitVec 32)) (x : (BitVec (32 - 1 - (32 - 4) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) (32 -i 4) x)

def _update_External_Trigger_trig_type (v : (BitVec 32)) (x : (BitVec (32 - 1 - (32 - 4) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) (32 -i 4) x)

def _update_ICount_bits_trig_type (v : (BitVec 32)) (x : (BitVec (32 - 1 - (32 - 4) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) (32 -i 4) x)

def _update_IETrigger_bits_trig_type (v : (BitVec 32)) (x : (BitVec (32 - 1 - (32 - 4) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) (32 -i 4) x)

def _update_MControl6_bits_trig_type (v : (BitVec 32)) (x : (BitVec (32 - 1 - (32 - 4) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) (32 -i 4) x)

def _update_TData1_trig_type (v : (BitVec 32)) (x : (BitVec (32 - 1 - (32 - 4) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) (32 -i 4) x)

def _set_TDisabled_bits_trig_type (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 1 - (32 - 4) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TDisabled_bits_trig_type r v)

def _get_External_Trigger_trig_type (v : (BitVec 32)) : (BitVec (32 - 1 - (32 - 4) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 1) (32 -i 4))

def _get_ICount_bits_trig_type (v : (BitVec 32)) : (BitVec (32 - 1 - (32 - 4) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 1) (32 -i 4))

def _get_IETrigger_bits_trig_type (v : (BitVec 32)) : (BitVec (32 - 1 - (32 - 4) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 1) (32 -i 4))

def _get_MControl6_bits_trig_type (v : (BitVec 32)) : (BitVec (32 - 1 - (32 - 4) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 1) (32 -i 4))

def _get_TData1_trig_type (v : (BitVec 32)) : (BitVec (32 - 1 - (32 - 4) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 1) (32 -i 4))

def _set_External_Trigger_trig_type (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 1 - (32 - 4) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_External_Trigger_trig_type r v)

def _set_ICount_bits_trig_type (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 1 - (32 - 4) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICount_bits_trig_type r v)

def _set_IETrigger_bits_trig_type (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 1 - (32 - 4) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IETrigger_bits_trig_type r v)

def _set_MControl6_bits_trig_type (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 1 - (32 - 4) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_trig_type r v)

def _set_TData1_trig_type (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 1 - (32 - 4) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TData1_trig_type r v)

def TDisabled_to_bits (t : TDisabled) : SailM (BitVec 32) := do
  (pure (_update_TDisabled_bits_data
      (_update_TDisabled_bits_dmode
        (_update_TDisabled_bits_trig_type (Mk_TDisabled_bits (zeros (n := 32)))
          (← (trig_type_bits_backwards TT_disabled))) (bool_bit_forwards t.dmode)) t.data))

def undefined_MControl6_bits (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_MControl6_bits (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_MControl6_bits_action (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_MControl6_bits_action (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_External_Trigger_action (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ICount_bits_action (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _update_IETrigger_bits_action (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _set_MControl6_bits_action (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_action r v)

def _get_External_Trigger_action (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICount_bits_action (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)

def _get_IETrigger_bits_action (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)

def _set_External_Trigger_action (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_External_Trigger_action r v)

def _set_ICount_bits_action (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICount_bits_action r v)

def _set_IETrigger_bits_action (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IETrigger_bits_action r v)

def _get_MControl6_bits_chain (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_MControl6_bits_chain (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _set_MControl6_bits_chain (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_chain r v)

def _get_MControl6_bits_execute (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_MControl6_bits_execute (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _set_MControl6_bits_execute (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_execute r v)

def _get_MControl6_bits_hit0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_MControl6_bits_hit0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _set_MControl6_bits_hit0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_hit0 r v)

def _get_MControl6_bits_hit1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_MControl6_bits_hit1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _set_MControl6_bits_hit1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_hit1 r v)

def _get_MControl6_bits_load (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_MControl6_bits_load (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_MControl6_bits_load (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_load r v)

def _get_MControl6_bits_m (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_MControl6_bits_m (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ICount_bits_m (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_IETrigger_bits_m (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _set_MControl6_bits_m (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_m r v)

def _get_ICount_bits_m (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_IETrigger_bits_m (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _set_ICount_bits_m (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICount_bits_m r v)

def _set_IETrigger_bits_m (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IETrigger_bits_m r v)

def _get_MControl6_bits_s (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_MControl6_bits_s (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_ICount_bits_s (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_IETrigger_bits_s (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_MControl6_bits_s (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_s r v)

def _get_ICount_bits_s (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_IETrigger_bits_s (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _set_ICount_bits_s (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICount_bits_s r v)

def _set_IETrigger_bits_s (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IETrigger_bits_s r v)

def _get_MControl6_bits_select (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_MControl6_bits_select (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_External_Trigger_select (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _set_MControl6_bits_select (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_select r v)

def _get_External_Trigger_select (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _set_External_Trigger_select (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_External_Trigger_select r v)

def _get_MControl6_bits_size (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 18 16)

def _update_MControl6_bits_size (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 16 x)

def _set_MControl6_bits_size (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_size r v)

def _get_MControl6_bits_store (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_MControl6_bits_store (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_MControl6_bits_store (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_store r v)

def _get_MControl6_bits_t_match (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 10 7)

def _update_MControl6_bits_t_match (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 7 x)

def _set_MControl6_bits_t_match (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_t_match r v)

def _get_MControl6_bits_u (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_MControl6_bits_u (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICount_bits_u (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_IETrigger_bits_u (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _set_MControl6_bits_u (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_u r v)

def _get_ICount_bits_u (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_IETrigger_bits_u (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _set_ICount_bits_u (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICount_bits_u r v)

def _set_IETrigger_bits_u (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IETrigger_bits_u r v)

def _get_MControl6_bits_uncertain (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_MControl6_bits_uncertain (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _set_MControl6_bits_uncertain (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_uncertain r v)

def _get_MControl6_bits_uncertainen (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_MControl6_bits_uncertainen (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_MControl6_bits_uncertainen (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_uncertainen r v)

def _get_MControl6_bits_vs (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_MControl6_bits_vs (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_ICount_bits_vs (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_IETrigger_bits_vs (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _set_MControl6_bits_vs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_vs r v)

def _get_ICount_bits_vs (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_IETrigger_bits_vs (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _set_ICount_bits_vs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICount_bits_vs r v)

def _set_IETrigger_bits_vs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IETrigger_bits_vs r v)

def _get_MControl6_bits_vu (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_MControl6_bits_vu (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_ICount_bits_vu (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_IETrigger_bits_vu (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _set_MControl6_bits_vu (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_vu r v)

def _get_ICount_bits_vu (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_IETrigger_bits_vu (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _set_ICount_bits_vu (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICount_bits_vu r v)

def _set_IETrigger_bits_vu (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IETrigger_bits_vu r v)

def MControl6_to_bits (t : MControl6) : SailM (BitVec 32) := do
  let hit := (hit_bits_backwards t.hit)
  (pure (_update_MControl6_bits_load
      (_update_MControl6_bits_store
        (_update_MControl6_bits_execute
          (_update_MControl6_bits_u
            (_update_MControl6_bits_s
              (_update_MControl6_bits_uncertainen
                (_update_MControl6_bits_m
                  (_update_MControl6_bits_t_match
                    (_update_MControl6_bits_chain
                      (_update_MControl6_bits_action
                        (_update_MControl6_bits_size
                          (_update_MControl6_bits_select
                            (_update_MControl6_bits_hit0
                              (_update_MControl6_bits_vu
                                (_update_MControl6_bits_vs
                                  (_update_MControl6_bits_hit1
                                    (_update_MControl6_bits_uncertain
                                      (_update_MControl6_bits_dmode
                                        (_update_MControl6_bits_trig_type
                                          (Mk_MControl6_bits (zeros (n := 32)))
                                          (← (trig_type_bits_backwards TT_mcontrol6)))
                                        (bool_bit_forwards t.dmode)) (bool_bit_forwards t.uncertain))
                                    (BitVec.join1 [(BitVec.access hit 1)])) (bool_bit_forwards t.vs))
                                (bool_bit_forwards t.vu)) (BitVec.join1 [(BitVec.access hit 0)]))
                            (compare_select_bits_backwards t.select))
                          (trig_match_size_backwards t.size))
                        (Sail.BitVec.extractLsb (trig_action_backwards t.action) 3 0))
                      (bool_bit_forwards t.chain)) (trig_match_val_backwards t.t_match))
                  (bool_bit_forwards t.m)) (bool_bit_forwards t.uncertainen))
              (bool_bit_forwards t.s)) (bool_bit_forwards t.u)) (bool_bit_forwards t.execute))
        (bool_bit_forwards t.store)) (bool_bit_forwards t.load)))

def icount_count_is_hardwired_one : Bool := false

def icount_self_write_sets_pending : Bool := true

def undefined_ICount_bits (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ICount_bits (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_ICount_bits_count (v : (BitVec 32)) : (BitVec 14) :=
  (Sail.BitVec.extractLsb v 23 10)

def _update_ICount_bits_count (v : (BitVec 32)) (x : (BitVec 14)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 10 x)

def _set_ICount_bits_count (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 14)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICount_bits_count r v)

def _get_ICount_bits_hit (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_ICount_bits_hit (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_External_Trigger_hit (v : (BitVec 32)) (x : (BitVec (32 - 6 - (32 - 6) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 6) (32 -i 6) x)

def _update_IETrigger_bits_hit (v : (BitVec 32)) (x : (BitVec (32 - 6 - (32 - 6) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 6) (32 -i 6) x)

def _set_ICount_bits_hit (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICount_bits_hit r v)

def _get_External_Trigger_hit (v : (BitVec 32)) : (BitVec (32 - 6 - (32 - 6) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 6) (32 -i 6))

def _get_IETrigger_bits_hit (v : (BitVec 32)) : (BitVec (32 - 6 - (32 - 6) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 6) (32 -i 6))

def _set_External_Trigger_hit (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 6 - (32 - 6) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_External_Trigger_hit r v)

def _set_IETrigger_bits_hit (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 6 - (32 - 6) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IETrigger_bits_hit r v)

def _get_ICount_bits_pending (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_ICount_bits_pending (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _set_ICount_bits_pending (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICount_bits_pending r v)

def ICount_to_bits (t : ICount) : SailM (BitVec 32) := do
  (pure (_update_ICount_bits_action
      (_update_ICount_bits_u
        (_update_ICount_bits_s
          (_update_ICount_bits_pending
            (_update_ICount_bits_m
              (_update_ICount_bits_count
                (_update_ICount_bits_hit
                  (_update_ICount_bits_vu
                    (_update_ICount_bits_vs
                      (_update_ICount_bits_dmode
                        (_update_ICount_bits_trig_type (Mk_ICount_bits (zeros (n := 32)))
                          (← (trig_type_bits_backwards TT_icount))) (bool_bit_forwards t.dmode))
                      (bool_bit_forwards t.vs)) (bool_bit_forwards t.vu)) (bool_bit_forwards t.hit))
                t.count) (bool_bit_forwards t.m)) (bool_bit_forwards t.pending))
          (bool_bit_forwards t.s)) (bool_bit_forwards t.u))
      (zero_extend (m := 6) (trig_action_backwards t.action))))

def undefined_ITrigger (_ : Unit) : SailM ITrigger := do
  (pure { dmode := ← (undefined_bool ())
          hit := ← (undefined_bool ())
          vs := ← (undefined_bool ())
          vu := ← (undefined_bool ())
          nmi := ← (undefined_bool ())
          m := ← (undefined_bool ())
          s := ← (undefined_bool ())
          u := ← (undefined_bool ())
          action := ← (undefined_Trig_Action ())
          tdata2 := ← (undefined_bitvector 32)
          tdata3 := ← (undefined_bitvector 32)
          pending := ← (undefined_bool ()) })

def undefined_ETrigger (_ : Unit) : SailM ETrigger := do
  (pure { dmode := ← (undefined_bool ())
          hit := ← (undefined_bool ())
          vs := ← (undefined_bool ())
          vu := ← (undefined_bool ())
          m := ← (undefined_bool ())
          s := ← (undefined_bool ())
          u := ← (undefined_bool ())
          action := ← (undefined_Trig_Action ())
          tdata2 := ← (undefined_bitvector 32)
          tdata3 := ← (undefined_bitvector 32)
          pending := ← (undefined_bool ()) })

def undefined_IETrigger_bits (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_IETrigger_bits (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_IETrigger_bits_nmi (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_IETrigger_bits_nmi (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _set_IETrigger_bits_nmi (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IETrigger_bits_nmi r v)

def ITrigger_to_bits (t : ITrigger) : SailM (BitVec 32) := do
  (pure (_update_IETrigger_bits_action
      (_update_IETrigger_bits_u
        (_update_IETrigger_bits_s
          (_update_IETrigger_bits_m
            (_update_IETrigger_bits_nmi
              (_update_IETrigger_bits_vu
                (_update_IETrigger_bits_vs
                  (_update_IETrigger_bits_hit
                    (_update_IETrigger_bits_dmode
                      (_update_IETrigger_bits_trig_type (Mk_IETrigger_bits (zeros (n := 32)))
                        (← (trig_type_bits_backwards TT_itrigger))) (bool_bit_forwards t.dmode))
                    (bool_bit_forwards t.hit)) (bool_bit_forwards t.vs)) (bool_bit_forwards t.vu))
              (bool_bit_forwards t.nmi)) (bool_bit_forwards t.m)) (bool_bit_forwards t.s))
        (bool_bit_forwards t.u)) (zero_extend (m := 6) (trig_action_backwards t.action))))

def ETrigger_to_bits (t : ETrigger) : SailM (BitVec 32) := do
  (pure (_update_IETrigger_bits_action
      (_update_IETrigger_bits_u
        (_update_IETrigger_bits_s
          (_update_IETrigger_bits_m
            (_update_IETrigger_bits_nmi
              (_update_IETrigger_bits_vu
                (_update_IETrigger_bits_vs
                  (_update_IETrigger_bits_hit
                    (_update_IETrigger_bits_dmode
                      (_update_IETrigger_bits_trig_type (Mk_IETrigger_bits (zeros (n := 32)))
                        (← (trig_type_bits_backwards TT_etrigger))) (bool_bit_forwards t.dmode))
                    (bool_bit_forwards t.hit)) (bool_bit_forwards t.vs)) (bool_bit_forwards t.vu))
              0#1) (bool_bit_forwards t.m)) (bool_bit_forwards t.s)) (bool_bit_forwards t.u))
      (zero_extend (m := 6) (trig_action_backwards t.action))))

def trigger_name (t : Trigger) : String :=
  match t with
  | .T_disabled _ => "disabled"
  | .T_icount _ => "icount"
  | .T_itrigger _ => "itrigger"
  | .T_etrigger _ => "etrigger"

def trig_reset_val : Trigger :=
  (T_disabled
    { dmode := false
      data := (zeros (n := (32 -i 5)))
      tdata2 := (zeros (n := 32))
      tdata3 := (zeros (n := 32)) })

def tdata1_of_trigger (t : Trigger) : SailM (BitVec 32) := do
  match t with
  | .T_disabled s => (TDisabled_to_bits s)
  | .T_icount s => (ICount_to_bits s)
  | .T_itrigger s => (ITrigger_to_bits s)
  | .T_etrigger s => (ETrigger_to_bits s)

def tdata2_of_trigger (t : Trigger) : (BitVec 32) :=
  match t with
  | .T_disabled s => s.tdata2
  | .T_icount s => s.tdata2
  | .T_itrigger s => s.tdata2
  | .T_etrigger s => s.tdata2

def tdata3_of_trigger (t : Trigger) : (BitVec 32) :=
  match t with
  | .T_disabled s => s.tdata3
  | .T_icount s => s.tdata3
  | .T_itrigger s => s.tdata3
  | .T_etrigger s => s.tdata3

def info_of_trigger (_t : Trigger) : SailM (BitVec 16) := do
  (supported_triggers_info ())

def undefined_TInfo (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_TInfo (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_TInfo_info (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_TInfo_info (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _set_TInfo_info (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TInfo_info r v)

def _get_TInfo_version (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _update_TInfo_version (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _set_TInfo_version (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TInfo_version r v)

def tinfo_of_trigger (t : Trigger) : SailM (BitVec 32) := do
  (pure (_update_TInfo_info (_update_TInfo_version (Mk_TInfo (zeros (n := 32))) 0x01#8)
      (← (info_of_trigger t))))

def undefined_TData1 (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_TData1 (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_TControl (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_TControl (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_TControl_mpte (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_TControl_mpte (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_TControl_mpte (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TControl_mpte r v)

def _get_TControl_mte (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_TControl_mte (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _set_TControl_mte (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TControl_mte r v)

def undefined_SContext (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_SContext (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_MContext (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_MContext (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_MContext_hcontext (v : (BitVec 32)) : (BitVec 14) :=
  (Sail.BitVec.extractLsb v 13 0)

def _update_MContext_hcontext (v : (BitVec 32)) (x : (BitVec 14)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 0 x)

def _set_MContext_hcontext (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 14)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MContext_hcontext r v)

def undefined_External_Trigger (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_External_Trigger (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_External_Trigger_intctl (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_External_Trigger_intctl (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _set_External_Trigger_intctl (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_External_Trigger_intctl r v)

def undefined_Trigger_Extra_RV32 (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Trigger_Extra_RV32 (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_Trigger_Extra_RV32_mhselect (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 25 23)

def _update_Trigger_Extra_RV32_mhselect (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 23 x)

def _update_Trigger_Extra_RV64_mhselect (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 48 x)

def _set_Trigger_Extra_RV32_mhselect (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Trigger_Extra_RV32_mhselect r v)

def _get_Trigger_Extra_RV64_mhselect (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 50 48)

def _set_Trigger_Extra_RV64_mhselect (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Trigger_Extra_RV64_mhselect r v)

def _get_Trigger_Extra_RV32_mhvalue (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 31 26)

def _update_Trigger_Extra_RV32_mhvalue (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 26 x)

def _update_Trigger_Extra_RV64_mhvalue (v : (BitVec 64)) (x : (BitVec 13)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 51 x)

def _set_Trigger_Extra_RV32_mhvalue (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Trigger_Extra_RV32_mhvalue r v)

def _get_Trigger_Extra_RV64_mhvalue (v : (BitVec 64)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 63 51)

def _set_Trigger_Extra_RV64_mhvalue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 13)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Trigger_Extra_RV64_mhvalue r v)

def _get_Trigger_Extra_RV32_sbytemask (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 19 18)

def _update_Trigger_Extra_RV32_sbytemask (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 18 x)

def _update_Trigger_Extra_RV64_sbytemask (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _set_Trigger_Extra_RV32_sbytemask (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Trigger_Extra_RV32_sbytemask r v)

def _get_Trigger_Extra_RV64_sbytemask (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _set_Trigger_Extra_RV64_sbytemask (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Trigger_Extra_RV64_sbytemask r v)

def _get_Trigger_Extra_RV32_sselect (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _update_Trigger_Extra_RV32_sselect (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _update_Trigger_Extra_RV64_sselect (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _set_Trigger_Extra_RV32_sselect (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Trigger_Extra_RV32_sselect r v)

def _get_Trigger_Extra_RV64_sselect (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _set_Trigger_Extra_RV64_sselect (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Trigger_Extra_RV64_sselect r v)

def _get_Trigger_Extra_RV32_svalue (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 17 2)

def _update_Trigger_Extra_RV32_svalue (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 2 x)

def _update_Trigger_Extra_RV64_svalue (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 2 x)

def _set_Trigger_Extra_RV32_svalue (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Trigger_Extra_RV32_svalue r v)

def _get_Trigger_Extra_RV64_svalue (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 33 2)

def _set_Trigger_Extra_RV64_svalue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Trigger_Extra_RV64_svalue r v)

def undefined_Trigger_Extra_RV64 (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Trigger_Extra_RV64 (v : (BitVec 64)) : (BitVec 64) :=
  v

def make_disabled_trigger (tdata1 : (BitVec 32)) (tdata2 : (BitVec 32)) (tdata3 : (BitVec 32)) : Trigger :=
  (T_disabled
    { dmode := false
      data := (_get_TData1_data tdata1)
      tdata2 := tdata2
      tdata3 := tdata3 })

def supported_etrigger_mask : xlenbits := (sail_mask 32 0b00000000111111011011111111111111#32)

def supported_itrigger_mask : xlenbits := (sail_mask 32 0b00000000000000000011111011101110#32)

def make_trigger (tdata1 : (BitVec 32)) (tdata2 : (BitVec 32)) (tdata3 : (BitVec 32)) : SailM Trigger := do
  let tt := (_get_TData1_trig_type tdata1)
  if ((not (is_supported_trigger_type tt)) : Bool)
  then
    (let _ : Unit :=
      if ((get_config_print_trigger ()) : Bool)
      then
        (print_endline
          (HAppend.hAppend "Cannot create unsupported trigger type "
            (HAppend.hAppend (BitVec.toFormatted tt) ".")))
      else ()
    (pure (make_disabled_trigger tdata1 tdata2 tdata3)))
  else
    (do
      let tt := (trig_type_bits_forwards tt)
      match tt with
      | .TT_icount =>
        (do
          let v := (Mk_ICount_bits tdata1)
          let act := (_get_ICount_bits_action v)
          let count :=
            if (icount_count_is_hardwired_one : Bool)
            then (zero_extend (m := 14) 0x1#4)
            else (_get_ICount_bits_count v)
          if ((← (is_supported_action act)) : Bool)
          then
            (pure (T_icount
                { dmode := false
                  vs := ← if ((← (currentlyEnabled Ext_H)) : Bool)
                    then (pure (bool_bit_backwards (_get_ICount_bits_vs v)))
                    else (pure false)
                  vu := ← if ((← (currentlyEnabled Ext_H)) : Bool)
                    then (pure (bool_bit_backwards (_get_ICount_bits_vu v)))
                    else (pure false)
                  hit := (bool_bit_backwards (_get_ICount_bits_hit v))
                  count := count
                  new_count := (some count)
                  m := (bool_bit_backwards (_get_ICount_bits_m v))
                  pending := (bool_bit_backwards (_get_ICount_bits_pending v))
                  s := ← if ((← (currentlyEnabled Ext_S)) : Bool)
                    then (pure (bool_bit_backwards (_get_ICount_bits_s v)))
                    else (pure false)
                  u := ← if ((← (currentlyEnabled Ext_U)) : Bool)
                    then (pure (bool_bit_backwards (_get_ICount_bits_u v)))
                    else (pure false)
                  action := ← (trig_action_forwards act)
                  active := false
                  tdata2 := tdata2
                  tdata3 := tdata3 }))
          else (pure (make_disabled_trigger tdata1 tdata2 tdata3)))
      | .TT_itrigger =>
        (do
          let v := (Mk_IETrigger_bits tdata1)
          let act := (_get_IETrigger_bits_action v)
          if ((← (is_supported_action act)) : Bool)
          then
            (pure (T_itrigger
                { dmode := false
                  hit := (bool_bit_backwards (_get_IETrigger_bits_hit v))
                  vs := ← if ((← (currentlyEnabled Ext_H)) : Bool)
                    then (pure (bool_bit_backwards (_get_IETrigger_bits_vs v)))
                    else (pure false)
                  vu := ← if ((← (currentlyEnabled Ext_H)) : Bool)
                    then (pure (bool_bit_backwards (_get_IETrigger_bits_vu v)))
                    else (pure false)
                  nmi := (bool_bit_backwards (_get_IETrigger_bits_nmi v))
                  m := (bool_bit_backwards (_get_IETrigger_bits_m v))
                  s := ← if ((← (currentlyEnabled Ext_S)) : Bool)
                    then (pure (bool_bit_backwards (_get_IETrigger_bits_s v)))
                    else (pure false)
                  u := ← if ((← (currentlyEnabled Ext_U)) : Bool)
                    then (pure (bool_bit_backwards (_get_IETrigger_bits_u v)))
                    else (pure false)
                  action := ← (trig_action_forwards act)
                  tdata2 := (tdata2 &&& supported_itrigger_mask)
                  tdata3 := tdata3
                  pending := false }))
          else (pure (make_disabled_trigger tdata1 tdata2 tdata3)))
      | .TT_etrigger =>
        (do
          let v := (Mk_IETrigger_bits tdata1)
          let act := (_get_IETrigger_bits_action v)
          if ((← (is_supported_action act)) : Bool)
          then
            (pure (T_etrigger
                { dmode := false
                  hit := (bool_bit_backwards (_get_IETrigger_bits_hit v))
                  vs := ← if ((← (currentlyEnabled Ext_H)) : Bool)
                    then (pure (bool_bit_backwards (_get_IETrigger_bits_vs v)))
                    else (pure false)
                  vu := ← if ((← (currentlyEnabled Ext_H)) : Bool)
                    then (pure (bool_bit_backwards (_get_IETrigger_bits_vu v)))
                    else (pure false)
                  m := (bool_bit_backwards (_get_IETrigger_bits_m v))
                  s := ← if ((← (currentlyEnabled Ext_S)) : Bool)
                    then (pure (bool_bit_backwards (_get_IETrigger_bits_s v)))
                    else (pure false)
                  u := ← if ((← (currentlyEnabled Ext_U)) : Bool)
                    then (pure (bool_bit_backwards (_get_IETrigger_bits_u v)))
                    else (pure false)
                  action := ← (trig_action_forwards act)
                  tdata2 := (tdata2 &&& supported_etrigger_mask)
                  tdata3 := tdata3
                  pending := false }))
          else (pure (make_disabled_trigger tdata1 tdata2 tdata3)))
      | _ =>
        (let _ : Unit :=
          if ((get_config_print_trigger ()) : Bool)
          then
            (print_endline
              (HAppend.hAppend "Creating disabled trigger for type '"
                (HAppend.hAppend (trig_type_name_forwards tt) "'.")))
          else ()
        (pure (make_disabled_trigger tdata1 tdata2 tdata3))))

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ (16 - 1) -/
def trigger_write_tdata1 (idx : Nat) (t : Trigger) (tdata1 : (BitVec 32)) : SailM Trigger := do
  let tdata1_bitfield := (Mk_TData1 tdata1)
  let disable ← do
    (pure ((tdata1 == (zeros (n := 32))) || ((_get_TData1_trig_type tdata1_bitfield) == (← (trig_type_bits_backwards
              TT_disabled)))))
  if (disable : Bool)
  then
    (let newt := (make_disabled_trigger tdata1_bitfield (tdata2_of_trigger t) (tdata3_of_trigger t))
    let _ : Unit :=
      if ((get_config_print_trigger ()) : Bool)
      then
        (print_endline
          (HAppend.hAppend (trigger_name newt)
            (HAppend.hAppend " trigger #"
              (HAppend.hAppend (Int.repr idx)
                (HAppend.hAppend " (was " (HAppend.hAppend (trigger_name t) ")."))))))
      else ()
    (pure newt))
  else
    (do
      match t with
      | .T_disabled s =>
        (do
          let newt ← do (make_trigger tdata1_bitfield s.tdata2 s.tdata3)
          let _ : Unit :=
            if ((get_config_print_trigger ()) : Bool)
            then
              (print_endline
                (HAppend.hAppend (trigger_name newt)
                  (HAppend.hAppend " trigger #"
                    (HAppend.hAppend (Int.repr idx)
                      (HAppend.hAppend ": enabled (was " (HAppend.hAppend (trigger_name t) ")."))))))
            else ()
          (pure newt))
      | .T_icount s =>
        (let data := (Mk_ICount_bits tdata1)
        let hit := (_get_ICount_bits_hit data)
        let pending := (_get_ICount_bits_pending data)
        let count :=
          if (icount_count_is_hardwired_one : Bool)
          then (zero_extend (m := 14) 0x1#4)
          else (_get_ICount_bits_count data)
        let _ : Unit :=
          if ((get_config_print_trigger ()) : Bool)
          then
            (print_endline
              (HAppend.hAppend (trigger_name t)
                (HAppend.hAppend " trigger #"
                  (HAppend.hAppend (Int.repr idx)
                    (HAppend.hAppend ": hit <- "
                      (HAppend.hAppend (BitVec.toFormatted hit)
                        (HAppend.hAppend ", count <- " (BitVec.toFormatted count))))))))
          else ()
        (pure (T_icount
            { s with hit := (bool_bit_backwards hit), pending := (bool_bit_backwards pending), new_count := (some
                count) })))
      | .T_itrigger s =>
        (let data := (Mk_IETrigger_bits tdata1)
        let hit := (_get_IETrigger_bits_hit data)
        let _ : Unit :=
          if ((get_config_print_trigger ()) : Bool)
          then
            (print_endline
              (HAppend.hAppend (trigger_name t)
                (HAppend.hAppend " trigger #"
                  (HAppend.hAppend (Int.repr idx)
                    (HAppend.hAppend ": hit <- " (BitVec.toFormatted hit))))))
          else ()
        (pure (T_itrigger { s with hit := (bool_bit_backwards hit) })))
      | .T_etrigger s =>
        (let data := (Mk_IETrigger_bits tdata1)
        let hit := (_get_IETrigger_bits_hit data)
        let _ : Unit :=
          if ((get_config_print_trigger ()) : Bool)
          then
            (print_endline
              (HAppend.hAppend (trigger_name t)
                (HAppend.hAppend " trigger #"
                  (HAppend.hAppend (Int.repr idx)
                    (HAppend.hAppend ": hit <- " (BitVec.toFormatted hit))))))
          else ()
        (pure (T_etrigger { s with hit := (bool_bit_backwards hit) }))))

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ (16 - 1) -/
def trigger_write_tdata2 (idx : Nat) (t : Trigger) (tdata2 : (BitVec 32)) : Trigger :=
  match t with
  | .T_disabled s =>
    (let _ : Unit :=
      if ((get_config_print_trigger ()) : Bool)
      then
        (print_endline
          (HAppend.hAppend (trigger_name t)
            (HAppend.hAppend " trigger #"
              (HAppend.hAppend (Int.repr idx)
                (HAppend.hAppend ": tdata2 <- " (BitVec.toFormatted tdata2))))))
      else ()
    (T_disabled { s with tdata2 := tdata2 }))
  | _ =>
    (let _ : Unit :=
      if ((get_config_print_trigger ()) : Bool)
      then
        (print_endline
          (HAppend.hAppend (trigger_name t)
            (HAppend.hAppend " trigger #"
              (HAppend.hAppend (Int.repr idx)
                (HAppend.hAppend ": ignoring write to tdata2 of " (BitVec.toFormatted tdata2))))))
      else ()
    t)

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ (16 - 1) -/
def trigger_write_tdata3 (idx : Nat) (t : Trigger) (tdata3 : (BitVec 32)) : Trigger :=
  match t with
  | .T_disabled s =>
    (let _ : Unit :=
      if ((get_config_print_trigger ()) : Bool)
      then
        (print_endline
          (HAppend.hAppend (trigger_name t)
            (HAppend.hAppend " trigger #"
              (HAppend.hAppend (Int.repr idx)
                (HAppend.hAppend ": tdata3 <- " (BitVec.toFormatted tdata3))))))
      else ()
    (T_disabled { s with tdata3 := (zeros (n := 32)) }))
  | _ =>
    (let _ : Unit :=
      if ((get_config_print_trigger ()) : Bool)
      then
        (print_endline
          (HAppend.hAppend (trigger_name t)
            (HAppend.hAppend " trigger #"
              (HAppend.hAppend (Int.repr idx)
                (HAppend.hAppend ": ignoring write to tdata3 of " (BitVec.toFormatted tdata3))))))
      else ()
    t)

