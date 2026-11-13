import SailRV32.Prelude
import SailRV32.Errors
import SailRV32.TypesExt

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

def pagesize_bits := 12

def regidx_bits (app_0 : regidx) : (BitVec (if ( false  : Bool) then 4 else 5)) :=
  let .Regidx b := app_0
  b

def creg2reg_idx (app_0 : cregidx) : regidx :=
  let .Cregidx i := app_0
  (Regidx (zero_extend (m := 5) (1#1 +++ i)))

def undefined_Architecture (_ : Unit) : SailM Architecture := do
  (internal_pick [RV32, RV64, RV128])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Architecture_of_num (arg_ : Nat) : Architecture :=
  match arg_ with
  | 0 => RV32
  | 1 => RV64
  | _ => RV128

def num_of_Architecture (arg_ : Architecture) : Int :=
  match arg_ with
  | .RV32 => 0
  | .RV64 => 1
  | .RV128 => 2

def architecture_bits_forwards_matches (arg_ : Architecture) : Bool :=
  match arg_ with
  | .RV32 => true
  | .RV64 => true
  | .RV128 => true

def architecture_bits_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | 0b00 => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def Privilege_of_num (arg_ : Nat) : Privilege :=
  match arg_ with
  | 0 => User
  | 1 => VirtualUser
  | 2 => Supervisor
  | 3 => VirtualSupervisor
  | _ => Machine

def num_of_Privilege (arg_ : Privilege) : Int :=
  match arg_ with
  | .User => 0
  | .VirtualUser => 1
  | .Supervisor => 2
  | .VirtualSupervisor => 3
  | .Machine => 4

def privLevel_bits_forwards (arg_ : ((BitVec 2) × (BitVec 1))) : SailM Privilege := do
  match arg_ with
  | (0b00, 0) => (pure User)
  | (0b00, 1) => (pure VirtualUser)
  | (0b01, 0) => (pure Supervisor)
  | (0b01, 1) => (pure VirtualSupervisor)
  | (0b11, 0) => (pure Machine)
  | _ => (internal_error "core/types.sail" 79 "Invalid privilege level or virtual mode")

def privLevel_bits_backwards (arg_ : Privilege) : ((BitVec 2) × (BitVec 1)) :=
  match arg_ with
  | .User => (0b00#2, 0#1)
  | .VirtualUser => (0b00#2, 1#1)
  | .Supervisor => (0b01#2, 0#1)
  | .VirtualSupervisor => (0b01#2, 1#1)
  | .Machine => (0b11#2, 0#1)

def privLevel_bits_forwards_matches (arg_ : ((BitVec 2) × (BitVec 1))) : Bool :=
  match arg_ with
  | (0b00, 0) => true
  | (0b00, 1) => true
  | (0b01, 0) => true
  | (0b01, 1) => true
  | (0b11, 0) => true
  | _ => true

def privLevel_bits_backwards_matches (arg_ : Privilege) : Bool :=
  match arg_ with
  | .User => true
  | .VirtualUser => true
  | .Supervisor => true
  | .VirtualSupervisor => true
  | .Machine => true

def privLevel_to_bits (p : Privilege) : (BitVec 2) :=
  let (p, _) := (privLevel_bits_backwards p)
  p

def privLevel_to_virt_bit (p : Privilege) : (BitVec 1) :=
  let (_, v) := (privLevel_bits_backwards p)
  v

/-- Type quantifiers: k_a : Type -/
def is_load_store (access : (MemoryAccessType k_a)) : Bool :=
  match access with
  | .Load _ => true
  | .Store _ => true
  | .LoadReserved _ => true
  | .LoadExecute _ => true
  | .StoreConditional _ => true
  | .Atomic _ => true
  | .InstructionFetch _ => false
  | .CacheAccess _ => true

/-- Type quantifiers: k_a : Type -/
def is_prefetch_access (access : (MemoryAccessType k_a)) : Bool :=
  match access with
  | .CacheAccess (.CB_prefetch _) => true
  | _ => false

/-- Type quantifiers: k_a : Type -/
def is_load_reserved (access : (MemoryAccessType k_a)) : Bool :=
  match access with
  | .LoadReserved _ => true
  | _ => false

/-- Type quantifiers: k_a : Type -/
def is_store_conditional (access : (MemoryAccessType k_a)) : Bool :=
  match access with
  | .StoreConditional _ => true
  | _ => false

def undefined_CSRAccessType (_ : Unit) : SailM CSRAccessType := do
  (internal_pick [CSRRead, CSRWrite, CSRReadWrite])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def CSRAccessType_of_num (arg_ : Nat) : CSRAccessType :=
  match arg_ with
  | 0 => CSRRead
  | 1 => CSRWrite
  | _ => CSRReadWrite

def num_of_CSRAccessType (arg_ : CSRAccessType) : Int :=
  match arg_ with
  | .CSRRead => 0
  | .CSRWrite => 1
  | .CSRReadWrite => 2

def undefined_InterruptType (_ : Unit) : SailM InterruptType := do
  (internal_pick
    [I_Reserved_0, I_S_Software, I_VS_Software, I_M_Software, I_Reserved_4, I_S_Timer, I_VS_Timer, I_M_Timer, I_Reserved_8, I_S_External, I_VS_External, I_M_External, I_SG_External, I_COF, I_Reserved_14, I_Reserved_15])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 15 -/
def InterruptType_of_num (arg_ : Nat) : InterruptType :=
  match arg_ with
  | 0 => I_Reserved_0
  | 1 => I_S_Software
  | 2 => I_VS_Software
  | 3 => I_M_Software
  | 4 => I_Reserved_4
  | 5 => I_S_Timer
  | 6 => I_VS_Timer
  | 7 => I_M_Timer
  | 8 => I_Reserved_8
  | 9 => I_S_External
  | 10 => I_VS_External
  | 11 => I_M_External
  | 12 => I_SG_External
  | 13 => I_COF
  | 14 => I_Reserved_14
  | _ => I_Reserved_15

def num_of_InterruptType (arg_ : InterruptType) : Int :=
  match arg_ with
  | .I_Reserved_0 => 0
  | .I_S_Software => 1
  | .I_VS_Software => 2
  | .I_M_Software => 3
  | .I_Reserved_4 => 4
  | .I_S_Timer => 5
  | .I_VS_Timer => 6
  | .I_M_Timer => 7
  | .I_Reserved_8 => 8
  | .I_S_External => 9
  | .I_VS_External => 10
  | .I_M_External => 11
  | .I_SG_External => 12
  | .I_COF => 13
  | .I_Reserved_14 => 14
  | .I_Reserved_15 => 15

def interruptType_bits_forwards (arg_ : InterruptType) : (BitVec 6) :=
  match arg_ with
  | .I_Reserved_0 => 0b000000#6
  | .I_S_Software => 0b000001#6
  | .I_VS_Software => 0b000010#6
  | .I_M_Software => 0b000011#6
  | .I_Reserved_4 => 0b000100#6
  | .I_S_Timer => 0b000101#6
  | .I_VS_Timer => 0b000110#6
  | .I_M_Timer => 0b000111#6
  | .I_Reserved_8 => 0b001000#6
  | .I_S_External => 0b001001#6
  | .I_VS_External => 0b001010#6
  | .I_M_External => 0b001011#6
  | .I_SG_External => 0b001100#6
  | .I_COF => 0b001101#6
  | .I_Reserved_14 => 0b001110#6
  | .I_Reserved_15 => 0b001111#6

def interruptType_bits_backwards (arg_ : (BitVec 6)) : SailM InterruptType := do
  match arg_ with
  | 0b000000 => (pure I_Reserved_0)
  | 0b000001 => (pure I_S_Software)
  | 0b000010 => (pure I_VS_Software)
  | 0b000011 => (pure I_M_Software)
  | 0b000100 => (pure I_Reserved_4)
  | 0b000101 => (pure I_S_Timer)
  | 0b000110 => (pure I_VS_Timer)
  | 0b000111 => (pure I_M_Timer)
  | 0b001000 => (pure I_Reserved_8)
  | 0b001001 => (pure I_S_External)
  | 0b001010 => (pure I_VS_External)
  | 0b001011 => (pure I_M_External)
  | 0b001100 => (pure I_SG_External)
  | 0b001101 => (pure I_COF)
  | 0b001110 => (pure I_Reserved_14)
  | 0b001111 => (pure I_Reserved_15)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def interruptType_bits_forwards_matches (arg_ : InterruptType) : Bool :=
  match arg_ with
  | .I_Reserved_0 => true
  | .I_S_Software => true
  | .I_VS_Software => true
  | .I_M_Software => true
  | .I_Reserved_4 => true
  | .I_S_Timer => true
  | .I_VS_Timer => true
  | .I_M_Timer => true
  | .I_Reserved_8 => true
  | .I_S_External => true
  | .I_VS_External => true
  | .I_M_External => true
  | .I_SG_External => true
  | .I_COF => true
  | .I_Reserved_14 => true
  | .I_Reserved_15 => true

def interruptType_bits_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b000000 => true
  | 0b000001 => true
  | 0b000010 => true
  | 0b000011 => true
  | 0b000100 => true
  | 0b000101 => true
  | 0b000110 => true
  | 0b000111 => true
  | 0b001000 => true
  | 0b001001 => true
  | 0b001010 => true
  | 0b001011 => true
  | 0b001100 => true
  | 0b001101 => true
  | 0b001110 => true
  | 0b001111 => true
  | _ => false

def is_reserved_interrupt (i : InterruptType) : Bool :=
  match i with
  | .I_Reserved_0 => true
  | .I_Reserved_4 => true
  | .I_Reserved_8 => true
  | .I_Reserved_14 => true
  | .I_Reserved_15 => true
  | _ => false

def is_hypervisor_interrupt (i : InterruptType) : Bool :=
  match i with
  | .I_VS_Software => true
  | .I_VS_Timer => true
  | .I_VS_External => true
  | .I_SG_External => true
  | _ => false

def undefined_breakpoint_cause (_ : Unit) : SailM breakpoint_cause := do
  (internal_pick [Brk_Software, Brk_Hardware])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def breakpoint_cause_of_num (arg_ : Nat) : breakpoint_cause :=
  match arg_ with
  | 0 => Brk_Software
  | _ => Brk_Hardware

def num_of_breakpoint_cause (arg_ : breakpoint_cause) : Int :=
  match arg_ with
  | .Brk_Software => 0
  | .Brk_Hardware => 1

def exceptionType_bits_forwards (arg_ : ExceptionType) : (BitVec 6) :=
  match arg_ with
  | .E_Fetch_Addr_Align () => 0b000000#6
  | .E_Fetch_Access_Fault () => 0b000001#6
  | .E_Illegal_Instr () => 0b000010#6
  | .E_Load_Addr_Align () => 0b000100#6
  | .E_Load_Access_Fault () => 0b000101#6
  | .E_SAMO_Addr_Align () => 0b000110#6
  | .E_SAMO_Access_Fault () => 0b000111#6
  | .E_U_EnvCall () => 0b001000#6
  | .E_S_EnvCall () => 0b001001#6
  | .E_VS_EnvCall () => 0b001010#6
  | .E_M_EnvCall () => 0b001011#6
  | .E_Fetch_Page_Fault () => 0b001100#6
  | .E_Load_Page_Fault () => 0b001101#6
  | .E_Reserved_14 () => 0b001110#6
  | .E_SAMO_Page_Fault () => 0b001111#6
  | .E_Double_Trap () => 0b010000#6
  | .E_Reserved_17 () => 0b010001#6
  | .E_Software_Check () => 0b010010#6
  | .E_Hardware_Error () => 0b010011#6
  | .E_Fetch_GPage_Fault () => 0b010100#6
  | .E_Load_GPage_Fault () => 0b010101#6
  | .E_Virtual_Instr () => 0b010110#6
  | .E_SAMO_GPage_Fault () => 0b010111#6
  | .E_Breakpoint .Brk_Software => 0b000011#6
  | .E_Breakpoint .Brk_Hardware => 0b000011#6
  | .E_Extension e => (ext_exc_type_bits_forwards e)

def exceptionType_bits_backwards (arg_ : (BitVec 6)) : SailM ExceptionType := do
  let head_exp_ := arg_
  match (← do
    match head_exp_ with
    | 0b000000 => (pure (some (E_Fetch_Addr_Align ())))
    | 0b000001 => (pure (some (E_Fetch_Access_Fault ())))
    | 0b000010 => (pure (some (E_Illegal_Instr ())))
    | 0b000100 => (pure (some (E_Load_Addr_Align ())))
    | 0b000101 => (pure (some (E_Load_Access_Fault ())))
    | 0b000110 => (pure (some (E_SAMO_Addr_Align ())))
    | 0b000111 => (pure (some (E_SAMO_Access_Fault ())))
    | 0b001000 => (pure (some (E_U_EnvCall ())))
    | 0b001001 => (pure (some (E_S_EnvCall ())))
    | 0b001010 => (pure (some (E_VS_EnvCall ())))
    | 0b001011 => (pure (some (E_M_EnvCall ())))
    | 0b001100 => (pure (some (E_Fetch_Page_Fault ())))
    | 0b001101 => (pure (some (E_Load_Page_Fault ())))
    | 0b001110 => (pure (some (E_Reserved_14 ())))
    | 0b001111 => (pure (some (E_SAMO_Page_Fault ())))
    | 0b010000 => (pure (some (E_Double_Trap ())))
    | 0b010001 => (pure (some (E_Reserved_17 ())))
    | 0b010010 => (pure (some (E_Software_Check ())))
    | 0b010011 => (pure (some (E_Hardware_Error ())))
    | 0b010100 => (pure (some (E_Fetch_GPage_Fault ())))
    | 0b010101 => (pure (some (E_Load_GPage_Fault ())))
    | 0b010110 => (pure (some (E_Virtual_Instr ())))
    | 0b010111 => (pure (some (E_SAMO_GPage_Fault ())))
    | 0b000011 => (pure (some (E_Breakpoint Brk_Software)))
    | mapping0_ =>
      (do
        if ((ext_exc_type_bits_backwards_matches mapping0_) : Bool)
        then
          (do
            match (← (ext_exc_type_bits_backwards mapping0_)) with
            | e => (pure (some (E_Extension e))))
        else (pure none))) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def exceptionType_bits_forwards_matches (arg_ : ExceptionType) : Bool :=
  match arg_ with
  | .E_Fetch_Addr_Align () => true
  | .E_Fetch_Access_Fault () => true
  | .E_Illegal_Instr () => true
  | .E_Load_Addr_Align () => true
  | .E_Load_Access_Fault () => true
  | .E_SAMO_Addr_Align () => true
  | .E_SAMO_Access_Fault () => true
  | .E_U_EnvCall () => true
  | .E_S_EnvCall () => true
  | .E_VS_EnvCall () => true
  | .E_M_EnvCall () => true
  | .E_Fetch_Page_Fault () => true
  | .E_Load_Page_Fault () => true
  | .E_Reserved_14 () => true
  | .E_SAMO_Page_Fault () => true
  | .E_Double_Trap () => true
  | .E_Reserved_17 () => true
  | .E_Software_Check () => true
  | .E_Hardware_Error () => true
  | .E_Fetch_GPage_Fault () => true
  | .E_Load_GPage_Fault () => true
  | .E_Virtual_Instr () => true
  | .E_SAMO_GPage_Fault () => true
  | .E_Breakpoint .Brk_Software => true
  | .E_Breakpoint .Brk_Hardware => true
  | .E_Extension e => true

def exceptionType_bits_backwards_matches (arg_ : (BitVec 6)) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    match head_exp_ with
    | 0b000000 => (pure (some true))
    | 0b000001 => (pure (some true))
    | 0b000010 => (pure (some true))
    | 0b000100 => (pure (some true))
    | 0b000101 => (pure (some true))
    | 0b000110 => (pure (some true))
    | 0b000111 => (pure (some true))
    | 0b001000 => (pure (some true))
    | 0b001001 => (pure (some true))
    | 0b001010 => (pure (some true))
    | 0b001011 => (pure (some true))
    | 0b001100 => (pure (some true))
    | 0b001101 => (pure (some true))
    | 0b001110 => (pure (some true))
    | 0b001111 => (pure (some true))
    | 0b010000 => (pure (some true))
    | 0b010001 => (pure (some true))
    | 0b010010 => (pure (some true))
    | 0b010011 => (pure (some true))
    | 0b010100 => (pure (some true))
    | 0b010101 => (pure (some true))
    | 0b010110 => (pure (some true))
    | 0b010111 => (pure (some true))
    | 0b000011 => (pure (some true))
    | mapping0_ =>
      (do
        if ((ext_exc_type_bits_backwards_matches mapping0_) : Bool)
        then
          (do
            match (← (ext_exc_type_bits_backwards mapping0_)) with
            | e => (pure (some true)))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def is_reserved_or_custom_exception (e : ExceptionType) : Bool :=
  match e with
  | .E_Reserved_14 () => true
  | .E_Reserved_17 () => true
  | .E_Extension _ => true
  | _ => false

def is_hypervisor_exception (e : ExceptionType) : Bool :=
  match e with
  | .E_VS_EnvCall () => true
  | .E_Fetch_GPage_Fault () => true
  | .E_Load_GPage_Fault () => true
  | .E_Virtual_Instr () => true
  | .E_SAMO_GPage_Fault () => true
  | _ => false

def is_guest_page_fault (e : ExceptionType) : Bool :=
  match e with
  | .E_Fetch_GPage_Fault () => true
  | .E_Load_GPage_Fault () => true
  | .E_SAMO_GPage_Fault () => true
  | _ => false

def undefined_SWCheckCodes (_ : Unit) : SailM SWCheckCodes := do
  (internal_pick [LANDING_PAD_FAULT])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 0 -/
def SWCheckCodes_of_num (arg_ : Nat) : SWCheckCodes :=
  match arg_ with
  | _ => LANDING_PAD_FAULT

def num_of_SWCheckCodes (arg_ : SWCheckCodes) : Int :=
  match arg_ with
  | .LANDING_PAD_FAULT => 0

def sw_check_code_to_bits (c : SWCheckCodes) : (BitVec 32) :=
  match c with
  | .LANDING_PAD_FAULT => (zero_extend (m := 32) 0b010#3)

def trapCause_bits (c : TrapCause) : (BitVec 6) :=
  match c with
  | .Interrupt i => (interruptType_bits_forwards i)
  | .Exception e => (exceptionType_bits_forwards e.trap)

def trapCause_is_interrupt (t : TrapCause) : Bool :=
  match t with
  | .Interrupt _ => true
  | .Exception _ => false

def undefined_TrapVectorMode (_ : Unit) : SailM TrapVectorMode := do
  (internal_pick [TV_Direct, TV_Vector, TV_Reserved])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def TrapVectorMode_of_num (arg_ : Nat) : TrapVectorMode :=
  match arg_ with
  | 0 => TV_Direct
  | 1 => TV_Vector
  | _ => TV_Reserved

def num_of_TrapVectorMode (arg_ : TrapVectorMode) : Int :=
  match arg_ with
  | .TV_Direct => 0
  | .TV_Vector => 1
  | .TV_Reserved => 2

def trapVectorMode_forwards (arg_ : (BitVec 2)) : TrapVectorMode :=
  match arg_ with
  | 0b00 => TV_Direct
  | 0b01 => TV_Vector
  | 0b10 => TV_Reserved
  | _ => TV_Reserved

def trapVectorMode_backwards (arg_ : TrapVectorMode) : (BitVec 2) :=
  match arg_ with
  | .TV_Direct => 0b00#2
  | .TV_Vector => 0b01#2
  | .TV_Reserved => 0b10#2

def trapVectorMode_forwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

def trapVectorMode_backwards_matches (arg_ : TrapVectorMode) : Bool :=
  match arg_ with
  | .TV_Direct => true
  | .TV_Vector => true
  | .TV_Reserved => true

def undefined_xRET_type (_ : Unit) : SailM xRET_type := do
  (internal_pick [mRET, sRET])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def xRET_type_of_num (arg_ : Nat) : xRET_type :=
  match arg_ with
  | 0 => mRET
  | _ => sRET

def num_of_xRET_type (arg_ : xRET_type) : Int :=
  match arg_ with
  | .mRET => 0
  | .sRET => 1

def undefined_ExtStatus (_ : Unit) : SailM ExtStatus := do
  (internal_pick [Off, Initial, Clean, Dirty])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def ExtStatus_of_num (arg_ : Nat) : ExtStatus :=
  match arg_ with
  | 0 => Off
  | 1 => Initial
  | 2 => Clean
  | _ => Dirty

def num_of_ExtStatus (arg_ : ExtStatus) : Int :=
  match arg_ with
  | .Off => 0
  | .Initial => 1
  | .Clean => 2
  | .Dirty => 3

def extStatus_map_forwards (arg_ : ExtStatus) : (BitVec 2) :=
  match arg_ with
  | .Off => 0b00#2
  | .Initial => 0b01#2
  | .Clean => 0b10#2
  | .Dirty => 0b11#2

def extStatus_map_backwards (arg_ : (BitVec 2)) : ExtStatus :=
  match arg_ with
  | 0b00 => Off
  | 0b01 => Initial
  | 0b10 => Clean
  | _ => Dirty

def extStatus_map_forwards_matches (arg_ : ExtStatus) : Bool :=
  match arg_ with
  | .Off => true
  | .Initial => true
  | .Clean => true
  | .Dirty => true

def extStatus_map_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

def legalize_extStatus (policy : ExtContextPolicy) (status : (BitVec 2)) : (BitVec 2) :=
  match policy with
  | .ExtContext_Off => (extStatus_map_forwards Off)
  | .ExtContext_TwoState =>
    (if (((extStatus_map_backwards status) == Off) : Bool)
    then status
    else (extStatus_map_forwards Dirty))
  | .ExtContext_FourState => status

def undefined_HGATPMode (_ : Unit) : SailM HGATPMode := do
  (internal_pick [HBare, Sv32x4, Sv39x4, Sv48x4, Sv57x4])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def HGATPMode_of_num (arg_ : Nat) : HGATPMode :=
  match arg_ with
  | 0 => HBare
  | 1 => Sv32x4
  | 2 => Sv39x4
  | 3 => Sv48x4
  | _ => Sv57x4

def num_of_HGATPMode (arg_ : HGATPMode) : Int :=
  match arg_ with
  | .HBare => 0
  | .Sv32x4 => 1
  | .Sv39x4 => 2
  | .Sv48x4 => 3
  | .Sv57x4 => 4

def hgatpMode_of_bits (a : Architecture) (m : (BitVec 4)) : SailM (Option HGATPMode) := do
  match (a, m) with
  | (_, 0x0) => (pure (some HBare))
  | (.RV32, 0x1) => (pure (some Sv32x4))
  | (.RV64, 0x8) => (pure (some Sv39x4))
  | (.RV64, 0x9) => (pure (some Sv48x4))
  | (.RV64, 0xA) => (pure (some Sv57x4))
  | (_, _) => (pure none)

def undefined_SATPMode (_ : Unit) : SailM SATPMode := do
  (internal_pick [Bare, Sv32, Sv39, Sv48, Sv57])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def SATPMode_of_num (arg_ : Nat) : SATPMode :=
  match arg_ with
  | 0 => Bare
  | 1 => Sv32
  | 2 => Sv39
  | 3 => Sv48
  | _ => Sv57

def num_of_SATPMode (arg_ : SATPMode) : Int :=
  match arg_ with
  | .Bare => 0
  | .Sv32 => 1
  | .Sv39 => 2
  | .Sv48 => 3
  | .Sv57 => 4

def satpMode_of_bits (a : Architecture) (m : (BitVec 4)) : SailM (Option SATPMode) := do
  match (a, m) with
  | (_, 0x0) => (pure (some Bare))
  | (.RV32, 0x1) => (pure (some Sv32))
  | (.RV64, 0x8) => (pure (some Sv39))
  | (.RV64, 0x9) => (pure (some Sv48))
  | (.RV64, 0xA) => (pure (some Sv57))
  | (_, _) => (pure none)

def undefined_WaitReason (_ : Unit) : SailM WaitReason := do
  (internal_pick [WAIT_WFI, WAIT_WRS_STO, WAIT_WRS_NTO])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def WaitReason_of_num (arg_ : Nat) : WaitReason :=
  match arg_ with
  | 0 => WAIT_WFI
  | 1 => WAIT_WRS_STO
  | _ => WAIT_WRS_NTO

def num_of_WaitReason (arg_ : WaitReason) : Int :=
  match arg_ with
  | .WAIT_WFI => 0
  | .WAIT_WRS_STO => 1
  | .WAIT_WRS_NTO => 2

def wait_name_forwards_matches (arg_ : WaitReason) : Bool :=
  match arg_ with
  | .WAIT_WFI => true
  | .WAIT_WRS_STO => true
  | .WAIT_WRS_NTO => true

def wait_name_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "WAIT-WFI" => true
  | "WAIT-WRS-STO" => true
  | "WAIT-WRS-NTO" => true
  | _ => false

def width_enc_backwards (arg_ : (BitVec 2)) : Int :=
  match arg_ with
  | 0b00 => 1
  | 0b01 => 2
  | 0b10 => 4
  | _ => 8

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8] -/
def width_enc_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | _ => false

def width_enc_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

def width_mnemonic_backwards (arg_ : String) : SailM Int := do
  match arg_ with
  | "b" => (pure 1)
  | "h" => (pure 2)
  | "w" => (pure 4)
  | "d" => (pure 8)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8] -/
def width_mnemonic_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | _ => false

def width_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "b" => true
  | "h" => true
  | "w" => true
  | "d" => true
  | _ => false

def width_enc_wide_backwards (arg_ : (BitVec 3)) : SailM Int := do
  match arg_ with
  | 0b000 => (pure 1)
  | 0b001 => (pure 2)
  | 0b010 => (pure 4)
  | 0b011 => (pure 8)
  | 0b100 => (pure 16)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8, 16] -/
def width_enc_wide_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | 16 => true
  | _ => false

def width_enc_wide_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match arg_ with
  | 0b000 => true
  | 0b001 => true
  | 0b010 => true
  | 0b011 => true
  | 0b100 => true
  | _ => false

def width_mnemonic_wide_backwards (arg_ : String) : SailM Int := do
  match arg_ with
  | "b" => (pure 1)
  | "h" => (pure 2)
  | "w" => (pure 4)
  | "d" => (pure 8)
  | "q" => (pure 16)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8, 16] -/
def width_mnemonic_wide_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | 16 => true
  | _ => false

def width_mnemonic_wide_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "b" => true
  | "h" => true
  | "w" => true
  | "d" => true
  | "q" => true
  | _ => false

