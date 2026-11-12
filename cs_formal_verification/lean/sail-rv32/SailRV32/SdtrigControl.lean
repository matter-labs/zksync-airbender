import SailRV32.SailRV32
import SailRV32.Flow
import SailRV32.Prelude
import SailRV32.Errors
import SailRV32.PlatformConfig
import SailRV32.Callbacks
import SailRV32.SysRegs
import SailRV32.InterruptRegs
import SailRV32.SdtrigTypeUtils
import SailRV32.SdtrigTypes

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

def prevent_reentrance (act : Trig_Action) (priv : Privilege) : SailM Bool := do
  if ((bne act TA_Breakpoint) : Bool)
  then (pure false)
  else
    (do
      match sdtrig_breakpoint_reentrancy with
      | .Use_tcontrol =>
        (pure ((priv == Machine) && ((_get_TControl_mte (← readReg tcontrol)) == 0#1)))
      | .Use_interrupt_enables =>
        (do
          match priv with
          | .Machine => (pure ((_get_Mstatus_MIE (← readReg mstatus)) == 0#1))
          | .Supervisor =>
            (pure (((_get_Medeleg_Breakpoint (← readReg medeleg)) == 1#1) && ((_get_Mstatus_SIE
                    (← readReg mstatus)) == 0#1)))
          | .VirtualSupervisor =>
            (pure (((_get_Medeleg_Breakpoint (← readReg medeleg)) == 1#1) && (((_get_Medeleg_Breakpoint
                      (← readReg hedeleg)) == 1#1) && ((_get_Mstatus_SIE (← readReg vsstatus)) == 0#1))))
          | .VirtualUser => (pure false)
          | .User => (pure false))
      | .No_reentrancy_support => (pure false))

/-- Type quantifiers: k_ex1822008_ : Bool -/
def icount_match (t : ICount) (priv : Privilege) (reentrance : Bool) : Bool :=
  ((not ((t.action == TA_Breakpoint) && reentrance)) && (match priv with
    | .Machine => t.m
    | .Supervisor => t.s
    | .User => t.u
    | .VirtualSupervisor => t.vs
    | .VirtualUser => t.vu : Bool))

/-- Type quantifiers: k_ex1822009_ : Bool -/
def match_icount_triggers (priv : Privilege) (reentrance : Bool) : SailM Unit := do
  if ((not (← (currentlyEnabled Ext_Sdtrig))) : Bool)
  then (pure ())
  else
    (do
      let loop_i_lower := 0
      let loop_i_upper := (num_triggers -i 1)
      let mut loop_vars := ()
      for i in [loop_i_lower:loop_i_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          match (GetElem?.getElem! (← readReg triggers) i) with
          | .T_icount t =>
            (do
              if ((t.active && (icount_match t priv reentrance)) : Bool)
              then
                (do
                  let set_pending ← (( do
                    match (← readReg written_trigger_index) with
                    | .some (idx, .TDATA1) => (pure ((idx != i) || icount_self_write_sets_pending))
                    | .some (_, _) => (pure true)
                    | none => (pure true) ) : SailM Bool )
                  let new_t : ICount :=
                    match (BitVec.toNatInt t.count) with
                    | 0 => t
                    | 1 =>
                      { t with count := if (icount_count_is_hardwired_one : Bool)
                        then t.count
                        else (zeros (n := 14)), pending := set_pending }
                    | _ => { t with count := (BitVec.subInt t.count 1) }
                  writeReg triggers (vectorUpdate (← readReg triggers) i (T_icount new_t))
                  let _ : Unit :=
                    if ((get_config_print_trigger ()) : Bool)
                    then
                      (print_endline
                        (HAppend.hAppend "Matched icount at index #"
                          (HAppend.hAppend (Int.repr i)
                            (HAppend.hAppend " with action " (trigger_action_name_forwards t.action)))))
                    else ()
                  (pure (trigger_match_callback i)))
              else (pure ()))
          | _ => (pure ())
      (pure loop_vars))

def itrigger_match (t : ITrigger) (intr : InterruptType) (from_priv : Privilege) (to_priv : Privilege) : SailM Bool := do
  let priv_match ← (( do
    (pure ((not (← (prevent_reentrance t.action to_priv))) && (match from_priv with
        | .Machine => t.m
        | .Supervisor => t.s
        | .User => t.u
        | .VirtualSupervisor => t.vs
        | .VirtualUser => t.vu : Bool))) ) : SailM Bool )
  (pure (priv_match && ((t.tdata2 &&& (make_itrigger_flag intr)) != (zeros (n := 32)))))

def match_itrigger_triggers (intr : InterruptType) (from_priv : Privilege) (to_priv : Privilege) : SailM Unit := do
  if ((not (← (currentlyEnabled Ext_Sdtrig))) : Bool)
  then (pure ())
  else
    (do
      let loop_i_lower := 0
      let loop_i_upper := (num_triggers -i 1)
      let mut loop_vars := ()
      for i in [loop_i_lower:loop_i_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          match (GetElem?.getElem! (← readReg triggers) i) with
          | .T_itrigger t =>
            (do
              if ((← (itrigger_match t intr from_priv to_priv)) : Bool)
              then
                (do
                  writeReg triggers (vectorUpdate (← readReg triggers) i
                    (T_itrigger { t with pending := true, hit := true }))
                  let _ : Unit :=
                    if ((get_config_print_trigger ()) : Bool)
                    then
                      (print_endline
                        (HAppend.hAppend "Interrupt "
                          (HAppend.hAppend (interruptType_to_str intr)
                            (HAppend.hAppend " matched itrigger at index #"
                              (HAppend.hAppend (Int.repr i)
                                (HAppend.hAppend " with action "
                                  (trigger_action_name_forwards t.action)))))))
                    else ()
                  (pure (trigger_match_callback i)))
              else (pure ()))
          | _ => (pure ())
      (pure loop_vars))

def etrigger_match (t : ETrigger) (e : ExceptionType) (from_priv : Privilege) (to_priv : Privilege) : SailM Bool := do
  let priv_match ← (( do
    (pure ((not (← (prevent_reentrance t.action to_priv))) && (match from_priv with
        | .Machine => t.m
        | .Supervisor => t.s
        | .User => t.u
        | .VirtualSupervisor => t.vs
        | .VirtualUser => t.vu : Bool))) ) : SailM Bool )
  (pure (priv_match && ((t.tdata2 &&& (make_etrigger_flag e)) != (zeros (n := 32)))))

def match_etrigger_triggers (exc : ExceptionType) (from_priv : Privilege) (to_priv : Privilege) : SailM Unit := do
  if ((not (← (currentlyEnabled Ext_Sdtrig))) : Bool)
  then (pure ())
  else
    (do
      let loop_i_lower := 0
      let loop_i_upper := (num_triggers -i 1)
      let mut loop_vars := ()
      for i in [loop_i_lower:loop_i_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          match (GetElem?.getElem! (← readReg triggers) i) with
          | .T_etrigger t =>
            (do
              if ((← (etrigger_match t exc from_priv to_priv)) : Bool)
              then
                (do
                  writeReg triggers (vectorUpdate (← readReg triggers) i
                    (T_etrigger { t with pending := true, hit := true }))
                  let _ : Unit :=
                    if ((get_config_print_trigger ()) : Bool)
                    then
                      (print_endline
                        (HAppend.hAppend "Exception "
                          (HAppend.hAppend (exceptionType_to_str exc)
                            (HAppend.hAppend " matched etrigger at index #"
                              (HAppend.hAppend (Int.repr i)
                                (HAppend.hAppend " with action "
                                  (trigger_action_name_forwards t.action)))))))
                    else ()
                  (pure (trigger_match_callback i)))
              else (pure ()))
          | _ => (pure ())
      (pure loop_vars))

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ (16 - 1) -/
def fire_trigger (idx : Nat) : SailM Unit := do
  let (t, action) ← (( do
    match (GetElem?.getElem! (← readReg triggers) idx) with
    | .T_icount t =>
      (let t :=
        if (icount_count_is_hardwired_one : Bool)
        then { t with m := false, s := false, u := false, vs := false, vu := false }
        else t
      (pure ((T_icount { t with pending := false, hit := true }), t.action)))
    | .T_itrigger t => (pure ((T_itrigger { t with pending := false }), t.action))
    | .T_etrigger t => (pure ((T_etrigger { t with pending := false }), t.action))
    | .T_disabled _ =>
      (internal_error "extensions/Sdtrig/sdtrig_control.sail" 163 "Disabled triggers cannot fire.")
    ) : SailM (Trigger × Trig_Action) )
  writeReg triggers (vectorUpdate (← readReg triggers) idx t)
  let _ : Unit :=
    if ((get_config_print_trigger ()) : Bool)
    then
      (print_endline
        (HAppend.hAppend "Fired "
          (HAppend.hAppend (trigger_name t)
            (HAppend.hAppend " at index #"
              (HAppend.hAppend (Int.repr idx)
                (HAppend.hAppend " with action " (trigger_action_name_forwards action)))))))
    else ()
  (pure (trigger_fire_callback idx))

def find_highest_priority_pending_trigger (priv : Privilege) : SailM (Option (Trig_Action × Nat × (BitVec 32))) := do
  if ((not (← (currentlyEnabled Ext_Sdtrig))) : Bool)
  then (pure none)
  else
    (do
      «assert» (num_triggers >b 0) "extensions/Sdtrig/sdtrig_control.sail:182.25-182.26"
      let found_pending : Bool := false
      let pending_index : trigger_index := 0
      let pending_action : Trig_Action := TA_Breakpoint
      let pending_tval : xlenbits := (zeros (n := 32))
      let (found_pending, pending_action, pending_index, pending_tval) ← (( do
        let loop_i_lower := 0
        let loop_i_upper := (num_triggers -i 1)
        let mut loop_vars := (found_pending, pending_action, pending_index, pending_tval)
        for i in [loop_i_lower:loop_i_upper:1]i do
          let (found_pending, pending_action, pending_index, pending_tval) := loop_vars
          loop_vars ← do
            let (found_pending, pending_action, pending_index, pending_tval) ← (( do
              match (GetElem?.getElem! (← readReg triggers) i) with
              | .T_disabled _ => (pure (found_pending, pending_action, pending_index, pending_tval))
              | .T_icount t =>
                (do
                  «assert» (zopz0zJzJzK t.pending t.active) "extensions/Sdtrig/sdtrig_control.sail:208.37-208.38"
                  let (found_pending, pending_action, pending_index, pending_tval) ← (( do
                    if ((t.pending && (icount_match t priv
                           (← (prevent_reentrance TA_Breakpoint priv)))) : Bool)
                    then
                      (do
                        let found_pending : Bool := true
                        let pending_index : trigger_index := i
                        let pending_action : Trig_Action := t.action
                        let pending_tval : (BitVec 32) :=
                          if ((pending_action == TA_Breakpoint) : Bool)
                          then (zeros (n := 32))
                          else pending_tval
                        (fire_trigger i)
                        (pure (found_pending, pending_action, pending_index, pending_tval)))
                    else (pure (found_pending, pending_action, pending_index, pending_tval)) ) :
                    SailM (Bool × Trig_Action × Nat × (BitVec 32)) )
                  (pure (found_pending, pending_action, pending_index, pending_tval)))
              | .T_itrigger t =>
                (do
                  let (found_pending, pending_action, pending_index, pending_tval) ← (( do
                    if ((t.pending && (not (← (prevent_reentrance t.action priv)))) : Bool)
                    then
                      (do
                        let found_pending : Bool := true
                        let pending_index : trigger_index := i
                        let pending_action : Trig_Action := t.action
                        let pending_tval : (BitVec 32) :=
                          if ((pending_action == TA_Breakpoint) : Bool)
                          then (zeros (n := 32))
                          else pending_tval
                        (fire_trigger i)
                        (pure (found_pending, pending_action, pending_index, pending_tval)))
                    else (pure (found_pending, pending_action, pending_index, pending_tval)) ) :
                    SailM (Bool × Trig_Action × Nat × (BitVec 32)) )
                  (pure (found_pending, pending_action, pending_index, pending_tval)))
              | .T_etrigger t =>
                (do
                  let (found_pending, pending_action, pending_index, pending_tval) ← (( do
                    if ((t.pending && (not (← (prevent_reentrance t.action priv)))) : Bool)
                    then
                      (do
                        let found_pending : Bool := true
                        let pending_index : trigger_index := i
                        let pending_action : Trig_Action := t.action
                        let pending_tval : (BitVec 32) :=
                          if ((pending_action == TA_Breakpoint) : Bool)
                          then (zeros (n := 32))
                          else pending_tval
                        (fire_trigger i)
                        (pure (found_pending, pending_action, pending_index, pending_tval)))
                    else (pure (found_pending, pending_action, pending_index, pending_tval)) ) :
                    SailM (Bool × Trig_Action × Nat × (BitVec 32)) )
                  (pure (found_pending, pending_action, pending_index, pending_tval))) ) : SailM
              (Bool × Trig_Action × Nat × (BitVec 32)) )
            (pure (found_pending, pending_action, pending_index, pending_tval))
        (pure loop_vars) ) : SailM (Bool × Trig_Action × Nat × (BitVec 32)) )
      if (found_pending : Bool)
      then (pure (some (pending_action, pending_index, pending_tval)))
      else (pure none))

def update_triggers (_ : Unit) : SailM Unit := do
  match (← readReg written_trigger_index) with
  | none => (pure ())
  | .some (idx, .TDATA1) =>
    (do
      match (GetElem?.getElem! (← readReg triggers) idx) with
      | .T_icount t =>
        (do
          match t.new_count with
          | .some c =>
            writeReg triggers (vectorUpdate (← readReg triggers) idx
              (T_icount { t with count := c, new_count := none, active := true }))
          | none => «assert» t.active "extensions/Sdtrig/sdtrig_control.sail:250.36-250.37")
      | _ => (pure ())
      writeReg written_trigger_index none)
  | .some _ => writeReg written_trigger_index none

