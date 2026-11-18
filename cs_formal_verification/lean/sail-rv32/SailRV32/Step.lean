import SailRV32.Prelude
import SailRV32.Errors
import SailRV32.PlatformConfig
import SailRV32.Types
import SailRV32.Common0
import SailRV32.Callbacks
import SailRV32.PcAccess
import SailRV32.SysRegs
import SailRV32.Events
import SailRV32.ExtRegs
import SailRV32.InterruptRegs
import SailRV32.Counters
import SailRV32.AddrChecks
import SailRV32.SysExceptions
import SailRV32.SyncException
import SailRV32.SdtrigTypes
import SailRV32.SdtrigControl
import SailRV32.ZicfilpRegs
import SailRV32.SysControl
import SailRV32.Platform
import SailRV32.InterruptImplementation
import SailRV32.Callbacks0
import SailRV32.InstsBegin
import SailRV32.ZicfilpInsts
import SailRV32.InstsEnd
import SailRV32.StepCommon
import SailRV32.StepExt
import SailRV32.DecodeExt
import SailRV32.Fetch
import SailRV32.TransformedInst

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

/-- Type quantifiers: k_ex1822425_ : Bool, _step_no : Nat, 0 ≤ _step_no -/
def run_hart_waiting (_step_no : Nat) (wr : WaitReason) (instr_info : instr_info) (exit_wait : Bool) : SailM Step := do
  if ((← (shouldWakeForInterrupt ())) : Bool)
  then
    (do
      if ((get_config_print_instr ()) : Bool)
      then
        (pure (print_endline
            (HAppend.hAppend "interrupt exit from "
              (HAppend.hAppend (wait_name_forwards wr)
                (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
      else (pure ())
      writeReg hart_state (HART_ACTIVE ())
      (pure (Step_Execute ((Retire_Success ()), instr_info))))
  else
    (do
      match (wr, (valid_reservation ()), exit_wait) with
      | (.WAIT_WRS_STO, false, _) =>
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "reservation invalid exit from "
                  (HAppend.hAppend (wait_name_forwards WAIT_WRS_STO)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_ACTIVE ())
          (pure (Step_Execute ((Retire_Success ()), instr_info))))
      | (.WAIT_WRS_NTO, false, _) =>
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "reservation invalid exit from "
                  (HAppend.hAppend (wait_name_forwards WAIT_WRS_NTO)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_ACTIVE ())
          (pure (Step_Execute ((Retire_Success ()), instr_info))))
      | (.WAIT_WFI, _, true) =>
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "forced exit from "
                  (HAppend.hAppend (wait_name_forwards WAIT_WFI)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_ACTIVE ())
          match (← readReg cur_privilege) with
          | .Machine => (pure (Step_Execute ((Retire_Success ()), instr_info)))
          | .User =>
            (do
              if ((((_get_Mstatus_TW (← readReg mstatus)) == 1#1) || (← (currentlyEnabled Ext_S))) : Bool)
              then (pure (Step_Execute ((Illegal_Instruction ()), instr_info)))
              else (pure (Step_Execute ((Retire_Success ()), instr_info))))
          | .VirtualSupervisor =>
            (do
              if (((_get_Hstatus_VTW (← readReg hstatus)) == 1#1) : Bool)
              then (pure (Step_Execute ((Virtual_Instruction ()), instr_info)))
              else (pure (Step_Execute ((Retire_Success ()), instr_info))))
          | _ =>
            (do
              if (((_get_Mstatus_TW (← readReg mstatus)) == 1#1) : Bool)
              then (pure (Step_Execute ((Illegal_Instruction ()), instr_info)))
              else (pure (Step_Execute ((Retire_Success ()), instr_info)))))
      | (.WAIT_WRS_STO, _, true) =>
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "timed-out exit from "
                  (HAppend.hAppend (wait_name_forwards WAIT_WRS_STO)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_ACTIVE ())
          (pure (Step_Execute ((Retire_Success ()), instr_info))))
      | (.WAIT_WRS_NTO, _, true) =>
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "timed-out exit from "
                  (HAppend.hAppend (wait_name_forwards WAIT_WRS_NTO)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_ACTIVE ())
          if (((← readReg cur_privilege) == Machine) : Bool)
          then (pure (Step_Execute ((Retire_Success ()), instr_info)))
          else
            (do
              if (((_get_Mstatus_TW (← readReg mstatus)) == 1#1) : Bool)
              then (pure (Step_Execute ((Illegal_Instruction ()), instr_info)))
              else
                (do
                  if (((← (inVirtualPrivilege ())) && ((_get_Hstatus_VTW (← readReg hstatus)) == 1#1)) : Bool)
                  then (pure (Step_Execute ((Virtual_Instruction ()), instr_info)))
                  else (pure (Step_Execute ((Retire_Success ()), instr_info))))))
      | (_, _, false) =>
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "remaining in "
                  (HAppend.hAppend (wait_name_forwards wr)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          (pure (Step_Waiting wr))))

/-- Type quantifiers: step_no : Nat, 0 ≤ step_no -/
def run_hart_active (step_no : Nat) : SailM Step := SailME.run do
  match (← (find_highest_priority_pending_trigger (← readReg cur_privilege))) with
  | .some (action, idx, breakpoint_tval) =>
    SailME.throw ((Step_Pending_Trigger (action, idx, breakpoint_tval)) : Step)
  | none => (pure ())
  match (← (dispatchInterrupt (← readReg cur_privilege))) with
  | .some (intr, priv) => SailME.throw ((Step_Pending_Interrupt (intr, priv)) : Step)
  | none => (pure ())
  let fetch_privilege ← do readReg cur_privilege
  let fetch_trigger_reentrance ← do (prevent_reentrance TA_Breakpoint fetch_privilege)
  match (ext_fetch_hook (← (fetch ()))) with
  | .F_Ext_Error e => (pure (Step_Ext_Fetch_Failure e))
  | .F_Error e => (pure (Step_Fetch_Failure e))
  | .F_RVC h =>
    (do
      let _ : Unit := (sail_instr_announce h)
      let _ : Unit := (fetch_callback h)
      let instbits : instbits := (zero_extend (m := 32) h)
      let fetched_instruction ← do (ext_decode_compressed h)
      if ((get_config_print_instr ()) : Bool)
      then
        (pure (print_log_instr
            (HAppend.hAppend "["
              (HAppend.hAppend (Int.repr step_no)
                (HAppend.hAppend "] ["
                  (HAppend.hAppend (← (privLevel_to_str (← readReg cur_privilege)))
                    (HAppend.hAppend "]: "
                      (HAppend.hAppend (BitVec.toFormatted (← readReg PC))
                        (HAppend.hAppend " ("
                          (HAppend.hAppend (BitVec.toFormatted h)
                            (HAppend.hAppend ") " (← (instruction_to_str fetched_instruction)))))))))))
            (zero_extend (m := 64) (← readReg PC))))
      else (pure ())
      if ((← (is_landing_pad_expected ())) : Bool)
      then
        (do
          let r ← do (trap (make_landing_pad_exception ()))
          let executed_instruction : (Option instruction) := none
          let instr_info :=
            { fetch_privilege := fetch_privilege
              fetch_trigger_reentrance := fetch_trigger_reentrance
              instbits := instbits
              fetched_instruction := fetched_instruction
              executed_instruction := executed_instruction
              compressed := true }
          (pure (Step_Execute (r, instr_info))))
      else
        (do
          if ((← (currentlyEnabled Ext_Zca)) : Bool)
          then
            (do
              writeReg nextPC (BitVec.addInt (← readReg PC) 2)
              let (executed_instruction, result) ← (( do
                match (← (execute fetched_instruction)) with
                | .ExecuteAs other_inst => (pure ((some other_inst), (← (execute other_inst))))
                | result => (pure ((some fetched_instruction), result)) ) : SailME Step
                ((Option instruction) × ExecutionResult) )
              let instr_info :=
                { fetch_privilege := fetch_privilege
                  fetch_trigger_reentrance := fetch_trigger_reentrance
                  fetched_instruction := fetched_instruction
                  executed_instruction := executed_instruction
                  instbits := instbits
                  compressed := true }
              (pure (Step_Execute (result, instr_info))))
          else
            (let executed_instruction : (Option instruction) := none
            let instr_info :=
              { fetch_privilege := fetch_privilege
                fetch_trigger_reentrance := fetch_trigger_reentrance
                fetched_instruction := fetched_instruction
                executed_instruction := executed_instruction
                instbits := instbits
                compressed := true }
            (pure (Step_Execute ((Illegal_Instruction ()), instr_info))))))
  | .F_Base w =>
    (do
      let _ : Unit := (sail_instr_announce w)
      let _ : Unit := (fetch_callback w)
      let instbits : instbits := (zero_extend (m := 32) w)
      let fetched_instruction ← do (ext_decode w)
      if ((get_config_print_instr ()) : Bool)
      then
        (pure (print_log_instr
            (HAppend.hAppend "["
              (HAppend.hAppend (Int.repr step_no)
                (HAppend.hAppend "] ["
                  (HAppend.hAppend (← (privLevel_to_str (← readReg cur_privilege)))
                    (HAppend.hAppend "]: "
                      (HAppend.hAppend (BitVec.toFormatted (← readReg PC))
                        (HAppend.hAppend " ("
                          (HAppend.hAppend (BitVec.toFormatted w)
                            (HAppend.hAppend ") " (← (instruction_to_str fetched_instruction)))))))))))
            (zero_extend (m := 64) (← readReg PC))))
      else (pure ())
      if (((← (is_landing_pad_expected ())) && (not (is_lpad_instruction fetched_instruction))) : Bool)
      then
        (do
          let r ← do (trap (make_landing_pad_exception ()))
          let executed_instruction : (Option instruction) := none
          let instr_info :=
            { fetch_privilege := fetch_privilege
              fetch_trigger_reentrance := fetch_trigger_reentrance
              fetched_instruction := fetched_instruction
              executed_instruction := executed_instruction
              instbits := instbits
              compressed := false }
          (pure (Step_Execute (r, instr_info))))
      else
        (do
          writeReg nextPC (BitVec.addInt (← readReg PC) 4)
          let (executed_instruction, result) ← (( do
            match (← (execute fetched_instruction)) with
            | .ExecuteAs other_inst => (pure ((some other_inst), (← (execute other_inst))))
            | result => (pure ((some fetched_instruction), result)) ) : SailME Step
            ((Option instruction) × ExecutionResult) )
          let instr_info :=
            { fetch_privilege := fetch_privilege
              fetch_trigger_reentrance := fetch_trigger_reentrance
              fetched_instruction := fetched_instruction
              executed_instruction := executed_instruction
              instbits := instbits
              compressed := false }
          (pure (Step_Execute (result, instr_info)))))

def wait_is_nop (wr : WaitReason) : Bool :=
  match wr with
  | .WAIT_WFI => false
  | .WAIT_WRS_STO => false
  | .WAIT_WRS_NTO => false

/-- Type quantifiers: k_ex1822428_ : Bool, step_no : Nat, 0 ≤ step_no -/
def try_step (step_no : Nat) (exit_wait : Bool) : SailM Bool := do
  let _ : Unit := (ext_pre_step_hook ())
  (update_mip ())
  writeReg minstret_increment (← (should_inc_minstret (← readReg cur_privilege)))
  let step_val ← (( do
    match (← readReg hart_state) with
    | .HART_WAITING (wr, instr_info) => (run_hart_waiting step_no wr instr_info exit_wait)
    | .HART_ACTIVE () => (run_hart_active step_no) ) : SailM Step )
  match step_val with
  | .Step_Pending_Trigger (action, _, trigger_tval) =>
    (do
      match action with
      | .TA_Breakpoint =>
        (handle_exception (← (exception_context (E_Breakpoint Brk_Hardware) trigger_tval)))
      | _ =>
        (internal_error "postlude/step.sail" 268
          (HAppend.hAppend "Trigger action "
            (HAppend.hAppend (trigger_action_name_forwards action) " not supported."))))
  | .Step_Pending_Interrupt (intr, priv) =>
    (do
      let _ : Unit :=
        if ((get_config_print_instr ()) : Bool)
        then (print_bits "Handling interrupt: " (interruptType_bits_forwards intr))
        else ()
      (handle_interrupt intr priv))
  | .Step_Ext_Fetch_Failure e => (pure (ext_handle_fetch_check_error e))
  | .Step_Fetch_Failure e => (handle_exception e)
  | .Step_Waiting _ =>
    «assert» (hart_is_waiting (← readReg hart_state)) "cannot be Waiting in a non-Wait state"
  | .Step_Execute (.Retire_Success (), instr_info) =>
    (do
      «assert» (hart_is_active (← readReg hart_state)) "postlude/step.sail:280.39-280.40"
      (match_icount_triggers instr_info.fetch_privilege instr_info.fetch_trigger_reentrance))
  | .Step_Execute (.ExecuteAs _, _) =>
    (internal_error "postlude/step.sail" 286
      "Multiple chained ExecuteAs (only one redirection is supported).")
  | .Step_Execute (.Trap (priv, ctx, pc), instr_info) =>
    (do
      let ctx ← do (transform_exception_context ctx instr_info)
      (set_next_pc (← (exception_handler priv ctx pc))))
  | .Step_Execute (.Illegal_Instruction (), instr_info) =>
    (handle_exception
      (make_instr_exception_context (E_Illegal_Instr ()) (zero_extend (m := 32) instr_info.instbits)))
  | .Step_Execute (.Virtual_Instruction (), instr_info) =>
    (handle_exception
      (make_instr_exception_context (E_Virtual_Instr ()) (zero_extend (m := 32) instr_info.instbits)))
  | .Step_Execute (.Enter_Wait wr, instr_info) =>
    (do
      if ((wait_is_nop wr) : Bool)
      then
        (do
          «assert» (hart_is_active (← readReg hart_state)) "postlude/step.sail:299.41-299.42"
          (match_icount_triggers instr_info.fetch_privilege instr_info.fetch_trigger_reentrance))
      else
        (do
          if ((get_config_print_instr ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "entering "
                  (HAppend.hAppend (wait_name_forwards wr)
                    (HAppend.hAppend " state at PC " (BitVec.toFormatted (← readReg PC)))))))
          else (pure ())
          writeReg hart_state (HART_WAITING (wr, instr_info))))
  | .Step_Execute (.Ext_CSR_Check_Failure (), _) => (pure (ext_check_CSR_fail ()))
  | .Step_Execute (.Ext_ControlAddr_Check_Failure e, _) => (pure (ext_handle_control_check_error e))
  | .Step_Execute (.Ext_DataAddr_Check_Failure e, _) => (pure (ext_handle_data_check_error e))
  | .Step_Execute (.Ext_XRET_Priv_Failure (), _) => (pure (ext_fail_xret_priv ()))
  match (← readReg hart_state) with
  | .HART_WAITING _ => (pure true)
  | .HART_ACTIVE () =>
    (do
      (tick_pc ())
      let retired : Bool :=
        match step_val with
        | .Step_Execute (.Retire_Success (), g__0) => true
        | .Step_Execute (.Enter_Wait wr, g__1) =>
          (if ((wait_is_nop wr) : Bool)
          then true
          else false)
        | _ => false
      if ((retired && (← readReg minstret_increment)) : Bool)
      then writeReg minstret (BitVec.addInt (← readReg minstret) 1)
      else (pure ())
      (dispatch_events ())
      (clear_written_event_index ())
      (update_triggers ())
      if ((get_config_rvfi ()) : Bool)
      then
        writeReg rvfi_pc_data (Sail.BitVec.updateSubrange (← readReg rvfi_pc_data) 127 64
          (zero_extend (m := 64) (← (get_arch_pc ()))))
      else (pure ())
      let _ : Unit := (ext_post_step_hook ())
      let _ : Unit :=
        if (retired : Bool)
        then (instret_callback ())
        else ()
      (pure false))

def loop (_ : Unit) : SailM Nat := do
  let i : Nat := 0
  let step_no : Nat := 0
  let (i, step_no) ← (( do
    let mut loop_vars := (i, step_no)
    while (← (λ (i, step_no) => do (pure (not (← readReg htif_done)))) loop_vars) do
      let (i, step_no) := loop_vars
      loop_vars ← do
        let stepped ← do (try_step step_no true)
        let step_no ← (( do
          if (stepped : Bool)
          then
            (do
              let step_no : Nat := (step_no +i 1)
              let _ : Unit :=
                if ((get_config_print_instr ()) : Bool)
                then (print_step ())
                else ()
              (cycle_count ())
              (pure step_no))
          else (pure step_no) ) : SailM Nat )
        let i ← (( do
          if ((not (← readReg htif_done)) : Bool)
          then
            (do
              let i : Nat := (i +i 1)
              if ((i == plat_insns_per_tick) : Bool)
              then
                (do
                  (tick_clock ())
                  (pure 0))
              else (pure i))
          else (pure i) ) : SailM Nat )
        (pure (i, step_no))
    (pure loop_vars) ) : SailM (Nat × Nat) )
  let exit_val ← do (pure (BitVec.toNatInt (← readReg htif_exit_code)))
  let _ : Unit :=
    if ((exit_val == 0) : Bool)
    then (print_endline "SUCCESS")
    else (print_int "FAILURE: " exit_val)
  (pure exit_val)

