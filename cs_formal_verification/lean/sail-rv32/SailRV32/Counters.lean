import SailRV32.Prelude
import SailRV32.Xlen
import SailRV32.PlatformConfig
import SailRV32.Callbacks
import SailRV32.SysRegs
import SailRV32.Events
import SailRV32.InterruptInterface
import SailRV32.InterruptRegs

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

def undefined_HpmEvent (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HpmEvent (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HpmEvent_MINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _update_HpmEvent_MINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_CountSmcntrpmf_MINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _set_HpmEvent_MINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HpmEvent_MINH r v)

def _get_CountSmcntrpmf_MINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _set_CountSmcntrpmf_MINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CountSmcntrpmf_MINH r v)

def _get_HpmEvent_OF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_HpmEvent_OF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _set_HpmEvent_OF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HpmEvent_OF r v)

def _get_HpmEvent_SINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _update_HpmEvent_SINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_CountSmcntrpmf_SINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _set_HpmEvent_SINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HpmEvent_SINH r v)

def _get_CountSmcntrpmf_SINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _set_CountSmcntrpmf_SINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CountSmcntrpmf_SINH r v)

def _get_HpmEvent_UINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _update_HpmEvent_UINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_CountSmcntrpmf_UINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _set_HpmEvent_UINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HpmEvent_UINH r v)

def _get_CountSmcntrpmf_UINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _set_CountSmcntrpmf_UINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CountSmcntrpmf_UINH r v)

def _get_HpmEvent_VSINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _update_HpmEvent_VSINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_CountSmcntrpmf_VSINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _set_HpmEvent_VSINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HpmEvent_VSINH r v)

def _get_CountSmcntrpmf_VSINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _set_CountSmcntrpmf_VSINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CountSmcntrpmf_VSINH r v)

def _get_HpmEvent_VUINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _update_HpmEvent_VUINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _update_CountSmcntrpmf_VUINH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _set_HpmEvent_VUINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HpmEvent_VUINH r v)

def _get_CountSmcntrpmf_VUINH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _set_CountSmcntrpmf_VUINH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CountSmcntrpmf_VUINH r v)

def _get_HpmEvent_event (v : (BitVec 64)) : (BitVec 56) :=
  (Sail.BitVec.extractLsb v 55 0)

def _update_HpmEvent_event (v : (BitVec 64)) (x : (BitVec 56)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 0 x)

def _set_HpmEvent_event (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 56)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HpmEvent_event r v)

def hpmidx_from_bits (b : (BitVec 5)) : SailM Nat := do
  let index := (BitVec.toNatInt b)
  «assert» (index ≥b 3) "unreachable HPM index"
  (pure index)

def legalize_hpmevent (v : (BitVec 64)) : SailM (BitVec 64) := do
  if ((not (← (currentlyEnabled Ext_Sscofpmf))) : Bool)
  then (pure (zero_extend (m := 64) (Sail.BitVec.extractLsb v (plat_hpmevent_width_bits -i 1) 0)))
  else
    (do
      «assert» (plat_hpmevent_width_bits ≤b 56) "core/counters.sail:157.39-157.40"
      let v := (Mk_HpmEvent v)
      (pure (_update_HpmEvent_event
          (_update_HpmEvent_VUINH
            (_update_HpmEvent_VSINH
              (_update_HpmEvent_UINH
                (_update_HpmEvent_SINH
                  (_update_HpmEvent_MINH
                    (_update_HpmEvent_OF (Mk_HpmEvent (zeros (n := 64)))
                      (← do
                        if ((← (currentlyEnabled Ext_Sscofpmf)) : Bool)
                        then (pure (_get_HpmEvent_OF v))
                        else (pure 0#1)))
                    (← do
                      if ((← (currentlyEnabled Ext_Sscofpmf)) : Bool)
                      then (pure (_get_HpmEvent_MINH v))
                      else (pure 0#1)))
                  (← do
                    if (((← (currentlyEnabled Ext_Sscofpmf)) && (← (currentlyEnabled Ext_S))) : Bool)
                    then (pure (_get_HpmEvent_SINH v))
                    else (pure 0#1)))
                (← do
                  if (((← (currentlyEnabled Ext_Sscofpmf)) && (← (currentlyEnabled Ext_U))) : Bool)
                  then (pure (_get_HpmEvent_UINH v))
                  else (pure 0#1)))
              (← do
                if (((← (currentlyEnabled Ext_Sscofpmf)) && (← (currentlyEnabled Ext_H))) : Bool)
                then (pure (_get_HpmEvent_VSINH v))
                else (pure 0#1)))
            (← do
              if (((← (currentlyEnabled Ext_Sscofpmf)) && (← (currentlyEnabled Ext_H))) : Bool)
              then (pure (_get_HpmEvent_VUINH v))
              else (pure 0#1)))
          (zero_extend (m := 56)
            (Sail.BitVec.extractLsb (_get_HpmEvent_event v) (plat_hpmevent_width_bits -i 1) 0)))))

def legalize_hpmcounter_value (v : (BitVec 64)) : (BitVec 64) :=
  (zero_extend (m := 64) (Sail.BitVec.extractLsb v (plat_hpmcounter_width_bits -i 1) 0))

def legalize_hpmcounter_value_xlen (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb (legalize_hpmcounter_value (zero_extend (m := 64) v)) (xlen -i 1) 0)

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def read_mhpmcounter (index : Nat) : SailM (BitVec 32) := do
  (pure (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg mhpmcounter) index) (xlen -i 1) 0))

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def read_mhpmcounterh (index : Nat) : SailM (BitVec 32) := do
  (pure (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg mhpmcounter) index) 63 32))

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def read_mhpmevent (index : Nat) : SailM (BitVec 32) := do
  (pure (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg mhpmevent) index) (xlen -i 1) 0))

def undefined_event_csr (_ : Unit) : SailM event_csr := do
  (internal_pick [EV_EVENT, EV_COUNTER])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def event_csr_of_num (arg_ : Nat) : event_csr :=
  match arg_ with
  | 0 => EV_EVENT
  | _ => EV_COUNTER

def num_of_event_csr (arg_ : event_csr) : Int :=
  match arg_ with
  | .EV_EVENT => 0
  | .EV_COUNTER => 1

def clear_written_event_index (_ : Unit) : SailM Unit := do
  writeReg written_event_index none

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def write_mhpmcounter (index : Nat) (value : (BitVec 64)) : SailM Unit := do
  if (((BitVec.access sys_writable_hpm_counters index) == 1#1) : Bool)
  then
    (do
      writeReg mhpmcounter (vectorUpdate (← readReg mhpmcounter) index
        (legalize_hpmcounter_value value))
      writeReg written_event_index (some (index, EV_COUNTER)))
  else (pure ())

/-- Type quantifiers: x_0 : Nat, 3 ≤ x_0 ∧ x_0 ≤ 31 -/
def event_csr_write_callback (x_0 : Nat) (x_1 : (BitVec 64)) (x_2 : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def write_mhpmevent (index : Nat) (value : (BitVec 64)) : SailM Unit := do
  if (((BitVec.access sys_writable_hpm_counters index) == 1#1) : Bool)
  then
    (do
      let old_value ← do (pure (GetElem?.getElem! (← readReg mhpmevent) index))
      let value ← do (legalize_hpmevent value)
      writeReg mhpmevent (vectorUpdate (← readReg mhpmevent) index value)
      writeReg written_event_index (some (index, EV_EVENT))
      (pure (event_csr_write_callback index (selector_value old_value) (selector_value value))))
  else (pure ())

/-- Type quantifiers: index : Nat, 3 ≤ index ∧ index ≤ 31 -/
def dispatchEventCounter (index : Nat) (event_priv : Privilege) : SailM Unit := SailME.run do
  «assert» ((BitVec.access sys_writable_hpm_counters index) == 1#1) "core/counters.sail:267.48-267.49"
  if (((BitVec.access (_get_Counterin_HPM (← readReg mcountinhibit)) (index -i 3)) == 1#1) : Bool)
  then (pure ())
  else
    (do
      if ((← (currentlyEnabled Ext_Sscofpmf)) : Bool)
      then
        (do
          let event_cfg ← do
            (pure (Mk_HpmEvent (GetElem?.getElem! (← readReg mhpmevent) index)))
          let is_inhibited_bit : (BitVec 1) :=
            match event_priv with
            | .Machine => (_get_HpmEvent_MINH event_cfg)
            | .Supervisor => (_get_HpmEvent_SINH event_cfg)
            | .User => (_get_HpmEvent_UINH event_cfg)
            | .VirtualSupervisor => (_get_HpmEvent_VSINH event_cfg)
            | .VirtualUser => (_get_HpmEvent_VUINH event_cfg)
          if ((is_inhibited_bit == 1#1) : Bool)
          then SailME.throw (() : Unit)
          else (pure ()))
      else (pure ())
      match (← readReg written_event_index) with
      | .some (idx, .EV_COUNTER) =>
        (do
          if ((idx == index) : Bool)
          then SailME.throw (() : Unit)
          else (pure ()))
      | .some (idx, .EV_EVENT) =>
        (do
          if (((idx == index) && (not plat_hpmcounter_increments_in_self_hpmevent_write)) : Bool)
          then SailME.throw (() : Unit)
          else (pure ()))
      | none => (pure ())
      let index_bits : (BitVec 5) := (to_bits (l := 5) index)
      let counter_csr : csreg := (0b1011000#7 +++ index_bits)
      let event_csr : csreg := (0b0011001#7 +++ index_bits)
      let count ← do (pure (GetElem?.getElem! (← readReg mhpmcounter) index))
      let overflowed : Bool := (count == (legalize_hpmcounter_value (ones (n := 64))))
      let new_count := (legalize_hpmcounter_value (BitVec.addInt count 1))
      writeReg mhpmcounter (vectorUpdate (← readReg mhpmcounter) index new_count)
      let counter_csr_name ← do (csr_name_map_forwards counter_csr)
      (long_csr_write_callback counter_csr_name (HAppend.hAppend counter_csr_name "h") new_count)
      if (((← (currentlyEnabled Ext_Sscofpmf)) && overflowed) : Bool)
      then
        (do
          let event_cfg ← do
            (pure (Mk_HpmEvent (GetElem?.getElem! (← readReg mhpmevent) index)))
          let previously_overflowed := ((_get_HpmEvent_OF event_cfg) == 1#1)
          if ((not previously_overflowed) : Bool)
          then
            (do
              let new_event_cfg := (_update_HpmEvent_OF event_cfg 1#1)
              writeReg mhpmevent (vectorUpdate (← readReg mhpmevent) index new_event_cfg)
              writeReg mip (← (supported_interrupts_mask
                  (_update_Minterrupts_LCOFI (← readReg mip) 1#1)))
              let event_csr_name ← do (csr_name_map_forwards event_csr)
              (long_csr_write_callback event_csr_name (HAppend.hAppend event_csr_name "h")
                new_event_cfg)
              (csr_name_write_callback "mip" (← (read_mip IncludePlatformInterrupts))))
          else (pure ()))
      else (pure ()))

