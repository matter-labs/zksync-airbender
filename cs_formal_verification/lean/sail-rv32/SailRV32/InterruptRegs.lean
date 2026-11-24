import SailRV32.Flow
import SailRV32.Prelude
import SailRV32.IsaVersion
import SailRV32.Xlen
import SailRV32.PlatformConfig
import SailRV32.Callbacks
import SailRV32.SysRegs
import SailRV32.InterruptInterface

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

def hgei_mask : xlenbits := (zero_extend (m := 32) ((ones (n := geilen)) +++ 0#1))

def legalize_hgeie (v : (BitVec 32)) : (BitVec 32) :=
  (v &&& hgei_mask)

def guest_external_interrupts_pending (_ : Unit) : SailM (BitVec 32) := do
  readReg sig_hgeip

def read_hgeip (_ : Unit) : SailM (BitVec 32) := do
  (pure ((← (guest_external_interrupts_pending ())) &&& hgei_mask))

def selected_vgein_in_hgeip (_ : Unit) : SailM (BitVec 1) := do
  let vgein ← do (pure (BitVec.toNatInt (_get_Hstatus_VGEIN (← readReg hstatus))))
  if (((vgein >b 0) && (vgein ≤b geilen)) : Bool)
  then
    (do
      let hgeip ← do (read_hgeip ())
      (pure (BitVec.join1 [(BitVec.access hgeip vgein)])))
  else (pure 0#1)

def supported_interrupts_mask (i : (BitVec 32)) : SailM (BitVec 32) := do
  (pure (Mk_Minterrupts
      ((_update_Minterrupts_LCOFI
          (_update_Minterrupts_SGEI
            (_update_Minterrupts_STI
              (_update_Minterrupts_SSI
                (_update_Minterrupts_SEI
                  (_update_Minterrupts_MTI
                    (_update_Minterrupts_MSI
                      (_update_Minterrupts_MEI (Mk_Minterrupts (ones (n := 32)))
                        (bool_to_bit plat_has_mei)) (bool_to_bit plat_has_msi))
                    (bool_to_bit plat_has_mti)) (bool_to_bit plat_has_sei))
                (bool_to_bit plat_has_ssi)) (bool_to_bit plat_has_sti)) (bool_to_bit (geilen >b 0)))
          (← do
            if ((← (currentlyEnabled Ext_Sscofpmf)) : Bool)
            then (pure 1#1)
            else (pure 0#1))) &&& i)))

def legalize_mip (o : (BitVec 32)) (v : (BitVec 32)) : SailM (BitVec 32) := do
  let v := (Mk_Minterrupts v)
  (supported_interrupts_mask
    (_update_Minterrupts_VSSI
      (_update_Minterrupts_VSTI
        (_update_Minterrupts_VSEI
          (_update_Minterrupts_SGEI
            (_update_Minterrupts_STI
              (_update_Minterrupts_SSI
                (_update_Minterrupts_SEI
                  (_update_Minterrupts_LCOFI o
                    (← do
                      if ((← (currentlyEnabled Ext_Sscofpmf)) : Bool)
                      then (pure (_get_Minterrupts_LCOFI v))
                      else (pure 0#1)))
                  (← do
                    if ((← (currentlyEnabled Ext_S)) : Bool)
                    then (pure (_get_Minterrupts_SEI v))
                    else (pure 0#1)))
                (← do
                  if ((← (currentlyEnabled Ext_S)) : Bool)
                  then (pure (_get_Minterrupts_SSI v))
                  else (pure 0#1)))
              (← do
                if ((← (currentlyEnabled Ext_S)) : Bool)
                then
                  (do
                    if (((← (currentlyEnabled Ext_Sstc)) && ((_get_MEnvcfg_STCE
                             (← readReg menvcfg)) == 1#1)) : Bool)
                    then (pure (_get_Minterrupts_STI o))
                    else (pure (_get_Minterrupts_STI v)))
                else (pure 0#1))) 0#1)
          (← do
            if ((← (currentlyEnabled Ext_H)) : Bool)
            then (pure (_get_Minterrupts_VSEI (← readReg hvip)))
            else (pure 0#1)))
        (← do
          if ((← (currentlyEnabled Ext_H)) : Bool)
          then
            (do
              if (((← (currentlyEnabled Ext_Sstc)) && ((_get_HEnvcfg_STCE (← (read_henvcfg ()))) == 1#1)) : Bool)
              then (pure (_get_Minterrupts_VSTI o))
              else (pure (_get_Minterrupts_VSTI (← readReg hvip))))
          else (pure 0#1)))
      (← do
        if ((← (currentlyEnabled Ext_H)) : Bool)
        then (pure (_get_Minterrupts_VSSI v))
        else (pure 0#1))))

def legalize_mie (o : (BitVec 32)) (v : (BitVec 32)) : SailM (BitVec 32) := do
  let v := (Mk_Minterrupts v)
  (supported_interrupts_mask
    (_update_Minterrupts_VSSI
      (_update_Minterrupts_VSTI
        (_update_Minterrupts_VSEI
          (_update_Minterrupts_SGEI
            (_update_Minterrupts_SSI
              (_update_Minterrupts_STI
                (_update_Minterrupts_SEI
                  (_update_Minterrupts_MSI
                    (_update_Minterrupts_MTI
                      (_update_Minterrupts_MEI
                        (_update_Minterrupts_LCOFI o
                          (← do
                            if ((← (currentlyEnabled Ext_Sscofpmf)) : Bool)
                            then (pure (_get_Minterrupts_LCOFI v))
                            else (pure 0#1))) (_get_Minterrupts_MEI v)) (_get_Minterrupts_MTI v))
                    (_get_Minterrupts_MSI v))
                  (← do
                    if ((← (currentlyEnabled Ext_S)) : Bool)
                    then (pure (_get_Minterrupts_SEI v))
                    else (pure 0#1)))
                (← do
                  if ((← (currentlyEnabled Ext_S)) : Bool)
                  then (pure (_get_Minterrupts_STI v))
                  else (pure 0#1)))
              (← do
                if ((← (currentlyEnabled Ext_S)) : Bool)
                then (pure (_get_Minterrupts_SSI v))
                else (pure 0#1)))
            (← do
              if ((← (currentlyEnabled Ext_H)) : Bool)
              then (pure (_get_Minterrupts_SGEI v))
              else (pure 0#1)))
          (← do
            if ((← (currentlyEnabled Ext_H)) : Bool)
            then (pure (_get_Minterrupts_VSEI v))
            else (pure 0#1)))
        (← do
          if ((← (currentlyEnabled Ext_H)) : Bool)
          then (pure (_get_Minterrupts_VSTI v))
          else (pure 0#1)))
      (← do
        if ((← (currentlyEnabled Ext_H)) : Bool)
        then (pure (_get_Minterrupts_VSSI v))
        else (pure 0#1))))

def legalize_mideleg (_o : (BitVec 32)) (v : (BitVec 32)) : SailM (BitVec 32) := do
  let v := (Mk_Minterrupts (v &&& plat_mideleg_delegatable_bits))
  (pure (_update_Minterrupts_SGEI
      (_update_Minterrupts_VSSI
        (_update_Minterrupts_VSTI
          (_update_Minterrupts_VSEI
            (_update_Minterrupts_SSI
              (_update_Minterrupts_STI
                (_update_Minterrupts_SEI
                  (_update_Minterrupts_LCOFI v
                    (← do
                      if ((← (currentlyEnabled Ext_Sscofpmf)) : Bool)
                      then (pure (_get_Minterrupts_LCOFI v))
                      else (pure 0#1)))
                  (← do
                    if ((← (currentlyEnabled Ext_S)) : Bool)
                    then (pure (_get_Minterrupts_SEI v))
                    else (pure 0#1)))
                (← do
                  if ((← (currentlyEnabled Ext_S)) : Bool)
                  then (pure (_get_Minterrupts_STI v))
                  else (pure 0#1)))
              (← do
                if ((← (currentlyEnabled Ext_S)) : Bool)
                then (pure (_get_Minterrupts_SSI v))
                else (pure 0#1)))
            (← do
              if ((← (currentlyEnabled Ext_H)) : Bool)
              then (pure 1#1)
              else (pure 0#1)))
          (← do
            if ((← (currentlyEnabled Ext_H)) : Bool)
            then (pure 1#1)
            else (pure 0#1)))
        (← do
          if ((← (currentlyEnabled Ext_H)) : Bool)
          then (pure 1#1)
          else (pure 0#1)))
      (← do
        if (((← (currentlyEnabled Ext_H)) && (geilen >b 0)) : Bool)
        then (pure 1#1)
        else (pure 0#1))))

def undefined_Medeleg (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Medeleg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Medeleg_Breakpoint (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_Medeleg_Breakpoint (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _set_Medeleg_Breakpoint (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Breakpoint r v)

def _get_Medeleg_Double_Trap (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_Medeleg_Double_Trap (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _set_Medeleg_Double_Trap (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Double_Trap r v)

def _get_Medeleg_Fetch_Access_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Medeleg_Fetch_Access_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Medeleg_Fetch_Access_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Fetch_Access_Fault r v)

def _get_Medeleg_Fetch_Addr_Align (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_Medeleg_Fetch_Addr_Align (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Medeleg_Fetch_Addr_Align (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Fetch_Addr_Align r v)

def _get_Medeleg_Fetch_GPage_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_Medeleg_Fetch_GPage_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _set_Medeleg_Fetch_GPage_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Fetch_GPage_Fault r v)

def _get_Medeleg_Fetch_Page_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_Medeleg_Fetch_Page_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _set_Medeleg_Fetch_Page_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Fetch_Page_Fault r v)

def _get_Medeleg_Hardware_Error (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_Medeleg_Hardware_Error (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _set_Medeleg_Hardware_Error (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Hardware_Error r v)

def _get_Medeleg_Illegal_Instr (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_Medeleg_Illegal_Instr (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _set_Medeleg_Illegal_Instr (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Illegal_Instr r v)

def _get_Medeleg_Load_Access_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_Medeleg_Load_Access_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Medeleg_Load_Access_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Load_Access_Fault r v)

def _get_Medeleg_Load_Addr_Align (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_Medeleg_Load_Addr_Align (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _set_Medeleg_Load_Addr_Align (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Load_Addr_Align r v)

def _get_Medeleg_Load_GPage_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_Medeleg_Load_GPage_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _set_Medeleg_Load_GPage_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Load_GPage_Fault r v)

def _get_Medeleg_Load_Page_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_Medeleg_Load_Page_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _set_Medeleg_Load_Page_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Load_Page_Fault r v)

def _get_Medeleg_MEnvCall (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_Medeleg_MEnvCall (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _set_Medeleg_MEnvCall (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_MEnvCall r v)

def _get_Medeleg_SAMO_Access_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_Medeleg_SAMO_Access_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Medeleg_SAMO_Access_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_SAMO_Access_Fault r v)

def _get_Medeleg_SAMO_Addr_Align (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_Medeleg_SAMO_Addr_Align (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _set_Medeleg_SAMO_Addr_Align (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_SAMO_Addr_Align r v)

def _get_Medeleg_SAMO_GPage_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_Medeleg_SAMO_GPage_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _set_Medeleg_SAMO_GPage_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_SAMO_GPage_Fault r v)

def _get_Medeleg_SAMO_Page_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_Medeleg_SAMO_Page_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _set_Medeleg_SAMO_Page_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_SAMO_Page_Fault r v)

def _get_Medeleg_SEnvCall (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_Medeleg_SEnvCall (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _set_Medeleg_SEnvCall (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_SEnvCall r v)

def _get_Medeleg_Software_Check (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_Medeleg_Software_Check (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _set_Medeleg_Software_Check (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Software_Check r v)

def _get_Medeleg_UEnvCall (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_Medeleg_UEnvCall (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _set_Medeleg_UEnvCall (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_UEnvCall r v)

def _get_Medeleg_VSEnvCall (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_Medeleg_VSEnvCall (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _set_Medeleg_VSEnvCall (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_VSEnvCall r v)

def _get_Medeleg_Virtual_Instr (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_Medeleg_Virtual_Instr (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _set_Medeleg_Virtual_Instr (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Virtual_Instr r v)

def legalize_medeleg (_o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_Medeleg (v &&& plat_medeleg_delegatable_bits))
  (pure (_update_Medeleg_Breakpoint
      (_update_Medeleg_MEnvCall
        (_update_Medeleg_Double_Trap
          (_update_Medeleg_VSEnvCall
            (_update_Medeleg_Fetch_GPage_Fault
              (_update_Medeleg_Load_GPage_Fault
                (_update_Medeleg_Virtual_Instr
                  (_update_Medeleg_SAMO_GPage_Fault v
                    (← do
                      if ((← (currentlyEnabled Ext_H)) : Bool)
                      then (pure (_get_Medeleg_SAMO_GPage_Fault v))
                      else (pure 0#1)))
                  (← do
                    if ((← (currentlyEnabled Ext_H)) : Bool)
                    then (pure (_get_Medeleg_Virtual_Instr v))
                    else (pure 0#1)))
                (← do
                  if ((← (currentlyEnabled Ext_H)) : Bool)
                  then (pure (_get_Medeleg_Load_GPage_Fault v))
                  else (pure 0#1)))
              (← do
                if ((← (currentlyEnabled Ext_H)) : Bool)
                then (pure (_get_Medeleg_Fetch_GPage_Fault v))
                else (pure 0#1)))
            (← do
              if ((← (currentlyEnabled Ext_H)) : Bool)
              then (pure (_get_Medeleg_VSEnvCall v))
              else (pure 0#1))) 0#1) 0#1)
      (← do
        if (((← (currentlyEnabled Ext_Sdtrig)) && (sdtrig_breakpoint_reentrancy == Use_tcontrol)) : Bool)
        then (pure 0#1)
        else (pure (_get_Medeleg_Breakpoint v)))))

def undefined_XipReadType (_ : Unit) : SailM XipReadType := do
  (internal_pick [IncludePlatformInterrupts, ExcludePlatformInterrupts])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def XipReadType_of_num (arg_ : Nat) : XipReadType :=
  match arg_ with
  | 0 => IncludePlatformInterrupts
  | _ => ExcludePlatformInterrupts

def num_of_XipReadType (arg_ : XipReadType) : Int :=
  match arg_ with
  | .IncludePlatformInterrupts => 0
  | .ExcludePlatformInterrupts => 1

def sig_external_interrupts_pending (hgeie_val : (BitVec 32)) : SailM (BitVec 32) := do
  (pure (_update_Minterrupts_VSEI
      (_update_Minterrupts_SGEI
        (_update_Minterrupts_SEI
          (_update_Minterrupts_MEI (Mk_Minterrupts (zeros (n := 32))) (← readReg sig_meip))
          (← do
            if ((← (currentlyEnabled Ext_S)) : Bool)
            then readReg sig_seip
            else (pure 0#1)))
        (← do
          if ((← (currentlyEnabled Ext_H)) : Bool)
          then (pure (bool_to_bit (((← readReg sig_hgeip) &&& hgeie_val) != (zeros (n := 32)))))
          else (pure 0#1)))
      (← do
        if ((← (currentlyEnabled Ext_H)) : Bool)
        then (selected_vgein_in_hgeip ())
        else (pure 0#1))))

def external_interrupts_pending (hgeie_val : (BitVec 32)) : SailM (BitVec 32) := do
  if (plat_have_sig : Bool)
  then (sig_external_interrupts_pending hgeie_val)
  else (pure (Mk_Minterrupts (zeros (n := 32))))

def sig_supervisor_software_interrupt_pending (_ : Unit) : SailM (BitVec 1) := do
  readReg sig_ssip

def supervisor_software_interrupt_pending (_ : Unit) : SailM (BitVec 1) := do
  if (plat_have_sig : Bool)
  then (sig_supervisor_software_interrupt_pending ())
  else (pure 0#1)

def read_mip (read_type : XipReadType) : SailM (BitVec 32) := do
  match read_type with
  | .IncludePlatformInterrupts =>
    (do
      let platform_interrupts ← do
        (supported_interrupts_mask
          (_update_Minterrupts_SSI (← (external_interrupts_pending (← readReg hgeie)))
            (← do
              if ((← (currentlyEnabled Ext_S)) : Bool)
              then (supervisor_software_interrupt_pending ())
              else (pure 0#1))))
      (pure (Mk_Minterrupts ((← readReg mip) ||| platform_interrupts))))
  | .ExcludePlatformInterrupts => readReg mip

def clint_get_hart_mtimecmp (_ : Unit) : SailM (BitVec 64) := do
  readReg mtimecmp

def get_hart_mtimecmp (_ : Unit) : SailM (BitVec 64) := do
  if (plat_have_clint : Bool)
  then (clint_get_hart_mtimecmp ())
  else (pure (zeros (n := 64)))

def clint_get_mtime (_ : Unit) : SailM (BitVec 64) := do
  readReg mtime

def get_mtime (_ : Unit) : SailM (BitVec 64) := do
  if (plat_have_clint : Bool)
  then (clint_get_mtime ())
  else (pure (zeros (n := 64)))

def clint_machine_software_interrupt_pending (_ : Unit) : SailM (BitVec 1) := do
  (pure (BitVec.access (← readReg msip) 0))

def sig_machine_software_interrupt_pending (_ : Unit) : SailM (BitVec 1) := do
  readReg sig_msip

def machine_software_interrupt_pending (_ : Unit) : SailM (BitVec 1) := do
  (pure ((← do
        if (plat_have_clint : Bool)
        then (clint_machine_software_interrupt_pending ())
        else (pure 0#1)) ||| (← do
        if (plat_have_sig : Bool)
        then (sig_machine_software_interrupt_pending ())
        else (pure 0#1))))

def update_mip (_ : Unit) : SailM Unit := do
  let old_mip ← do readReg mip
  let platform_has_timer := plat_have_clint
  let cur_mtime ← do (get_mtime ())
  let hart_mtimecmp ← do (get_hart_mtimecmp ())
  let new_mip ← do readReg mip
  let new_mip ←
    (pure (Sail.BitVec.updateSubrange new_mip 3 3 (← (machine_software_interrupt_pending ()))))
  let new_mip ← (( do
    if (platform_has_timer : Bool)
    then
      (do
        let new_mip : (BitVec 32) :=
          (Sail.BitVec.updateSubrange new_mip 7 7
            (bool_to_bit (zopz0zIzJ_u hart_mtimecmp cur_mtime)))
        if (((← (currentlyEnabled Ext_Sstc)) && ((_get_MEnvcfg_STCE (← readReg menvcfg)) == 1#1)) : Bool)
        then
          (do
            (pure (Sail.BitVec.updateSubrange new_mip 5 5
                (bool_to_bit (zopz0zIzJ_u (← readReg stimecmp) cur_mtime)))))
        else (pure new_mip))
    else (pure new_mip) ) : SailM (BitVec 32) )
  let new_mip ← (( do
    if ((← (currentlyEnabled Ext_H)) : Bool)
    then
      (do
        let new_mip ←
          (pure (Sail.BitVec.updateSubrange new_mip 10 10 (_get_Minterrupts_VSEI (← readReg hvip))))
        (pure (Sail.BitVec.updateSubrange new_mip 6 6
            ((_get_Minterrupts_VSTI (← readReg hvip)) ||| (← do
                if (((← (currentlyEnabled Ext_Sstc)) && (((_get_HEnvcfg_STCE
                           (← (read_henvcfg ()))) == 1#1) && platform_has_timer)) : Bool)
                then
                  (pure (bool_to_bit
                      (zopz0zIzJ_u (← readReg vstimecmp) (cur_mtime + (← readReg htimedelta)))))
                else (pure 0#1))))))
    else (pure new_mip) ) : SailM (BitVec 32) )
  writeReg mip (← (supported_interrupts_mask new_mip))
  if ((old_mip != (← readReg mip)) : Bool)
  then (csr_name_write_callback "mip" (← (read_mip IncludePlatformInterrupts)))
  else (pure ())

def write_mip (value : (BitVec 32)) : SailM Unit := do
  writeReg mip (← (legalize_mip (← readReg mip) value))

def legalize_hvip (h : (BitVec 32)) (v : (BitVec 32)) : (BitVec 32) :=
  let v := (Mk_Minterrupts v)
  (_update_Minterrupts_VSSI
    (_update_Minterrupts_VSTI (_update_Minterrupts_VSEI h (_get_Minterrupts_VSEI v))
      (_get_Minterrupts_VSTI v)) (_get_Minterrupts_VSSI v))

def legalize_hie (m : (BitVec 32)) (v : (BitVec 32)) : SailM (BitVec 32) := do
  let v := (Mk_Minterrupts v)
  (supported_interrupts_mask
    (_update_Minterrupts_VSSI
      (_update_Minterrupts_VSTI
        (_update_Minterrupts_VSEI (_update_Minterrupts_SGEI m (_get_Minterrupts_SGEI v))
          (_get_Minterrupts_VSEI v)) (_get_Minterrupts_VSTI v)) (_get_Minterrupts_VSSI v)))

def legalize_hip (m : (BitVec 32)) (v : (BitVec 32)) : SailM (BitVec 32) := do
  let v := (Mk_Minterrupts v)
  (supported_interrupts_mask (_update_Minterrupts_VSSI m (_get_Minterrupts_VSSI v)))

def lower_mip_to_hvip (m : (BitVec 32)) (h : (BitVec 32)) : (BitVec 32) :=
  (_update_Minterrupts_VSSI h (_get_Minterrupts_VSSI m))

def lower_mie_to_hie (m : (BitVec 32)) : (BitVec 32) :=
  (_update_Minterrupts_VSSI
    (_update_Minterrupts_VSTI
      (_update_Minterrupts_VSEI
        (_update_Minterrupts_SGEI (Mk_Minterrupts (zeros (n := 32))) (_get_Minterrupts_SGEI m))
        (_get_Minterrupts_VSEI m)) (_get_Minterrupts_VSTI m)) (_get_Minterrupts_VSSI m))

def lower_mip_to_hip (m : (BitVec 32)) : (BitVec 32) :=
  (_update_Minterrupts_VSSI
    (_update_Minterrupts_VSTI
      (_update_Minterrupts_VSEI
        (_update_Minterrupts_SGEI (Mk_Minterrupts (zeros (n := 32))) (_get_Minterrupts_SGEI m))
        (_get_Minterrupts_VSEI m)) (_get_Minterrupts_VSTI m)) (_get_Minterrupts_VSSI m))

def hedeleg_writable_mask (_ : Unit) : (BitVec 64) :=
  (_update_Medeleg_Hardware_Error (Mk_Medeleg 0x00000000000CB1FF#64)
    (if ((privileged_isa_version_ge priv_isa_version Privileged_ISA_1_13) : Bool)
    then 1#1
    else 0#1))

def legalize_hedeleg (_m : (BitVec 64)) (v : (BitVec 64)) : (BitVec 64) :=
  (Mk_Medeleg (v &&& (hedeleg_writable_mask ())))

def legalize_hideleg (m : (BitVec 32)) (v : (BitVec 32)) : (BitVec 32) :=
  let v := (Mk_Minterrupts v)
  (_update_Minterrupts_VSSI
    (_update_Minterrupts_VSTI (_update_Minterrupts_VSEI m (_get_Minterrupts_VSEI v))
      (_get_Minterrupts_VSTI v)) (_get_Minterrupts_VSSI v))

def undefined_Sinterrupts (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Sinterrupts (v : (BitVec 32)) : (BitVec 32) :=
  v

def lower_mip (m : (BitVec 32)) (d : (BitVec 32)) : (BitVec 32) :=
  let s : Sinterrupts := (Mk_Sinterrupts (zeros (n := 32)))
  (_update_Sinterrupts_SSI
    (_update_Sinterrupts_MSI
      (_update_Sinterrupts_STI
        (_update_Sinterrupts_MTI
          (_update_Sinterrupts_SEI
            (_update_Sinterrupts_MEI
              (_update_Sinterrupts_LCOFI s
                ((_get_Minterrupts_LCOFI m) &&& (_get_Minterrupts_LCOFI d)))
              ((_get_Minterrupts_MEI m) &&& (_get_Minterrupts_MEI d)))
            ((_get_Minterrupts_SEI m) &&& (_get_Minterrupts_SEI d)))
          ((_get_Minterrupts_MTI m) &&& (_get_Minterrupts_MTI d)))
        ((_get_Minterrupts_STI m) &&& (_get_Minterrupts_STI d)))
      ((_get_Minterrupts_MSI m) &&& (_get_Minterrupts_MSI d)))
    ((_get_Minterrupts_SSI m) &&& (_get_Minterrupts_SSI d)))

def lower_mie (m : (BitVec 32)) (d : (BitVec 32)) : (BitVec 32) :=
  let s : Sinterrupts := (Mk_Sinterrupts (zeros (n := 32)))
  (_update_Sinterrupts_SSI
    (_update_Sinterrupts_MSI
      (_update_Sinterrupts_STI
        (_update_Sinterrupts_MTI
          (_update_Sinterrupts_SEI
            (_update_Sinterrupts_MEI
              (_update_Sinterrupts_LCOFI s
                ((_get_Minterrupts_LCOFI m) &&& (_get_Minterrupts_LCOFI d)))
              ((_get_Minterrupts_MEI m) &&& (_get_Minterrupts_MEI d)))
            ((_get_Minterrupts_SEI m) &&& (_get_Minterrupts_SEI d)))
          ((_get_Minterrupts_MTI m) &&& (_get_Minterrupts_MTI d)))
        ((_get_Minterrupts_STI m) &&& (_get_Minterrupts_STI d)))
      ((_get_Minterrupts_MSI m) &&& (_get_Minterrupts_MSI d)))
    ((_get_Minterrupts_SSI m) &&& (_get_Minterrupts_SSI d)))

def lower_mip_to_vsip (m : (BitVec 32)) (d : (BitVec 32)) : (BitVec 32) :=
  (_update_Sinterrupts_SSI
    (_update_Sinterrupts_STI
      (_update_Sinterrupts_SEI (Mk_Sinterrupts (zeros (n := 32)))
        ((_get_Minterrupts_VSEI m) &&& (_get_Minterrupts_VSEI d)))
      ((_get_Minterrupts_VSTI m) &&& (_get_Minterrupts_VSTI d)))
    ((_get_Minterrupts_VSSI m) &&& (_get_Minterrupts_VSSI d)))

def lower_mie_to_vsie (m : (BitVec 32)) (d : (BitVec 32)) : (BitVec 32) :=
  let vs := (Mk_Minterrupts (zeros (n := 32)))
  (_update_Minterrupts_SSI
    (_update_Minterrupts_STI
      (_update_Minterrupts_SEI vs ((_get_Minterrupts_VSEI m) &&& (_get_Minterrupts_VSEI d)))
      ((_get_Minterrupts_VSTI m) &&& (_get_Minterrupts_VSTI d)))
    ((_get_Minterrupts_VSSI m) &&& (_get_Minterrupts_VSSI d)))

def lift_sip (o : (BitVec 32)) (d : (BitVec 32)) (s : (BitVec 32)) : (BitVec 32) :=
  (_update_Minterrupts_LCOFI
    (_update_Minterrupts_SSI o
      (if (((_get_Minterrupts_SSI d) == 1#1) : Bool)
      then (_get_Sinterrupts_SSI s)
      else (_get_Minterrupts_SSI o)))
    (if (((_get_Minterrupts_LCOFI d) == 1#1) : Bool)
    then (_get_Sinterrupts_LCOFI s)
    else (_get_Minterrupts_LCOFI o)))

def legalize_sip (m : (BitVec 32)) (d : (BitVec 32)) (v : (BitVec 32)) : SailM (BitVec 32) := do
  (supported_interrupts_mask (lift_sip m d (Mk_Sinterrupts v)))

def legalize_vsip (m : (BitVec 32)) (d : (BitVec 32)) (v : (BitVec 32)) : SailM (BitVec 32) := do
  let v := (Mk_Minterrupts v)
  (supported_interrupts_mask
    (_update_Minterrupts_VSSI m ((_get_Minterrupts_SSI v) &&& (_get_Minterrupts_VSSI d))))

def read_sip (read_type : XipReadType) : SailM (BitVec 32) := do
  if ((← (inVirtualPrivilege ())) : Bool)
  then (pure (lower_mip_to_vsip (← (read_mip read_type)) (← readReg hideleg)))
  else (pure (lower_mip (← (read_mip read_type)) (← readReg mideleg)))

def write_sip (value : (BitVec 32)) : SailM Unit := do
  writeReg mip (← do
    if ((← (inVirtualPrivilege ())) : Bool)
    then (legalize_vsip (← readReg mip) (← readReg hideleg) value)
    else (legalize_sip (← readReg mip) (← readReg mideleg) value))

def lift_sie (o : (BitVec 32)) (d : (BitVec 32)) (s : (BitVec 32)) : (BitVec 32) :=
  (_update_Minterrupts_LCOFI
    (_update_Minterrupts_SSI
      (_update_Minterrupts_MSI
        (_update_Minterrupts_STI
          (_update_Minterrupts_MTI
            (_update_Minterrupts_SEI
              (_update_Minterrupts_MEI o
                (if (((_get_Minterrupts_MEI d) == 1#1) : Bool)
                then (_get_Sinterrupts_MEI s)
                else (_get_Minterrupts_MEI o)))
              (if (((_get_Minterrupts_SEI d) == 1#1) : Bool)
              then (_get_Sinterrupts_SEI s)
              else (_get_Minterrupts_SEI o)))
            (if (((_get_Minterrupts_MTI d) == 1#1) : Bool)
            then (_get_Sinterrupts_MTI s)
            else (_get_Minterrupts_MTI o)))
          (if (((_get_Minterrupts_STI d) == 1#1) : Bool)
          then (_get_Sinterrupts_STI s)
          else (_get_Minterrupts_STI o)))
        (if (((_get_Minterrupts_MSI d) == 1#1) : Bool)
        then (_get_Sinterrupts_MSI s)
        else (_get_Minterrupts_MSI o)))
      (if (((_get_Minterrupts_SSI d) == 1#1) : Bool)
      then (_get_Sinterrupts_SSI s)
      else (_get_Minterrupts_SSI o)))
    (if (((_get_Minterrupts_LCOFI d) == 1#1) : Bool)
    then (_get_Sinterrupts_LCOFI s)
    else (_get_Minterrupts_LCOFI o)))

def legalize_sie (m : (BitVec 32)) (d : (BitVec 32)) (v : (BitVec 32)) : SailM (BitVec 32) := do
  (supported_interrupts_mask (lift_sie m d (Mk_Sinterrupts v)))

def legalize_vsie (m : (BitVec 32)) (d : (BitVec 32)) (v : (BitVec 32)) : SailM (BitVec 32) := do
  let v := (Mk_Minterrupts v)
  (supported_interrupts_mask
    (_update_Minterrupts_VSSI
      (_update_Minterrupts_VSTI
        (_update_Minterrupts_VSEI m ((_get_Minterrupts_SEI v) &&& (_get_Minterrupts_VSEI d)))
        ((_get_Minterrupts_STI v) &&& (_get_Minterrupts_VSTI d)))
      ((_get_Minterrupts_SSI v) &&& (_get_Minterrupts_VSSI d))))

