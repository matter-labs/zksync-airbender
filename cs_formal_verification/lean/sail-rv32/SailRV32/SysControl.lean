import SailRV32.Flow
import SailRV32.Prelude
import SailRV32.Errors
import SailRV32.IsaVersion
import SailRV32.Xlen
import SailRV32.PlatformConfig
import SailRV32.Types
import SailRV32.VmemTypes
import SailRV32.Callbacks
import SailRV32.PcAccess
import SailRV32.SysRegs
import SailRV32.Events
import SailRV32.InterruptInterface
import SailRV32.InterruptRegs
import SailRV32.SysExceptions
import SailRV32.PmpRegs
import SailRV32.PmpControl
import SailRV32.StateenRegs
import SailRV32.SdtrigRegs
import SailRV32.SdtrigControl
import SailRV32.ZicfilpRegs
import SailRV32.StateenAccessChecks

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

def effectivePrivilege (access : (MemoryAccessType mem_payload)) (m : (BitVec 64)) (priv : Privilege) : SailM Privilege := do
  if (((not (is_implicit_access access)) && ((_get_Mstatus_MPRV m) == 1#1)) : Bool)
  then
    (privLevel_bits_forwards
      ((_get_Mstatus_MPP m), (if (((_get_Mstatus_MPP m) == 0b11#2) : Bool)
      then 0#1
      else (_get_Mstatus_MPV m))))
  else (pure priv)

def csrAccess (csr : (BitVec 12)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb csr 11 10)

def csrPriv (csr : (BitVec 12)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb csr 9 8)

def privLevel_to_CSR_privbits (p : Privilege) : SailM (BitVec 2) := do
  match p with
  | .User => (pure 0b00#2)
  | .VirtualUser => (pure 0b00#2)
  | .Supervisor =>
    (do
      if ((← (currentlyEnabled Ext_H)) : Bool)
      then (pure 0b10#2)
      else (pure 0b01#2))
  | .VirtualSupervisor => (pure 0b01#2)
  | .Machine => (pure 0b11#2)

def check_CSR_priv (csr : (BitVec 12)) (p : Privilege) : SailM Bool := do
  (pure (zopz0zKzJ_u (← (privLevel_to_CSR_privbits p)) (csrPriv csr)))

def check_CSR_access (csr : (BitVec 12)) (access_type : CSRAccessType) : Bool :=
  (not (((access_type == CSRWrite) || (access_type == CSRReadWrite)) && ((csrAccess csr) == 0b11#2)))

def is_satp_accessible (priv : Privilege) : SailM Bool := do
  match priv with
  | .Machine => (pure (hartSupports Ext_S))
  | .Supervisor => (pure ((_get_Mstatus_TVM (← readReg mstatus)) == 0#1))
  | .VirtualSupervisor => (pure ((_get_Hstatus_VTVM (← readReg hstatus)) == 0#1))
  | .User => (pure false)
  | .VirtualUser => (pure false)

def is_ssp_accessible (priv : Privilege) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_Zicfiss)) && (← do
        match priv with
        | .Machine => (pure true)
        | .Supervisor => (pure ((_get_MEnvcfg_SSE (← readReg menvcfg)) == 1#1))
        | .User =>
          (pure (((_get_MEnvcfg_SSE (← readReg menvcfg)) == 1#1) && (((_get_SEnvcfg_SSE
                    (← (read_senvcfg ()))) == 1#1) || (not (← (currentlyEnabled Ext_S))))))
        | .VirtualSupervisor =>
          (pure (((_get_MEnvcfg_SSE (← readReg menvcfg)) == 1#1) && ((_get_HEnvcfg_SSE
                  (← (read_henvcfg ()))) == 1#1)))
        | .VirtualUser =>
          (pure (((_get_MEnvcfg_SSE (← readReg menvcfg)) == 1#1) && (((_get_HEnvcfg_SSE
                    (← (read_henvcfg ()))) == 1#1) && ((_get_SEnvcfg_SSE (← (read_senvcfg ()))) == 1#1)))))))

def is_stimecmp_accessible (priv : Privilege) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_S)) && ((← (currentlyEnabled Ext_Sstc)) && (← do
          match priv with
          | .Machine => (pure true)
          | .Supervisor =>
            (pure (((_get_Counteren_TM (← readReg mcounteren)) == 1#1) && ((_get_MEnvcfg_STCE
                    (← readReg menvcfg)) == 1#1)))
          | .User => (pure false)
          | .VirtualSupervisor =>
            (pure (((_get_Counteren_TM (← readReg mcounteren)) == 1#1) && (((_get_MEnvcfg_STCE
                      (← readReg menvcfg)) == 1#1) && (((_get_Counteren_TM
                        (← readReg hcounteren)) == 1#1) && ((_get_HEnvcfg_STCE
                        (← (read_henvcfg ()))) == 1#1)))))
          | .VirtualUser => (pure false)))))

def is_vstimecmp_accessible (priv : Privilege) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_H)) && ((← (currentlyEnabled Ext_Sstc)) && ((priv == Machine) || (((_get_Counteren_TM
                (← readReg mcounteren)) == 1#1) && ((_get_MEnvcfg_STCE (← readReg menvcfg)) == 1#1))))))

def is_CSR_accessible (b__0 : (BitVec 12)) (g__26 : Privilege) (g__27 : CSRAccessType) : SailM Bool := do
  if ((b__0 == (0x301#12 : (BitVec 12))) : Bool)
  then (pure true)
  else
    (do
      if ((b__0 == (0x300#12 : (BitVec 12))) : Bool)
      then (pure true)
      else
        (do
          if ((b__0 == (0x310#12 : (BitVec 12))) : Bool)
          then (pure (mstatush_is_defined && (xlen == 32)))
          else
            (do
              if ((b__0 == (0x600#12 : (BitVec 12))) : Bool)
              then (currentlyEnabled Ext_H)
              else
                (do
                  if ((b__0 == (0x747#12 : (BitVec 12))) : Bool)
                  then
                    (pure (mseccfg_csrs_are_defined && ((← (currentlyEnabled Ext_Zkr)) || ((hartSupports
                              Ext_Zicfilp) || (← (currentlyEnabled Ext_Smmpm))))))
                  else
                    (do
                      if ((b__0 == (0x757#12 : (BitVec 12))) : Bool)
                      then
                        (pure (mseccfg_csrs_are_defined && (((← (currentlyEnabled Ext_Zkr)) || (hartSupports
                                  Ext_Zicfilp)) && (xlen == 32))))
                      else
                        (do
                          if ((b__0 == (0x30A#12 : (BitVec 12))) : Bool)
                          then (pure ((← (currentlyEnabled Ext_U)) && xenvcfg_csrs_are_defined))
                          else
                            (do
                              if ((b__0 == (0x31A#12 : (BitVec 12))) : Bool)
                              then
                                (pure ((← (currentlyEnabled Ext_U)) && ((xlen == 32) && xenvcfg_csrs_are_defined)))
                              else
                                (do
                                  if ((b__0 == (0x10A#12 : (BitVec 12))) : Bool)
                                  then
                                    (pure ((← (currentlyEnabled Ext_S)) && xenvcfg_csrs_are_defined))
                                  else
                                    (do
                                      if ((b__0 == (0x60A#12 : (BitVec 12))) : Bool)
                                      then (currentlyEnabled Ext_H)
                                      else
                                        (do
                                          if ((b__0 == (0x61A#12 : (BitVec 12))) : Bool)
                                          then
                                            (pure ((← (currentlyEnabled Ext_H)) && (xlen == 32)))
                                          else
                                            (do
                                              if ((b__0 == (0x342#12 : (BitVec 12))) : Bool)
                                              then (pure true)
                                              else
                                                (do
                                                  if ((b__0 == (0x343#12 : (BitVec 12))) : Bool)
                                                  then (pure true)
                                                  else
                                                    (do
                                                      if ((b__0 == (0x340#12 : (BitVec 12))) : Bool)
                                                      then (pure true)
                                                      else
                                                        (do
                                                          if ((b__0 == (0x106#12 : (BitVec 12))) : Bool)
                                                          then (currentlyEnabled Ext_S)
                                                          else
                                                            (do
                                                              if ((b__0 == (0x606#12 : (BitVec 12))) : Bool)
                                                              then (currentlyEnabled Ext_H)
                                                              else
                                                                (do
                                                                  if ((b__0 == (0x306#12 : (BitVec 12))) : Bool)
                                                                  then (currentlyEnabled Ext_U)
                                                                  else
                                                                    (do
                                                                      if ((b__0 == (0x320#12 : (BitVec 12))) : Bool)
                                                                      then
                                                                        (pure plat_have_mcountinhibit)
                                                                      else
                                                                        (do
                                                                          if ((b__0 == (0xF11#12 : (BitVec 12))) : Bool)
                                                                          then (pure true)
                                                                          else
                                                                            (do
                                                                              if ((b__0 == (0xF12#12 : (BitVec 12))) : Bool)
                                                                              then (pure true)
                                                                              else
                                                                                (do
                                                                                  if ((b__0 == (0xF13#12 : (BitVec 12))) : Bool)
                                                                                  then (pure true)
                                                                                  else
                                                                                    (do
                                                                                      if ((b__0 == (0xF14#12 : (BitVec 12))) : Bool)
                                                                                      then
                                                                                        (pure true)
                                                                                      else
                                                                                        (do
                                                                                          if ((b__0 == (0xF15#12 : (BitVec 12))) : Bool)
                                                                                          then
                                                                                            (pure mconfigptr_is_defined)
                                                                                          else
                                                                                            (do
                                                                                              if ((b__0 == (0x34A#12 : (BitVec 12))) : Bool)
                                                                                              then
                                                                                                (currentlyEnabled
                                                                                                  Ext_H)
                                                                                              else
                                                                                                (do
                                                                                                  if ((b__0 == (0x34B#12 : (BitVec 12))) : Bool)
                                                                                                  then
                                                                                                    (pure ((← (currentlyEnabled
                                                                                                            Ext_H)) || (hartSupports
                                                                                                          Ext_Ssdbltrp)))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((b__0 == (0x605#12 : (BitVec 12))) : Bool)
                                                                                                      then
                                                                                                        (currentlyEnabled
                                                                                                          Ext_H)
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((b__0 == (0x615#12 : (BitVec 12))) : Bool)
                                                                                                          then
                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                    Ext_H)) && (xlen == 32)))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((b__0 == (0x643#12 : (BitVec 12))) : Bool)
                                                                                                              then
                                                                                                                (currentlyEnabled
                                                                                                                  Ext_H)
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((b__0 == (0x64A#12 : (BitVec 12))) : Bool)
                                                                                                                  then
                                                                                                                    (currentlyEnabled
                                                                                                                      Ext_H)
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((b__0 == (0x200#12 : (BitVec 12))) : Bool)
                                                                                                                      then
                                                                                                                        (currentlyEnabled
                                                                                                                          Ext_H)
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((b__0 == (0x100#12 : (BitVec 12))) : Bool)
                                                                                                                          then
                                                                                                                            (currentlyEnabled
                                                                                                                              Ext_S)
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((b__0 == (0x240#12 : (BitVec 12))) : Bool)
                                                                                                                              then
                                                                                                                                (currentlyEnabled
                                                                                                                                  Ext_H)
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((b__0 == (0x242#12 : (BitVec 12))) : Bool)
                                                                                                                                  then
                                                                                                                                    (currentlyEnabled
                                                                                                                                      Ext_H)
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((b__0 == (0x243#12 : (BitVec 12))) : Bool)
                                                                                                                                      then
                                                                                                                                        (currentlyEnabled
                                                                                                                                          Ext_H)
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((b__0 == (0x140#12 : (BitVec 12))) : Bool)
                                                                                                                                          then
                                                                                                                                            (currentlyEnabled
                                                                                                                                              Ext_S)
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if ((b__0 == (0x142#12 : (BitVec 12))) : Bool)
                                                                                                                                              then
                                                                                                                                                (currentlyEnabled
                                                                                                                                                  Ext_S)
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if ((b__0 == (0x143#12 : (BitVec 12))) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (currentlyEnabled
                                                                                                                                                      Ext_S)
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if ((b__0 == (0x607#12 : (BitVec 12))) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (currentlyEnabled
                                                                                                                                                          Ext_H)
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if ((b__0 == (0xE12#12 : (BitVec 12))) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (currentlyEnabled
                                                                                                                                                              Ext_H)
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if ((b__0 == (0x304#12 : (BitVec 12))) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (pure true)
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((b__0 == (0x344#12 : (BitVec 12))) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (pure true)
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((b__0 == (0x302#12 : (BitVec 12))) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                          Ext_S)
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((b__0 == (0x312#12 : (BitVec 12))) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (pure (delegh_csrs_are_defined && ((← (currentlyEnabled
                                                                                                                                                                                      Ext_S)) && (xlen == 32))))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((b__0 == (0x303#12 : (BitVec 12))) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                  Ext_S)
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((b__0 == (0x645#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                      Ext_H)
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((b__0 == (0x604#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                          Ext_H)
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if ((b__0 == (0x644#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                              Ext_H)
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if ((b__0 == (0x602#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                  Ext_H)
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if ((b__0 == (0x612#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (pure (delegh_csrs_are_defined && ((← (currentlyEnabled
                                                                                                                                                                                                              Ext_H)) && (xlen == 32))))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if ((b__0 == (0x603#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                          Ext_H)
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if ((b__0 == (0x144#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                              Ext_S)
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if ((b__0 == (0x104#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                                  Ext_S)
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if ((b__0 == (0x204#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                      Ext_H)
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if ((b__0 == (0x244#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                                          Ext_H)
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if ((b__0 == (0xB00#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (pure true)
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if ((b__0 == (0xB02#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (pure true)
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if ((b__0 == (0xB80#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (pure (xlen == 32))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if ((b__0 == (0xB82#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (pure (xlen == 32))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                                                   11
                                                                                                                                                                                                                                                   5) == (0b0011001#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                                                   4
                                                                                                                                                                                                                                                   0)
                                                                                                                                                                                                                                               ((BitVec.toNatInt
                                                                                                                                                                                                                                                   index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (pure true)
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                                                       11
                                                                                                                                                                                                                                                       5) == (0b1011000#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                                                       4
                                                                                                                                                                                                                                                       0)
                                                                                                                                                                                                                                                   ((BitVec.toNatInt
                                                                                                                                                                                                                                                       index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (pure true)
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                           11
                                                                                                                                                                                                                                                           5) == (0b1011100#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                           4
                                                                                                                                                                                                                                                           0)
                                                                                                                                                                                                                                                       ((BitVec.toNatInt
                                                                                                                                                                                                                                                           index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (pure (xlen == 32))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      if ((b__0 == (0x205#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                                                                          Ext_H)
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          if ((b__0 == (0x241#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                                                                              Ext_H)
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              if ((b__0 == (0x105#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                                                                                  Ext_S)
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  if ((b__0 == (0x141#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                                      Ext_S)
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      if ((b__0 == (0x305#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (pure true)
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          if ((b__0 == (0x341#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (pure true)
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              if (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                     b__0
                                                                                                                                                                                                                                                                                     11
                                                                                                                                                                                                                                                                                     4) == (0x3A#8 : (BitVec 8))) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (let idx : (BitVec 4) :=
                                                                                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                    b__0
                                                                                                                                                                                                                                                                                    3
                                                                                                                                                                                                                                                                                    0)
                                                                                                                                                                                                                                                                                (pure ((sys_pmp_count >b (4 *i (BitVec.toNatInt
                                                                                                                                                                                                                                                                                          idx))) && (((BitVec.access
                                                                                                                                                                                                                                                                                          idx
                                                                                                                                                                                                                                                                                          0) == 0#1) || (xlen == 32)))))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  if (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                         b__0
                                                                                                                                                                                                                                                                                         11
                                                                                                                                                                                                                                                                                         4) == (0x3B#8 : (BitVec 8))) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (let idx : (BitVec 4) :=
                                                                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                        b__0
                                                                                                                                                                                                                                                                                        3
                                                                                                                                                                                                                                                                                        0)
                                                                                                                                                                                                                                                                                    (pure (sys_pmp_count >b (BitVec.toNatInt
                                                                                                                                                                                                                                                                                          (0b00#2 +++ idx)))))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      if (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                             b__0
                                                                                                                                                                                                                                                                                             11
                                                                                                                                                                                                                                                                                             4) == (0x3C#8 : (BitVec 8))) : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (let idx : (BitVec 4) :=
                                                                                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                            b__0
                                                                                                                                                                                                                                                                                            3
                                                                                                                                                                                                                                                                                            0)
                                                                                                                                                                                                                                                                                        (pure (sys_pmp_count >b (BitVec.toNatInt
                                                                                                                                                                                                                                                                                              (0b01#2 +++ idx)))))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          if (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                 b__0
                                                                                                                                                                                                                                                                                                 11
                                                                                                                                                                                                                                                                                                 4) == (0x3D#8 : (BitVec 8))) : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (let idx : (BitVec 4) :=
                                                                                                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                b__0
                                                                                                                                                                                                                                                                                                3
                                                                                                                                                                                                                                                                                                0)
                                                                                                                                                                                                                                                                                            (pure (sys_pmp_count >b (BitVec.toNatInt
                                                                                                                                                                                                                                                                                                  (0b10#2 +++ idx)))))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              if (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                     b__0
                                                                                                                                                                                                                                                                                                     11
                                                                                                                                                                                                                                                                                                     4) == (0x3E#8 : (BitVec 8))) : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (let idx : (BitVec 4) :=
                                                                                                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                    b__0
                                                                                                                                                                                                                                                                                                    3
                                                                                                                                                                                                                                                                                                    0)
                                                                                                                                                                                                                                                                                                (pure (sys_pmp_count >b (BitVec.toNatInt
                                                                                                                                                                                                                                                                                                      (0b11#2 +++ idx)))))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x001#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                            Ext_F)) || (← (currentlyEnabled
                                                                                                                                                                                                                                                                                                            Ext_Zfinx))))
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x002#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                Ext_F)) || (← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                Ext_Zfinx))))
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x003#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                    Ext_F)) || (← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                    Ext_Zfinx))))
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x008#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                                                                                                                                  Ext_Zve32x)
                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x009#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                                                                                      Ext_Zve32x)
                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x00A#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                                                                                                                                          Ext_Zve32x)
                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x00F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                                                                                                                                              Ext_Zve32x)
                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0xC20#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                  Ext_Zve32x)
                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0xC21#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                      Ext_Zve32x)
                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0xC22#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                          Ext_Zve32x)
                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x321#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                              Ext_Smcntrpmf)
                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x721#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                        Ext_Smcntrpmf)) && (xlen == 32)))
                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x322#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                      Ext_Smcntrpmf)
                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x722#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                        (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                Ext_Smcntrpmf)) && (xlen == 32)))
                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x7A0#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                              Ext_Sdtrig)
                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x7A1#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                  Ext_Sdtrig)
                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x7A2#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                      Ext_Sdtrig)
                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x7A3#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                          Ext_Sdtrig)
                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x7A4#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                              Ext_Sdtrig)
                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x7A5#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                        Ext_Sdtrig)) && sdtrig_has_tcontrol))
                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x5A8#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                    (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                            Ext_Sdtrig)) && sdtrig_has_scontext))
                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x7A8#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                                        (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                Ext_Sdtrig)) && (sdtrig_has_mcontext || sdtrig_has_hcontext)))
                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x6A8#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                    Ext_Sdtrig)) && ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                      Ext_H)) && sdtrig_has_hcontext)))
                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x30C#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                                (pure (is_mstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                    ()))
                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x30D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                                    (pure (is_mstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                        ()))
                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x30E#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                                                        (pure (is_mstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                            ()))
                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x30F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                                                            (pure (is_mstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                ()))
                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x31C#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                                                (pure ((is_mstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                      ()) && (xlen == 32)))
                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x31D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                                                    (pure ((is_mstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                          ()) && (xlen == 32)))
                                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x31E#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                                                                        (pure ((is_mstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                              ()) && (xlen == 32)))
                                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x31F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                                                                            (pure ((is_mstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                  ()) && (xlen == 32)))
                                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x60C#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                                                                (is_hstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                  ())
                                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x60D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                                                                    (is_hstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                      ())
                                                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x60E#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                                                                                        (is_hstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                          ())
                                                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x60F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                                                                                            (is_hstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                              ())
                                                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x61C#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                                                                                (pure ((xlen == 32) && (← (is_hstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                                        ()))))
                                                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x61D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (pure ((xlen == 32) && (← (is_hstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                                            ()))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x61E#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (pure ((xlen == 32) && (← (is_hstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                                                ()))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x61F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (pure ((xlen == 32) && (← (is_hstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    ()))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x10C#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (is_sstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  ())
                                                                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x10D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (is_sstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      ())
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x10E#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (is_sstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          ())
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x10F#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (is_sstateen_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              ())
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x680#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        Ext_H)) && ((g__26 == Machine) || ((g__26 == Supervisor) && ((_get_Mstatus_TVM
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (← readReg mstatus)) == 0#1)))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x280#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      Ext_H)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x180#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (is_satp_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          g__26)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x015#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    Ext_Zkr)) && ((bne
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    g__27
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    CSRRead) && (← do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    match g__26 with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    | .Machine =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (pure true)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    | .User =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (pure ((_get_Seccfg_USEED
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (← readReg mseccfg)) == 1#1))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    | .Supervisor =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (pure ((_get_Seccfg_SSEED
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (← readReg mseccfg)) == 1#1))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    | .VirtualSupervisor =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    | .VirtualUser =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (pure false)))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       11
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       5) == (0b1100000#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       4
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       0)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   ((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      b__0
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      4
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      0)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Ext_Zihpm)) && (← (counter_enabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            index)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          g__26)))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           11
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           5) == (0b1100100#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           4
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           0)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       ((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          b__0
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          4
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          0)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              Ext_Zihpm)) && ((xlen == 32) && (← (counter_enabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  index)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                g__26))))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      if ((((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               11
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               5) == (0b0111001#7 : (BitVec 7))) && (let index : (BitVec 5) :=
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               4
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               0)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           ((BitVec.toNatInt
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               index) ≥b 3) : Bool)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                Ext_Sscofpmf)) && (xlen == 32)))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0xDA0#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    Ext_Sscofpmf)) && (← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    Ext_S))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x14D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (is_stimecmp_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  g__26)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0x15D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (pure ((← (is_stimecmp_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            g__26)) && (xlen == 32)))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0x24D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (is_vstimecmp_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          g__26)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x25D#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (pure ((← (is_vstimecmp_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    g__26)) && (xlen == 32)))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0x011#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (is_ssp_accessible
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  g__26)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0xC00#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            Ext_Zicntr)) && (← (counter_enabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            0
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            g__26))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0xC01#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                Ext_Zicntr)) && (← (counter_enabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                1
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                g__26))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0xC02#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    Ext_Zicntr)) && (← (counter_enabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    2
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    g__26))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              if ((b__0 == (0xC80#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        Ext_Zicntr)) && ((xlen == 32) && (← (counter_enabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          g__26)))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  if ((b__0 == (0xC81#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            Ext_Zicntr)) && ((xlen == 32) && (← (counter_enabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              1
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              g__26)))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      if ((b__0 == (0xC82#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                Ext_Zicntr)) && ((xlen == 32) && (← (counter_enabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  2
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  g__26)))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          if ((b__0 == (0x181#12 : (BitVec 12))) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (pure ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    Ext_Ssqosid)) && ((bne
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    g__26
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    VirtualSupervisor) && (bne
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    g__26
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    VirtualUser))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (pure false)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def check_CSR (csr : (BitVec 12)) (p : Privilege) (access_type : CSRAccessType) : SailM Bool := do
  (pure ((← (check_CSR_priv csr p)) && ((check_CSR_access csr access_type) && ((← (is_CSR_accessible
              csr p access_type)) && (← (stateen_allows_CSR_access csr p access_type))))))

def is_CSR_exception_virtual (arg0 : (BitVec 12)) (arg1 : Privilege) (arg2 : CSRAccessType) : SailM Bool := do
  let merge_var := (arg0, arg1, arg2)
  match merge_var with
  | (0x001, g__2, g__3) => (pure false)
  | (0x002, g__4, g__5) => (pure false)
  | (0x003, g__6, g__7) => (pure false)
  | (0x008, g__8, g__9) => (pure false)
  | (0x009, g__10, g__11) => (pure false)
  | (0x00A, g__12, g__13) => (pure false)
  | (0x00F, g__14, g__15) => (pure false)
  | (0xC20, g__16, g__17) => (pure false)
  | (0xC21, g__18, g__19) => (pure false)
  | (0xC22, g__20, g__21) => (pure false)
  | (0x680, g__22, g__23) => (pure true)
  | (0x180, g__24, g__25) => (pure true)
  | (csr, _, access_type) => (check_CSR csr Supervisor access_type)

def check_CSR_result (csr : (BitVec 12)) (p : Privilege) (access_type : CSRAccessType) : SailM CSRCheckResult := do
  if ((← (check_CSR csr p access_type)) : Bool)
  then (pure (CSR_Check_OK ()))
  else
    (do
      if ((((p == VirtualSupervisor) || (p == VirtualUser)) && (← (is_CSR_exception_virtual csr p
               access_type))) : Bool)
      then (pure (CSR_Virtual ()))
      else (pure (CSR_Illegal ())))

def exception_delegatee (e : ExceptionType) (p : Privilege) : SailM Privilege := do
  let idx := (BitVec.toNatInt (exceptionType_bits_forwards e))
  let super ← do (pure (bit_to_bool (BitVec.access (← readReg medeleg) idx)))
  let virtual ← do
    (pure ((bit_to_bool (BitVec.access (← readReg hedeleg) idx)) && (← (inVirtualPrivilege ()))))
  let deleg ← do
    if (((← (currentlyEnabled Ext_S)) && super) : Bool)
    then
      (do
        if (((← (currentlyEnabled Ext_H)) && virtual) : Bool)
        then (pure VirtualSupervisor)
        else (pure Supervisor))
    else (pure Machine)
  if ((zopz0zKzJ_u (privLevel_to_bits deleg) (privLevel_to_bits p)) : Bool)
  then (pure deleg)
  else (pure p)

def findPendingInterrupt (ip : (BitVec 32)) : (Option InterruptType) :=
  let ip := (Mk_Minterrupts ip)
  if (((_get_Minterrupts_MEI ip) == 1#1) : Bool)
  then (some I_M_External)
  else
    (if (((_get_Minterrupts_MSI ip) == 1#1) : Bool)
    then (some I_M_Software)
    else
      (if (((_get_Minterrupts_MTI ip) == 1#1) : Bool)
      then (some I_M_Timer)
      else
        (if (((_get_Minterrupts_SEI ip) == 1#1) : Bool)
        then (some I_S_External)
        else
          (if (((_get_Minterrupts_SSI ip) == 1#1) : Bool)
          then (some I_S_Software)
          else
            (if (((_get_Minterrupts_STI ip) == 1#1) : Bool)
            then (some I_S_Timer)
            else
              (if (((_get_Minterrupts_SGEI ip) == 1#1) : Bool)
              then (some I_SG_External)
              else
                (if (((_get_Minterrupts_VSEI ip) == 1#1) : Bool)
                then (some I_VS_External)
                else
                  (if (((_get_Minterrupts_VSSI ip) == 1#1) : Bool)
                  then (some I_VS_Software)
                  else
                    (if (((_get_Minterrupts_VSTI ip) == 1#1) : Bool)
                    then (some I_VS_Timer)
                    else
                      (if (((_get_Minterrupts_LCOFI ip) == 1#1) : Bool)
                      then (some I_COF)
                      else none))))))))))

def getPendingSet (priv : Privilege) : SailM (Option ((BitVec 32) × Privilege)) := do
  let mideleg_bits ← do
    if ((← (currentlyEnabled Ext_S)) : Bool)
    then readReg mideleg
    else (pure (zeros (n := 32)))
  let pending ← do (pure ((← (read_mip IncludePlatformInterrupts)) &&& (← readReg mie)))
  let pending_m := (pending &&& (Complement.complement mideleg_bits))
  let pending_s ← do
    (pure (pending &&& (mideleg_bits &&& (Complement.complement (← readReg hideleg)))))
  let pending_vs ← do (pure (pending &&& (mideleg_bits &&& (← readReg hideleg))))
  let mIE ← do
    (pure (((priv == Machine) && ((_get_Mstatus_MIE (← readReg mstatus)) == 1#1)) || (bne priv
          Machine)))
  let sIE ← do
    (pure (((priv == Supervisor) && ((_get_Mstatus_SIE (← readReg mstatus)) == 1#1)) || ((priv == User) || ((priv == VirtualSupervisor) || (priv == VirtualUser)))))
  let vsIE ← do
    (pure (((priv == VirtualSupervisor) && ((_get_Mstatus_SIE (← readReg vsstatus)) == 1#1)) || (priv == VirtualUser)))
  if ((mIE && (pending_m != (zeros (n := 32)))) : Bool)
  then (pure (some (pending_m, Machine)))
  else
    (if ((sIE && (pending_s != (zeros (n := 32)))) : Bool)
    then (pure (some (pending_s, Supervisor)))
    else
      (if ((vsIE && (pending_vs != (zeros (n := 32)))) : Bool)
      then
        (let vs := (Mk_Minterrupts pending_vs)
        let translated :=
          (_update_Minterrupts_VSTI
            (_update_Minterrupts_STI
              (_update_Minterrupts_VSSI
                (_update_Minterrupts_SSI
                  (_update_Minterrupts_VSEI (_update_Minterrupts_SEI vs (_get_Minterrupts_VSEI vs))
                    0#1) (_get_Minterrupts_VSSI vs)) 0#1) (_get_Minterrupts_VSTI vs)) 0#1)
        (pure (some (translated, VirtualSupervisor))))
      else (pure none)))

def shouldWakeForInterrupt (_ : Unit) : SailM Bool := do
  (pure (((← (read_mip IncludePlatformInterrupts)) &&& (← readReg mie)) != (zeros (n := 32))))

def dispatchInterrupt (priv : Privilege) : SailM (Option (InterruptType × Privilege)) := do
  match (← (getPendingSet priv)) with
  | none => (pure none)
  | .some (ip, p) =>
    (match (findPendingInterrupt ip) with
    | none => (pure none)
    | .some i => (pure (some (i, p))))

def tval (excinfo : (Option (BitVec 32))) : (BitVec 32) :=
  match excinfo with
  | .some e => e
  | none => (zeros (n := 32))

/-- Type quantifiers: k_ex1822015_ : Bool -/
def track_trap (p : Privilege) (is_interrupt : Bool) (cause : (BitVec 6)) : SailM Unit := do
  (long_csr_write_callback "mstatus" "mstatush" (← (read_mstatus ())))
  match p with
  | .Machine =>
    (do
      (csr_name_write_callback "mcause" (← readReg mcause))
      (csr_name_write_callback "mtval" (← readReg mtval))
      (csr_name_write_callback "mepc" (← readReg mepc))
      if ((← (currentlyEnabled Ext_H)) : Bool)
      then
        (do
          (csr_name_write_callback "mtval2" (← readReg mtval2))
          (csr_name_write_callback "mtinst" (← readReg mtinst)))
      else (pure ()))
  | .Supervisor =>
    (do
      (csr_name_write_callback "scause" (← readReg scause))
      (csr_name_write_callback "stval" (← readReg stval))
      (csr_name_write_callback "sepc" (← readReg sepc))
      if ((← (currentlyEnabled Ext_H)) : Bool)
      then
        (do
          (csr_name_write_callback "hstatus"
            (Sail.BitVec.extractLsb (← readReg hstatus) (xlen -i 1) 0))
          (csr_name_write_callback "htval" (← readReg htval))
          (csr_name_write_callback "htinst" (← readReg htinst)))
      else (pure ()))
  | .User => (internal_error "sys/sys_control.sail" 216 "Invalid privilege level")
  | .VirtualUser => (internal_error "sys/sys_control.sail" 217 "Invalid privilege level")
  | .VirtualSupervisor =>
    (do
      (csr_name_write_callback "vscause" (← readReg vscause))
      (csr_name_write_callback "vstval" (← readReg vstval))
      (csr_name_write_callback "vsepc" (← readReg vsepc))
      (csr_name_write_callback "vsstatus"
        (Sail.BitVec.extractLsb (← readReg vsstatus) (xlen -i 1) 0)))
  (pure (trap_callback is_interrupt cause))

def xtval_exception_value (e : ExceptionType) (excinfo : (BitVec 32)) : (Option (BitVec 32)) :=
  if ((match e with
     | .E_Illegal_Instr () => illegal_instruction_writes_xtval
     | .E_Virtual_Instr () => virtual_instruction_writes_xtval
     | .E_Breakpoint .Brk_Software => software_breakpoint_writes_xtval
     | .E_Breakpoint .Brk_Hardware => hardware_breakpoint_writes_xtval
     | .E_Load_Addr_Align () => misaligned_load_writes_xtval
     | .E_Load_Access_Fault () => load_access_fault_writes_xtval
     | .E_Load_Page_Fault () => load_page_fault_writes_xtval
     | .E_Load_GPage_Fault () => load_guest_page_fault_writes_xtval
     | .E_SAMO_Addr_Align () => misaligned_samo_writes_xtval
     | .E_SAMO_Access_Fault () => samo_access_fault_writes_xtval
     | .E_SAMO_Page_Fault () => samo_page_fault_writes_xtval
     | .E_SAMO_GPage_Fault () => samo_guest_page_fault_writes_xtval
     | .E_Fetch_Addr_Align () => misaligned_fetch_writes_xtval
     | .E_Fetch_Access_Fault () => fetch_access_fault_writes_xtval
     | .E_Fetch_Page_Fault () => fetch_page_fault_writes_xtval
     | .E_Fetch_GPage_Fault () => fetch_guest_page_fault_writes_xtval
     | .E_Software_Check () => software_check_exception_writes_xtval
     | .E_Hardware_Error () => hardware_error_exception_writes_xtval
     | .E_U_EnvCall () => false
     | .E_S_EnvCall () => false
     | .E_VS_EnvCall () => false
     | .E_M_EnvCall () => false
     | .E_Extension _ => true
     | .E_Double_Trap () => true
     | .E_Reserved_14 () => reserved_exceptions_write_xtval
     | .E_Reserved_17 () => reserved_exceptions_write_xtval) : Bool)
  then (some excinfo)
  else none

def trap_handler_inner (del_priv : Privilege) (c : TrapCause) (pc : (BitVec 32)) : SailM (BitVec 32) := do
  let is_interrupt := (trapCause_is_interrupt c)
  let cause := (trapCause_bits c)
  let (excinfo_is_gva, excinfo, excinfo2, excinst, ext) : (Bool × (Option xlenbits) × (Option xlenbits) × (Option xlenbits) × (Option ext_exception)) :=
    match c with
    | .Interrupt _ => (false, (some (zeros (n := 32))), none, none, none)
    | .Exception ctx =>
      (ctx.excinfo_is_gva, (xtval_exception_value ctx.trap ctx.excinfo), ctx.excinfo2, ctx.excinst, ctx.ext)
  if (((get_config_print_exception ()) || (get_config_print_interrupt ())) : Bool)
  then
    (pure (print_endline
        (HAppend.hAppend "handling "
          (HAppend.hAppend (trapCause_to_str c)
            (HAppend.hAppend " at priv "
              (HAppend.hAppend (← (privLevel_to_str del_priv))
                (HAppend.hAppend " | tval="
                  (HAppend.hAppend (BitVec.toFormatted (tval excinfo))
                    (HAppend.hAppend " | tval2="
                      (HAppend.hAppend (BitVec.toFormatted (tval excinfo2))
                        (HAppend.hAppend " | tinst=" (BitVec.toFormatted (tval excinst)))))))))))))
  else (pure ())
  if ((hartSupports Ext_Zicfilp) : Bool)
  then (zicfilp_preserve_elp_on_trap del_priv)
  else (pure ())
  (generate_trap_event c)
  let prev_priv ← do readReg cur_privilege
  (match_icount_triggers prev_priv (← (prevent_reentrance TA_Breakpoint prev_priv)))
  let tvec ← (( do
    match del_priv with
    | .Machine =>
      (do
        writeReg mcause (Sail.BitVec.updateSubrange (← readReg mcause) (32 -i 1) (32 -i 1)
          (bool_to_bit is_interrupt))
        writeReg mcause (Sail.BitVec.updateSubrange (← readReg mcause) (32 -i 2) 0
          (zero_extend (m := (32 -i 1)) cause))
        writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 7 7
          (_get_Mstatus_MIE (← readReg mstatus)))
        writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3 0#1)
        writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 12 11
          (privLevel_to_bits (← readReg cur_privilege)))
        writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 39 39
          (bool_to_bit (← (inVirtualPrivilege ()))))
        writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 38 38
          (bool_to_bit excinfo_is_gva))
        writeReg mtval (tval excinfo)
        writeReg mtval2 (tval excinfo2)
        writeReg mtinst (tval excinst)
        writeReg mepc pc
        writeReg cur_privilege del_priv
        let _ : Unit := (handle_trap_extension del_priv pc ext)
        if ((← (currentlyEnabled Ext_Sdtrig)) : Bool)
        then (tcontrol_trap_into_mmode ())
        else (pure ())
        (track_trap del_priv is_interrupt cause)
        (prepare_trap_vector del_priv (← readReg mcause)))
    | .Supervisor =>
      (do
        «assert» (← (currentlyEnabled Ext_S)) "no supervisor mode present for delegation"
        writeReg scause (Sail.BitVec.updateSubrange (← readReg scause) (32 -i 1) (32 -i 1)
          (bool_to_bit is_interrupt))
        writeReg scause (Sail.BitVec.updateSubrange (← readReg scause) (32 -i 2) 0
          (zero_extend (m := (32 -i 1)) cause))
        writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 5 5
          (_get_Mstatus_SIE (← readReg mstatus)))
        writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 1 1 0#1)
        writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 8 8
          (← do
            match (← readReg cur_privilege) with
            | .User => (pure 0#1)
            | .VirtualUser => (pure 0#1)
            | .Supervisor => (pure 1#1)
            | .VirtualSupervisor => (pure 1#1)
            | .Machine =>
              (internal_error "sys/sys_control.sail" 331 "invalid privilege for s-mode trap")))
        writeReg hstatus (Sail.BitVec.updateSubrange (← readReg hstatus) 7 7
          (bool_to_bit (← (inVirtualPrivilege ()))))
        writeReg hstatus (Sail.BitVec.updateSubrange (← readReg hstatus) 8 8
          (← do
            if ((← (inVirtualPrivilege ())) : Bool)
            then (pure (_get_Mstatus_SPP (← readReg mstatus)))
            else (pure (_get_Hstatus_SPVP (← readReg hstatus)))))
        writeReg hstatus (Sail.BitVec.updateSubrange (← readReg hstatus) 6 6
          (bool_to_bit excinfo_is_gva))
        writeReg stval (tval excinfo)
        writeReg htval (tval excinfo2)
        writeReg htinst (tval excinst)
        writeReg sepc pc
        writeReg cur_privilege del_priv
        let _ : Unit := (handle_trap_extension del_priv pc ext)
        (track_trap del_priv is_interrupt cause)
        (prepare_trap_vector del_priv (← readReg scause)))
    | .User => (internal_error "sys/sys_control.sail" 351 "Invalid privilege level")
    | .VirtualUser => (internal_error "sys/sys_control.sail" 352 "Invalid privilege level")
    | .VirtualSupervisor =>
      (do
        «assert» (← (currentlyEnabled Ext_H)) "no hypervisor-extended supervisor mode present for delegation"
        writeReg vscause (Sail.BitVec.updateSubrange (← readReg vscause) (32 -i 1) (32 -i 1)
          (bool_to_bit is_interrupt))
        writeReg vscause (Sail.BitVec.updateSubrange (← readReg vscause) (32 -i 2) 0
          (zero_extend (m := (32 -i 1)) cause))
        writeReg vsstatus (Sail.BitVec.updateSubrange (← readReg vsstatus) 5 5
          (_get_Mstatus_SIE (← readReg vsstatus)))
        writeReg vsstatus (Sail.BitVec.updateSubrange (← readReg vsstatus) 1 1 0#1)
        writeReg vsstatus (Sail.BitVec.updateSubrange (← readReg vsstatus) 8 8
          (← do
            match (← readReg cur_privilege) with
            | .VirtualUser => (pure 0#1)
            | .VirtualSupervisor => (pure 1#1)
            | _ => (internal_error "sys/sys_control.sail" 364 "invalid privilege for vs-mode trap")))
        writeReg vsepc pc
        writeReg vstval (tval excinfo)
        writeReg cur_privilege del_priv
        let _ : Unit := (handle_trap_extension del_priv pc ext)
        (track_trap del_priv is_interrupt cause)
        (prepare_trap_vector del_priv (← readReg vscause))) ) : SailM xlenbits )
  match c with
  | .Interrupt intr => (match_itrigger_triggers intr prev_priv del_priv)
  | .Exception ctx => (match_etrigger_triggers ctx.trap prev_priv del_priv)
  (pure tvec)

def machine_trap_set_mdt (_ : Unit) : SailM Unit := do
  if ((← (currentlyEnabled Ext_Smdbltrp)) : Bool)
  then
    (do
      if (((_get_Mstatus_MDT (← readReg mstatus)) == 0#1) : Bool)
      then writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 42 42 1#1)
      else «assert» false "unexpected trap taken in machine mode")
  else (pure ())

def double_trap_cause (c : TrapCause) : TrapCause :=
  let unexpected_cause :=
    (_update_Mcause_Cause
      (_update_Mcause_IsInterrupt (Mk_Mcause (zeros (n := 32)))
        (bool_to_bit (trapCause_is_interrupt c))) (zero_extend (m := (32 -i 1)) (trapCause_bits c)))
  (Exception
    (match c with
    | .Interrupt _ =>
      { trap := (E_Double_Trap ())
        excinfo_is_gva := false
        excinfo := (zeros (n := 32))
        excinfo2 := (some unexpected_cause)
        excinst := none
        excinst_offset := (zeros (n := 5))
        ext := none }
    | .Exception e =>
      { trap := (E_Double_Trap ())
        excinfo_is_gva := e.excinfo_is_gva
        excinfo := (tval (xtval_exception_value e.trap e.excinfo))
        excinfo2 := (some unexpected_cause)
        excinst := e.excinst
        excinst_offset := e.excinst_offset
        ext := e.ext }))

def trap_handler (del_priv : Privilege) (c : TrapCause) (pc : (BitVec 32)) : SailM (BitVec 32) := SailME.run do
  match del_priv with
  | .Machine => (machine_trap_set_mdt ())
  | .Supervisor =>
    (do
      if ((← (currentlyEnabled Ext_Ssdbltrp)) : Bool)
      then
        (do
          if (((_get_Mstatus_SDT (← readReg mstatus)) == 0#1) : Bool)
          then writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 24 24 1#1)
          else
            SailME.throw (← do
                (machine_trap_set_mdt ())
                (trap_handler_inner Machine (double_trap_cause c) pc)))
      else (pure ()))
  | .VirtualSupervisor =>
    (do
      if (((← (currentlyEnabled Ext_Ssdbltrp)) && ((_get_HEnvcfg_DTE (← (read_henvcfg ()))) == 1#1)) : Bool)
      then
        (do
          if (((_get_Mstatus_SDT (← readReg vsstatus)) == 0#1) : Bool)
          then writeReg vsstatus (Sail.BitVec.updateSubrange (← readReg vsstatus) 24 24 1#1)
          else
            SailME.throw (← do
                (machine_trap_set_mdt ())
                (trap_handler_inner Machine (double_trap_cause c) pc)))
      else (pure ()))
  | .User => (pure ())
  | .VirtualUser => (pure ())
  (trap_handler_inner del_priv c pc)

def exception_handler (cur_priv : Privilege) (exc_context : ExceptionContext) (pc : (BitVec 32)) : SailM (BitVec 32) := do
  let del_priv ← do (exception_delegatee exc_context.trap cur_priv)
  if ((get_config_print_exception ()) : Bool)
  then
    (pure (print_endline
        (HAppend.hAppend "trapping from "
          (HAppend.hAppend (← (privLevel_to_str cur_priv))
            (HAppend.hAppend " to "
              (HAppend.hAppend (← (privLevel_to_str del_priv))
                (HAppend.hAppend " to handle " (exceptionType_to_str exc_context.trap))))))))
  else (pure ())
  (trap_handler del_priv (Exception exc_context) pc)

def handle_exception (c : ExceptionContext) : SailM Unit := do
  (set_next_pc (← (exception_handler (← readReg cur_privilege) c (← readReg PC))))

def handle_interrupt (i : InterruptType) (del_priv : Privilege) : SailM Unit := do
  (set_next_pc (← (trap_handler del_priv (Interrupt i) (← readReg PC))))

def reset_misa (_ : Unit) : SailM Unit := do
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 0 0
    (bool_to_bit (hartSupports Ext_A)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 2 2
    (bool_to_bit (hartSupports Ext_C)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 1 1
    (bool_to_bit (hartSupports Ext_B)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 7 7
    (bool_to_bit (hartSupports Ext_H)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 12 12
    (bool_to_bit (hartSupports Ext_M)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 20 20
    (bool_to_bit (hartSupports Ext_U)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 18 18
    (bool_to_bit (hartSupports Ext_S)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 21 21
    (bool_to_bit (hartSupports Ext_V)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 4 4 (bool_to_bit base_E_enabled))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 8 8
    (Complement.complement (_get_Misa_E (← readReg misa))))
  if (((hartSupports Ext_F) && (hartSupports Ext_Zfinx)) : Bool)
  then (internal_error "sys/sys_control.sail" 510 "F and Zfinx cannot both be enabled!")
  else (pure ())
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 5 5
    (bool_to_bit (hartSupports Ext_F)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 3 3
    (bool_to_bit (hartSupports Ext_D)))
  (csr_name_write_callback "misa" (← readReg misa))

def set_pc_reset_address (addr : (BitVec 64)) : SailM Unit := do
  writeReg pc_reset_address (trunc (m := 32) addr)

def reset_sys (_ : Unit) : SailM Unit := do
  writeReg cur_privilege Machine
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3 0#1)
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
  if ((hartSupports Ext_Smdbltrp) : Bool)
  then writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 42 42 1#1)
  else (pure ())
  (reset_tvecs ())
  (long_csr_write_callback "mstatus" "mstatush" (← (read_mstatus ())))
  (reset_misa ())
  (cancel_reservation ())
  writeReg PC (← readReg pc_reset_address)
  writeReg nextPC (← readReg pc_reset_address)
  writeReg mcause (zeros (n := 32))
  (csr_name_write_callback "mcause" (← readReg mcause))
  (reset_pmp ())
  writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 9 9
    (bool_to_bit (false : Bool)))
  writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 8 8
    (bool_to_bit (false : Bool)))
  if ((hartSupports Ext_Zicfilp) : Bool)
  then writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 10 10 0#1)
  else (pure ())
  (reset_stateen ())
  writeReg vstart (zeros (n := 32))
  writeReg vl (zeros (n := 32))
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 2 1 0b00#2)
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 0 0 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) (32 -i 1) (32 -i 1) 1#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) (32 -i 2) 8
    (zeros (n := (32 -i 9))))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 7 7 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 6 6 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 5 3 0b000#3)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 2 0 0b000#3)

/-- Type quantifiers: k_t : Type -/
def MemoryOpResult_add_meta (r : (Result k_t (physaddr × ExceptionType))) (m : Unit) : (Result (k_t × Unit) (physaddr × ExceptionType)) :=
  match r with
  | .Ok v => (Ok (v, m))
  | .Err e => (Err e)

/-- Type quantifiers: k_t : Type -/
def MemoryOpResult_drop_meta (r : (Result (k_t × Unit) (physaddr × ExceptionType))) : (Result k_t (physaddr × ExceptionType)) :=
  match r with
  | .Ok (v, _m) => (Ok v)
  | .Err e => (Err e)

