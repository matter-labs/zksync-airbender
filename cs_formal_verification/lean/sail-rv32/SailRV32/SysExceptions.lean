import SailRV32.Errors
import SailRV32.PlatformConfig
import SailRV32.Types
import SailRV32.SysRegs

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

def ext_check_xret_priv (_p : Privilege) : Bool :=
  true

def ext_fail_xret_priv (_ : Unit) : Unit :=
  ()

def handle_trap_extension (_p : Privilege) (_pc : (BitVec 32)) (_u : (Option Unit)) : Unit :=
  ()

def prepare_trap_vector (p : Privilege) (cause : (BitVec 32)) : SailM (BitVec 32) := do
  let tvec ← (( do
    match p with
    | .Machine => readReg mtvec
    | .Supervisor => readReg stvec
    | .User => (internal_error "exceptions/sys_exceptions.sail" 21 "Invalid privilege level")
    | .VirtualUser => (internal_error "exceptions/sys_exceptions.sail" 22 "Invalid privilege level")
    | .VirtualSupervisor => readReg vstvec ) : SailM Mtvec )
  match (tvec_addr tvec cause) with
  | .some epc => (pure epc)
  | none => (internal_error "exceptions/sys_exceptions.sail" 27 "Invalid tvec mode")

def get_xepc (p : Privilege) : SailM (BitVec 32) := do
  match p with
  | .Machine => (align_pc (← readReg mepc))
  | .Supervisor => (align_pc (← readReg sepc))
  | .User => (internal_error "exceptions/sys_exceptions.sail" 41 "Invalid privilege level")
  | .VirtualUser => (internal_error "exceptions/sys_exceptions.sail" 42 "Invalid privilege level")
  | .VirtualSupervisor => (align_pc (← readReg vsepc))

def set_xepc (p : Privilege) (value : (BitVec 32)) : SailM (BitVec 32) := do
  let target := (legalize_xepc value)
  match p with
  | .Machine => writeReg mepc target
  | .Supervisor => writeReg sepc target
  | .User => (internal_error "exceptions/sys_exceptions.sail" 51 "Invalid privilege level")
  | .VirtualUser => (internal_error "exceptions/sys_exceptions.sail" 52 "Invalid privilege level")
  | .VirtualSupervisor => writeReg vsepc target
  (pure target)

def prepare_xret_target (p : Privilege) : SailM (BitVec 32) := do
  (get_xepc p)

def get_mtvec (_ : Unit) : SailM (BitVec 32) := do
  readReg mtvec

def get_stvec (_ : Unit) : SailM (BitVec 32) := do
  readReg stvec

def get_vstvec (_ : Unit) : SailM (BitVec 32) := do
  readReg vstvec

def set_mtvec (value : (BitVec 32)) : SailM (BitVec 32) := do
  writeReg mtvec (← (legalize_tvec (← readReg mtvec) value plat_mtvec_direct_mode_supported
      plat_mtvec_direct_base_alignment_exp plat_mtvec_vectored_mode_supported
      plat_mtvec_vectored_base_alignment_exp))
  readReg mtvec

def set_stvec (value : (BitVec 32)) : SailM (BitVec 32) := do
  writeReg stvec (← (legalize_tvec (← readReg stvec) value plat_stvec_direct_mode_supported 2
      plat_stvec_vectored_mode_supported plat_stvec_vectored_base_alignment_exp))
  readReg stvec

def set_vstvec (value : (BitVec 32)) : SailM (BitVec 32) := do
  writeReg vstvec (← (legalize_tvec (← readReg vstvec) value plat_vstvec_direct_mode_supported 2
      plat_vstvec_vectored_mode_supported plat_vstvec_vectored_base_alignment_exp))
  readReg vstvec

def reset_tvecs (_ : Unit) : SailM Unit := do
  if (plat_mtvec_direct_mode_supported : Bool)
  then
    writeReg mtvec (Sail.BitVec.updateSubrange (← readReg mtvec) 1 0
      (trapVectorMode_backwards TV_Direct))
  else
    (do
      if (plat_mtvec_vectored_mode_supported : Bool)
      then
        writeReg mtvec (Sail.BitVec.updateSubrange (← readReg mtvec) 1 0
          (trapVectorMode_backwards TV_Vector))
      else (pure ()))
  if (plat_stvec_direct_mode_supported : Bool)
  then
    writeReg stvec (Sail.BitVec.updateSubrange (← readReg stvec) 1 0
      (trapVectorMode_backwards TV_Direct))
  else
    (do
      if (plat_stvec_vectored_mode_supported : Bool)
      then
        writeReg stvec (Sail.BitVec.updateSubrange (← readReg stvec) 1 0
          (trapVectorMode_backwards TV_Vector))
      else (pure ()))
  if (plat_vstvec_direct_mode_supported : Bool)
  then
    writeReg vstvec (Sail.BitVec.updateSubrange (← readReg vstvec) 1 0
      (trapVectorMode_backwards TV_Direct))
  else
    (do
      if (plat_vstvec_vectored_mode_supported : Bool)
      then
        writeReg vstvec (Sail.BitVec.updateSubrange (← readReg vstvec) 1 0
          (trapVectorMode_backwards TV_Vector))
      else (pure ()))

