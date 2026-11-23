import SailRV32.Option
import SailRV32.Prelude
import SailRV32.PlatformConfig
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

def allows_transformed_instruction (e : ExceptionType) : Bool :=
  match e with
  | .E_Load_Addr_Align () => sys_misaligned_load_writes_tinst
  | .E_Load_Access_Fault () => sys_load_access_fault_writes_tinst
  | .E_SAMO_Addr_Align () => sys_misaligned_samo_writes_tinst
  | .E_SAMO_Access_Fault () => sys_samo_access_fault_writes_tinst
  | .E_Load_Page_Fault () => sys_load_page_fault_writes_tinst
  | .E_SAMO_Page_Fault () => sys_samo_page_fault_writes_tinst
  | .E_Load_GPage_Fault () => sys_load_guest_page_fault_writes_tinst
  | .E_SAMO_GPage_Fault () => sys_samo_guest_page_fault_writes_tinst
  | _ => false

def transformed_instruction (insn : instruction) : SailM (Option (BitVec 32)) := do
  match insn with
  | .LOAD (_, _, rd, is_unsigned, width) =>
    (pure (some (← (encdec_forwards (LOAD ((zeros (n := 12)), zreg, rd, is_unsigned, width))))))
  | .STORE (_, rs2, _, width) =>
    (pure (some (← (encdec_forwards (STORE ((zeros (n := 12)), rs2, zreg, width))))))
  | .LOAD_FP (_, _, rd, width) =>
    (pure (some (← (encdec_forwards (LOAD_FP ((zeros (n := 12)), zreg, rd, width))))))
  | .STORE_FP (_, rs2, _, width) =>
    (pure (some (← (encdec_forwards (STORE_FP ((zeros (n := 12)), rs2, zreg, width))))))
  | .LOADRES (aq, rl, _, width, rd) =>
    (pure (some (← (encdec_forwards (LOADRES (aq, rl, zreg, width, rd))))))
  | .STORECON (aq, rl, rs2, _, width, rd) =>
    (pure (some (← (encdec_forwards (STORECON (aq, rl, rs2, zreg, width, rd))))))
  | .AMO (op, aq, rl, rs2, _, width, rd) =>
    (pure (some (← (encdec_forwards (AMO (op, aq, rl, rs2, zreg, width, rd))))))
  | .HLVTYPE (width, op, is_unsigned, _, rd) =>
    (pure (some (← (encdec_forwards (HLVTYPE (width, op, is_unsigned, zreg, rd))))))
  | .HSV (width, _, rs2) => (pure (some (← (encdec_forwards (HSV (width, zreg, rs2))))))
  | .ZICBOM (cbop, _) => (pure (some (← (encdec_forwards (ZICBOM (cbop, zreg))))))
  | .ZICBOZ _ => (pure (some (← (encdec_forwards (ZICBOZ zreg)))))
  | _ => (pure none)

def transform_exception_context (ctx : ExceptionContext) (instr_info : instr_info) : SailM ExceptionContext := do
  if ((not ((← (currentlyEnabled Ext_H)) && (allows_transformed_instruction ctx.trap))) : Bool)
  then (pure ctx)
  else
    (do
      if ((is_some ctx.excinst) : Bool)
      then (pure ctx)
      else
        (do
          match instr_info.executed_instruction with
          | none => (pure ctx)
          | .some instruction =>
            (do
              match (← (transformed_instruction instruction)) with
              | none => (pure ctx)
              | .some tinst =>
                (let tinst := (Sail.BitVec.updateSubrange tinst 19 15 ctx.excinst_offset)
                let tinst :=
                  if (instr_info.compressed : Bool)
                  then (BitVec.update tinst 1 0#1)
                  else tinst
                (pure { ctx with excinst := (some (zero_extend (m := 32) tinst)) })))))

