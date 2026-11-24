import SailRV32.Prelude
import SailRV32.Errors
import SailRV32.Xlen
import SailRV32.TypesExt
import SailRV32.Types
import SailRV32.VmemTypes
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

def ext_get_ptw_error (failure : pte_check_failure) : PTW_Error :=
  match failure with
  | .PTE_No_Permission () => (PTW_No_Permission ())
  | .PTE_No_Access () => (PTW_No_Access ())
  | .PTE_Ext_Failure _ => (PTW_No_Permission ())

def convertToGuestException (e : ExceptionType) : ExceptionType :=
  match e with
  | .E_Fetch_Page_Fault () => (E_Fetch_GPage_Fault ())
  | .E_Load_Page_Fault () => (E_Load_GPage_Fault ())
  | .E_SAMO_Page_Fault () => (E_SAMO_GPage_Fault ())
  | _ => e

def g_stage_tval2_exception_value (trap : ExceptionType) (gpa : (BitVec (if ( 32 = 32  : Bool) then 34 else 64))) : (BitVec 32) :=
  if (((is_guest_page_fault trap) && sys_guest_page_fault_writes_htval) : Bool)
  then (Sail.BitVec.truncate (gpa >>> 2) xlen)
  else (zeros (n := 32))

def translationException (access : (MemoryAccessType mem_payload)) (err : PTW_Error) : SailM ExceptionType := do
  match (access, err) with
  | (_, .PTW_Ext_Error e) => (pure (E_Extension (ext_translate_exception e)))
  | (.Atomic (_, _, _, .Data, .Data), .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.Atomic (_, _, _, .Data, .Data), _) => (pure (E_SAMO_Page_Fault ()))
  | (.Load .Data, .PTW_No_Access ()) => (pure (E_Load_Access_Fault ()))
  | (.Load .Data, _) => (pure (E_Load_Page_Fault ()))
  | (.Load .Vector, .PTW_No_Access ()) => (pure (E_Load_Access_Fault ()))
  | (.Load .Vector, _) => (pure (E_Load_Page_Fault ()))
  | (.Load .PageTableEntry, .PTW_No_Access ()) => (pure (E_Load_Access_Fault ()))
  | (.Load .PageTableEntry, _) => (pure (E_Load_Page_Fault ()))
  | (.LoadExecute .Data, .PTW_No_Access ()) => (pure (E_Load_Access_Fault ()))
  | (.LoadExecute .Data, _) => (pure (E_Load_Page_Fault ()))
  | (.LoadReserved (_, _, .Data), .PTW_No_Access ()) => (pure (E_Load_Access_Fault ()))
  | (.LoadReserved (_, _, .Data), _) => (pure (E_Load_Page_Fault ()))
  | (.Store .Data, .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.Store .Data, _) => (pure (E_SAMO_Page_Fault ()))
  | (.Store .Vector, .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.Store .Vector, _) => (pure (E_SAMO_Page_Fault ()))
  | (.Store .PageTableEntry, .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.Store .PageTableEntry, _) => (pure (E_SAMO_Page_Fault ()))
  | (.StoreConditional (_, _, .Data), .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.StoreConditional (_, _, .Data), _) => (pure (E_SAMO_Page_Fault ()))
  | (.Atomic (_, _, _, .ShadowStack, .ShadowStack), .PTW_No_Access ()) =>
    (pure (E_SAMO_Access_Fault ()))
  | (.Atomic (_, _, _, .ShadowStack, .ShadowStack), _) => (pure (E_SAMO_Page_Fault ()))
  | (.Load .ShadowStack, .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.Load .ShadowStack, _) => (pure (E_SAMO_Page_Fault ()))
  | (.Store .ShadowStack, .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.Store .ShadowStack, _) => (pure (E_SAMO_Page_Fault ()))
  | (.InstructionFetch (), .PTW_No_Access ()) => (pure (E_Fetch_Access_Fault ()))
  | (.InstructionFetch (), _) => (pure (E_Fetch_Page_Fault ()))
  | (.CacheAccess (.CB_manage _), .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.CacheAccess (.CB_manage _), _) => (pure (E_SAMO_Page_Fault ()))
  | (.CacheAccess (.CB_zero ()), .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.CacheAccess (.CB_zero ()), _) => (pure (E_SAMO_Page_Fault ()))
  | (.CacheAccess (.CB_prefetch p), .PTW_No_Access ()) =>
    (match p with
    | .PREFETCH_R => (pure (E_Load_Access_Fault ()))
    | .PREFETCH_W => (pure (E_SAMO_Access_Fault ()))
    | .PREFETCH_I => (pure (E_Fetch_Access_Fault ())))
  | (.CacheAccess (.CB_prefetch p), _) =>
    (match p with
    | .PREFETCH_R => (pure (E_Load_Page_Fault ()))
    | .PREFETCH_W => (pure (E_SAMO_Page_Fault ()))
    | .PREFETCH_I => (pure (E_Fetch_Page_Fault ())))
  | (.LoadExecute p, _) =>
    (internal_error "sys/vmem_ptw.sail" 137
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadExecute.")))
  | (.LoadReserved (_, _, p), _) =>
    (internal_error "sys/vmem_ptw.sail" 138
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadReserved.")))
  | (.StoreConditional (_, _, p), _) =>
    (internal_error "sys/vmem_ptw.sail" 139
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for StoreConditional.")))
  | (.Atomic (_, _, _, rp, wp), _) =>
    (internal_error "sys/vmem_ptw.sail" 140
      (HAppend.hAppend "Invalid payloads ("
        (HAppend.hAppend (mem_payload_name_forwards rp)
          (HAppend.hAppend ", " (HAppend.hAppend (mem_payload_name_forwards wp) ") for Atomic.")))))

