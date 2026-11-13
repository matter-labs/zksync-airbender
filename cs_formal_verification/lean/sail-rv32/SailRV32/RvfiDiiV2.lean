import SailRV32.Prelude
import SailRV32.RvfiDii
import SailRV32.RvfiDiiV1

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

def undefined_RVFI_DII_Execution_PacketV2 (_ : Unit) : SailM (BitVec 512) := do
  (undefined_bitvector 512)

def Mk_RVFI_DII_Execution_PacketV2 (v : (BitVec 512)) : (BitVec 512) :=
  v

def _get_RVFI_DII_Execution_PacketV2_basic_data (v : (BitVec 512)) : (BitVec 192) :=
  (Sail.BitVec.extractLsb v 319 128)

def _update_RVFI_DII_Execution_PacketV2_basic_data (v : (BitVec 512)) (x : (BitVec 192)) : (BitVec 512) :=
  (Sail.BitVec.updateSubrange v 319 128 x)

def _set_RVFI_DII_Execution_PacketV2_basic_data (r_ref : (RegisterRef (BitVec 512))) (v : (BitVec 192)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_PacketV2_basic_data r v)

def _get_RVFI_DII_Execution_PacketV2_cheri_data_available (v : (BitVec 512)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 452 452)

def _update_RVFI_DII_Execution_PacketV2_cheri_data_available (v : (BitVec 512)) (x : (BitVec 1)) : (BitVec 512) :=
  (Sail.BitVec.updateSubrange v 452 452 x)

def _set_RVFI_DII_Execution_PacketV2_cheri_data_available (r_ref : (RegisterRef (BitVec 512))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_PacketV2_cheri_data_available r v)

def _get_RVFI_DII_Execution_PacketV2_cheri_scr_read_write_data_available (v : (BitVec 512)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 453 453)

def _update_RVFI_DII_Execution_PacketV2_cheri_scr_read_write_data_available (v : (BitVec 512)) (x : (BitVec 1)) : (BitVec 512) :=
  (Sail.BitVec.updateSubrange v 453 453 x)

def _set_RVFI_DII_Execution_PacketV2_cheri_scr_read_write_data_available (r_ref : (RegisterRef (BitVec 512))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_PacketV2_cheri_scr_read_write_data_available r v)

def _get_RVFI_DII_Execution_PacketV2_csr_read_write_data_available (v : (BitVec 512)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 451 451)

def _update_RVFI_DII_Execution_PacketV2_csr_read_write_data_available (v : (BitVec 512)) (x : (BitVec 1)) : (BitVec 512) :=
  (Sail.BitVec.updateSubrange v 451 451 x)

def _set_RVFI_DII_Execution_PacketV2_csr_read_write_data_available (r_ref : (RegisterRef (BitVec 512))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_PacketV2_csr_read_write_data_available r v)

def _get_RVFI_DII_Execution_PacketV2_floating_point_data_available (v : (BitVec 512)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 450 450)

def _update_RVFI_DII_Execution_PacketV2_floating_point_data_available (v : (BitVec 512)) (x : (BitVec 1)) : (BitVec 512) :=
  (Sail.BitVec.updateSubrange v 450 450 x)

def _set_RVFI_DII_Execution_PacketV2_floating_point_data_available (r_ref : (RegisterRef (BitVec 512))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_PacketV2_floating_point_data_available r v)

def _get_RVFI_DII_Execution_PacketV2_integer_data_available (v : (BitVec 512)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 448 448)

def _update_RVFI_DII_Execution_PacketV2_integer_data_available (v : (BitVec 512)) (x : (BitVec 1)) : (BitVec 512) :=
  (Sail.BitVec.updateSubrange v 448 448 x)

def _set_RVFI_DII_Execution_PacketV2_integer_data_available (r_ref : (RegisterRef (BitVec 512))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_PacketV2_integer_data_available r v)

def _get_RVFI_DII_Execution_PacketV2_memory_access_data_available (v : (BitVec 512)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 449 449)

def _update_RVFI_DII_Execution_PacketV2_memory_access_data_available (v : (BitVec 512)) (x : (BitVec 1)) : (BitVec 512) :=
  (Sail.BitVec.updateSubrange v 449 449 x)

def _set_RVFI_DII_Execution_PacketV2_memory_access_data_available (r_ref : (RegisterRef (BitVec 512))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_PacketV2_memory_access_data_available r v)

def _get_RVFI_DII_Execution_PacketV2_pc_data (v : (BitVec 512)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v 447 320)

def _update_RVFI_DII_Execution_PacketV2_pc_data (v : (BitVec 512)) (x : (BitVec 128)) : (BitVec 512) :=
  (Sail.BitVec.updateSubrange v 447 320 x)

def _set_RVFI_DII_Execution_PacketV2_pc_data (r_ref : (RegisterRef (BitVec 512))) (v : (BitVec 128)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_PacketV2_pc_data r v)

def _get_RVFI_DII_Execution_PacketV2_trace_size (v : (BitVec 512)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 127 64)

def _update_RVFI_DII_Execution_PacketV2_trace_size (v : (BitVec 512)) (x : (BitVec 64)) : (BitVec 512) :=
  (Sail.BitVec.updateSubrange v 127 64 x)

def _set_RVFI_DII_Execution_PacketV2_trace_size (r_ref : (RegisterRef (BitVec 512))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_PacketV2_trace_size r v)

def _get_RVFI_DII_Execution_PacketV2_trap_data_available (v : (BitVec 512)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 454 454)

def _update_RVFI_DII_Execution_PacketV2_trap_data_available (v : (BitVec 512)) (x : (BitVec 1)) : (BitVec 512) :=
  (Sail.BitVec.updateSubrange v 454 454 x)

def _set_RVFI_DII_Execution_PacketV2_trap_data_available (r_ref : (RegisterRef (BitVec 512))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_PacketV2_trap_data_available r v)

def _get_RVFI_DII_Execution_PacketV2_unused_data_available_fields (v : (BitVec 512)) : (BitVec 57) :=
  (Sail.BitVec.extractLsb v 511 455)

def _update_RVFI_DII_Execution_PacketV2_unused_data_available_fields (v : (BitVec 512)) (x : (BitVec 57)) : (BitVec 512) :=
  (Sail.BitVec.updateSubrange v 511 455 x)

def _set_RVFI_DII_Execution_PacketV2_unused_data_available_fields (r_ref : (RegisterRef (BitVec 512))) (v : (BitVec 57)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_PacketV2_unused_data_available_fields r v)

def rvfi_get_v2_support_packet (_ : Unit) : (BitVec 704) :=
  let rvfi_exec := (Mk_RVFI_DII_Execution_Packet_V1 (zeros (n := 704)))
  (_update_RVFI_DII_Execution_Packet_V1_rvfi_halt rvfi_exec 0x03#8)

def rvfi_get_v2_trace_size (_ : Unit) : SailM (BitVec 64) := do
  let trace_size : (BitVec 64) := (to_bits (l := 64) 512)
  let trace_size ← do
    if ((← readReg rvfi_int_data_present) : Bool)
    then (pure (BitVec.addInt trace_size 320))
    else (pure trace_size)
  let trace_size ← do
    if ((← readReg rvfi_mem_data_present) : Bool)
    then (pure (BitVec.addInt trace_size 704))
    else (pure trace_size)
  (pure (trace_size >>> 3))

def rvfi_get_exec_packet_v2 (_ : Unit) : SailM (BitVec 512) := do
  let packet := (Mk_RVFI_DII_Execution_PacketV2 (zeros (n := 512)))
  let packet := (_update_RVFI_DII_Execution_PacketV2_magic packet 0x32762D6563617274#64)
  let packet ← do
    (pure (_update_RVFI_DII_Execution_PacketV2_basic_data packet (← readReg rvfi_inst_data)))
  let packet ← do
    (pure (_update_RVFI_DII_Execution_PacketV2_pc_data packet (← readReg rvfi_pc_data)))
  let packet ← do
    (pure (_update_RVFI_DII_Execution_PacketV2_integer_data_available packet
        (bool_to_bit (← readReg rvfi_int_data_present))))
  let packet ← do
    (pure (_update_RVFI_DII_Execution_PacketV2_memory_access_data_available packet
        (bool_to_bit (← readReg rvfi_mem_data_present))))
  (pure (_update_RVFI_DII_Execution_PacketV2_trace_size packet (← (rvfi_get_v2_trace_size ()))))

