import SailRV32.Prelude
import SailRV32.Errors

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option backward.do.legacy true
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

def undefined_RVFI_DII_Instruction_Packet (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_RVFI_DII_Instruction_Packet (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_RVFI_DII_Instruction_Packet_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _update_RVFI_DII_Instruction_Packet_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CountSmcntrpmf_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Counteren_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Counterin_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_External_Trigger_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Fcsr_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HEnvcfg_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Hgatp32_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Hgatp64_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HpmEvent_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Hstateen0_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Hstateen1_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Hstateen2_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Hstateen3_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Hstatus_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICount_bits_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_IETrigger_bits_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_MContext_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_MControl6_bits_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_MEnvcfg_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Mcause_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Medeleg_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Minterrupts_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Misa_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Mstateen0_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Mstateen1_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Mstateen2_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Mstateen3_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Mstatus_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Mtvec_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PTE_Ext_bits (v : (BitVec 10)) (x : (BitVec 10)) : (BitVec 10) :=
  (Sail.BitVec.updateSubrange v (10 -i 1) 0 x)

def _update_PTE_Flags_bits (v : (BitVec 8)) (x : (BitVec 8)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v (8 -i 1) 0 x)

def _update_Pmpcfg_ent_bits (v : (BitVec 8)) (x : (BitVec 8)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v (8 -i 1) 0 x)

def _update_RVFI_DII_Execution_PacketV2_bits (v : (BitVec 512)) (x : (BitVec 512)) : (BitVec 512) :=
  (Sail.BitVec.updateSubrange v (512 -i 1) 0 x)

def _update_RVFI_DII_Execution_Packet_Ext_Integer_bits (v : (BitVec 320)) (x : (BitVec 320)) : (BitVec 320) :=
  (Sail.BitVec.updateSubrange v (320 -i 1) 0 x)

def _update_RVFI_DII_Execution_Packet_Ext_MemAccess_bits (v : (BitVec 704)) (x : (BitVec 704)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v (704 -i 1) 0 x)

def _update_RVFI_DII_Execution_Packet_InstMetaData_bits (v : (BitVec 192)) (x : (BitVec 192)) : (BitVec 192) :=
  (Sail.BitVec.updateSubrange v (192 -i 1) 0 x)

def _update_RVFI_DII_Execution_Packet_PC_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (128 -i 1) 0 x)

def _update_RVFI_DII_Execution_Packet_V1_bits (v : (BitVec 704)) (x : (BitVec 704)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v (704 -i 1) 0 x)

def _update_SContext_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_SEnvcfg_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Satp32_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Satp64_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Seccfg_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Sinterrupts_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Srmcfg_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Sstateen0_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Sstateen1_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Sstateen2_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Sstateen3_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Sstatus_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TControl_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_TData1_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_TDisabled_bits_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_TInfo_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Trigger_Extra_RV32_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Trigger_Extra_RV64_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Vcsr_bits (v : (BitVec 3)) (x : (BitVec 3)) : (BitVec 3) :=
  (Sail.BitVec.updateSubrange v (3 -i 1) 0 x)

def _update_Vtype_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_htif_cmd_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _set_RVFI_DII_Instruction_Packet_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Instruction_Packet_bits r v)

def _get_CountSmcntrpmf_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Counteren_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Counterin_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_External_Trigger_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Fcsr_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HEnvcfg_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Hgatp32_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Hgatp64_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HpmEvent_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Hstateen0_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Hstateen1_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Hstateen2_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Hstateen3_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Hstatus_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICount_bits_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_IETrigger_bits_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_MContext_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_MControl6_bits_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_MEnvcfg_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Mcause_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Medeleg_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Minterrupts_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Misa_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Mstateen0_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Mstateen1_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Mstateen2_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Mstateen3_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Mstatus_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Mtvec_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PTE_Ext_bits (v : (BitVec 10)) : (BitVec 10) :=
  (Sail.BitVec.extractLsb v (10 -i 1) 0)

def _get_PTE_Flags_bits (v : (BitVec 8)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v (8 -i 1) 0)

def _get_Pmpcfg_ent_bits (v : (BitVec 8)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v (8 -i 1) 0)

def _get_RVFI_DII_Execution_PacketV2_bits (v : (BitVec 512)) : (BitVec 512) :=
  (Sail.BitVec.extractLsb v (512 -i 1) 0)

def _get_RVFI_DII_Execution_Packet_Ext_Integer_bits (v : (BitVec 320)) : (BitVec 320) :=
  (Sail.BitVec.extractLsb v (320 -i 1) 0)

def _get_RVFI_DII_Execution_Packet_Ext_MemAccess_bits (v : (BitVec 704)) : (BitVec 704) :=
  (Sail.BitVec.extractLsb v (704 -i 1) 0)

def _get_RVFI_DII_Execution_Packet_InstMetaData_bits (v : (BitVec 192)) : (BitVec 192) :=
  (Sail.BitVec.extractLsb v (192 -i 1) 0)

def _get_RVFI_DII_Execution_Packet_PC_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (128 -i 1) 0)

def _get_RVFI_DII_Execution_Packet_V1_bits (v : (BitVec 704)) : (BitVec 704) :=
  (Sail.BitVec.extractLsb v (704 -i 1) 0)

def _get_SContext_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_SEnvcfg_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Satp32_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Satp64_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Seccfg_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Sinterrupts_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Srmcfg_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Sstateen0_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Sstateen1_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Sstateen2_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Sstateen3_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Sstatus_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_TControl_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_TData1_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_TDisabled_bits_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_TInfo_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Trigger_Extra_RV32_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Trigger_Extra_RV64_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Vcsr_bits (v : (BitVec 3)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v (3 -i 1) 0)

def _get_Vtype_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_htif_cmd_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _set_CountSmcntrpmf_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CountSmcntrpmf_bits r v)

def _set_Counteren_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counteren_bits r v)

def _set_Counterin_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counterin_bits r v)

def _set_External_Trigger_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_External_Trigger_bits r v)

def _set_Fcsr_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Fcsr_bits r v)

def _set_HEnvcfg_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HEnvcfg_bits r v)

def _set_Hgatp32_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hgatp32_bits r v)

def _set_Hgatp64_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hgatp64_bits r v)

def _set_HpmEvent_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HpmEvent_bits r v)

def _set_Hstateen0_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen0_bits r v)

def _set_Hstateen1_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen1_bits r v)

def _set_Hstateen2_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen2_bits r v)

def _set_Hstateen3_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen3_bits r v)

def _set_Hstatus_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstatus_bits r v)

def _set_ICount_bits_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICount_bits_bits r v)

def _set_IETrigger_bits_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IETrigger_bits_bits r v)

def _set_MContext_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MContext_bits r v)

def _set_MControl6_bits_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MControl6_bits_bits r v)

def _set_MEnvcfg_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_bits r v)

def _set_Mcause_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mcause_bits r v)

def _set_Medeleg_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_bits r v)

def _set_Minterrupts_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_bits r v)

def _set_Misa_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_bits r v)

def _set_Mstateen0_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen0_bits r v)

def _set_Mstateen1_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen1_bits r v)

def _set_Mstateen2_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen2_bits r v)

def _set_Mstateen3_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen3_bits r v)

def _set_Mstatus_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_bits r v)

def _set_Mtvec_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mtvec_bits r v)

def _set_PTE_Ext_bits (r_ref : (RegisterRef (BitVec 10))) (v : (BitVec 10)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Ext_bits r v)

def _set_PTE_Flags_bits (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_bits r v)

def _set_Pmpcfg_ent_bits (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_bits r v)

def _set_RVFI_DII_Execution_PacketV2_bits (r_ref : (RegisterRef (BitVec 512))) (v : (BitVec 512)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_PacketV2_bits r v)

def _set_RVFI_DII_Execution_Packet_Ext_Integer_bits (r_ref : (RegisterRef (BitVec 320))) (v : (BitVec 320)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_Integer_bits r v)

def _set_RVFI_DII_Execution_Packet_Ext_MemAccess_bits (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 704)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_MemAccess_bits r v)

def _set_RVFI_DII_Execution_Packet_InstMetaData_bits (r_ref : (RegisterRef (BitVec 192))) (v : (BitVec 192)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_InstMetaData_bits r v)

def _set_RVFI_DII_Execution_Packet_PC_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_PC_bits r v)

def _set_RVFI_DII_Execution_Packet_V1_bits (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 704)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_bits r v)

def _set_SContext_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SContext_bits r v)

def _set_SEnvcfg_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_bits r v)

def _set_Satp32_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp32_bits r v)

def _set_Satp64_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp64_bits r v)

def _set_Seccfg_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Seccfg_bits r v)

def _set_Sinterrupts_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sinterrupts_bits r v)

def _set_Srmcfg_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Srmcfg_bits r v)

def _set_Sstateen0_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstateen0_bits r v)

def _set_Sstateen1_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstateen1_bits r v)

def _set_Sstateen2_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstateen2_bits r v)

def _set_Sstateen3_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstateen3_bits r v)

def _set_Sstatus_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_bits r v)

def _set_TControl_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TControl_bits r v)

def _set_TData1_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TData1_bits r v)

def _set_TDisabled_bits_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TDisabled_bits_bits r v)

def _set_TInfo_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TInfo_bits r v)

def _set_Trigger_Extra_RV32_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Trigger_Extra_RV32_bits r v)

def _set_Trigger_Extra_RV64_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Trigger_Extra_RV64_bits r v)

def _set_Vcsr_bits (r_ref : (RegisterRef (BitVec 3))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vcsr_bits r v)

def _set_Vtype_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vtype_bits r v)

def _set_htif_cmd_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_htif_cmd_bits r v)

def _get_RVFI_DII_Instruction_Packet_padding (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _update_RVFI_DII_Instruction_Packet_padding (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def _update_RVFI_DII_Execution_Packet_Ext_Integer_padding (v : (BitVec 320)) (x : (BitVec 40)) : (BitVec 320) :=
  (Sail.BitVec.updateSubrange v 319 280 x)

def _update_RVFI_DII_Execution_Packet_InstMetaData_padding (v : (BitVec 192)) (x : (BitVec 16)) : (BitVec 192) :=
  (Sail.BitVec.updateSubrange v 191 176 x)

def _set_RVFI_DII_Instruction_Packet_padding (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Instruction_Packet_padding r v)

def _get_RVFI_DII_Execution_Packet_Ext_Integer_padding (v : (BitVec 320)) : (BitVec 40) :=
  (Sail.BitVec.extractLsb v 319 280)

def _get_RVFI_DII_Execution_Packet_InstMetaData_padding (v : (BitVec 192)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 191 176)

def _set_RVFI_DII_Execution_Packet_Ext_Integer_padding (r_ref : (RegisterRef (BitVec 320))) (v : (BitVec 40)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_Integer_padding r v)

def _set_RVFI_DII_Execution_Packet_InstMetaData_padding (r_ref : (RegisterRef (BitVec 192))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_InstMetaData_padding r v)

def _get_RVFI_DII_Instruction_Packet_rvfi_cmd (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _update_RVFI_DII_Instruction_Packet_rvfi_cmd (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _set_RVFI_DII_Instruction_Packet_rvfi_cmd (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Instruction_Packet_rvfi_cmd r v)

def _get_RVFI_DII_Instruction_Packet_rvfi_insn (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_RVFI_DII_Instruction_Packet_rvfi_insn (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_insn (v : (BitVec 192)) (x : (BitVec 64)) : (BitVec 192) :=
  (Sail.BitVec.updateSubrange v 127 64 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_insn (v : (BitVec 704)) (x : (BitVec 64)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 255 192 x)

def _set_RVFI_DII_Instruction_Packet_rvfi_insn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Instruction_Packet_rvfi_insn r v)

def _get_RVFI_DII_Execution_Packet_InstMetaData_rvfi_insn (v : (BitVec 192)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 127 64)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_insn (v : (BitVec 704)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 255 192)

def _set_RVFI_DII_Execution_Packet_InstMetaData_rvfi_insn (r_ref : (RegisterRef (BitVec 192))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_insn r v)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_insn (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_insn r v)

def _get_RVFI_DII_Instruction_Packet_rvfi_time (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)

def _update_RVFI_DII_Instruction_Packet_rvfi_time (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)

def _set_RVFI_DII_Instruction_Packet_rvfi_time (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Instruction_Packet_rvfi_time r v)

def rvfi_set_instr_packet (p : (BitVec 64)) : SailM Unit := do
  writeReg rvfi_instruction (Mk_RVFI_DII_Instruction_Packet p)

def rvfi_get_cmd (_ : Unit) : SailM (BitVec 8) := do
  (pure (_get_RVFI_DII_Instruction_Packet_rvfi_cmd (← readReg rvfi_instruction)))

def rvfi_get_insn (_ : Unit) : SailM (BitVec 32) := do
  (pure (_get_RVFI_DII_Instruction_Packet_rvfi_insn (← readReg rvfi_instruction)))

def print_instr_packet (bs : (BitVec 64)) : Unit :=
  let p := (Mk_RVFI_DII_Instruction_Packet bs)
  let _ : Unit := (print_bits "command " (_get_RVFI_DII_Instruction_Packet_rvfi_cmd p))
  (print_bits "instruction " (_get_RVFI_DII_Instruction_Packet_rvfi_insn p))

def undefined_RVFI_DII_Execution_Packet_InstMetaData (_ : Unit) : SailM (BitVec 192) := do
  (undefined_bitvector 192)

def Mk_RVFI_DII_Execution_Packet_InstMetaData (v : (BitVec 192)) : (BitVec 192) :=
  v

def _get_RVFI_DII_Execution_Packet_InstMetaData_rvfi_halt (v : (BitVec 192)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 143 136)

def _update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_halt (v : (BitVec 192)) (x : (BitVec 8)) : (BitVec 192) :=
  (Sail.BitVec.updateSubrange v 143 136 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_halt (v : (BitVec 704)) (x : (BitVec 8)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 695 688 x)

def _set_RVFI_DII_Execution_Packet_InstMetaData_rvfi_halt (r_ref : (RegisterRef (BitVec 192))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_halt r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_halt (v : (BitVec 704)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 695 688)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_halt (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_halt r v)

def _get_RVFI_DII_Execution_Packet_InstMetaData_rvfi_intr (v : (BitVec 192)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 151 144)

def _update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_intr (v : (BitVec 192)) (x : (BitVec 8)) : (BitVec 192) :=
  (Sail.BitVec.updateSubrange v 151 144 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_intr (v : (BitVec 704)) (x : (BitVec 8)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 703 696 x)

def _set_RVFI_DII_Execution_Packet_InstMetaData_rvfi_intr (r_ref : (RegisterRef (BitVec 192))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_intr r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_intr (v : (BitVec 704)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 703 696)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_intr (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_intr r v)

def _get_RVFI_DII_Execution_Packet_InstMetaData_rvfi_ixl (v : (BitVec 192)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 167 160)

def _update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_ixl (v : (BitVec 192)) (x : (BitVec 8)) : (BitVec 192) :=
  (Sail.BitVec.updateSubrange v 167 160 x)

def _set_RVFI_DII_Execution_Packet_InstMetaData_rvfi_ixl (r_ref : (RegisterRef (BitVec 192))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_ixl r v)

def _get_RVFI_DII_Execution_Packet_InstMetaData_rvfi_mode (v : (BitVec 192)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 159 152)

def _update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_mode (v : (BitVec 192)) (x : (BitVec 8)) : (BitVec 192) :=
  (Sail.BitVec.updateSubrange v 159 152 x)

def _set_RVFI_DII_Execution_Packet_InstMetaData_rvfi_mode (r_ref : (RegisterRef (BitVec 192))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_mode r v)

def _get_RVFI_DII_Execution_Packet_InstMetaData_rvfi_order (v : (BitVec 192)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_order (v : (BitVec 192)) (x : (BitVec 64)) : (BitVec 192) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_order (v : (BitVec 704)) (x : (BitVec 64)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _set_RVFI_DII_Execution_Packet_InstMetaData_rvfi_order (r_ref : (RegisterRef (BitVec 192))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_order r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_order (v : (BitVec 704)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_order (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_order r v)

def _get_RVFI_DII_Execution_Packet_InstMetaData_rvfi_trap (v : (BitVec 192)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 135 128)

def _update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_trap (v : (BitVec 192)) (x : (BitVec 8)) : (BitVec 192) :=
  (Sail.BitVec.updateSubrange v 135 128 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_trap (v : (BitVec 704)) (x : (BitVec 8)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 687 680 x)

def _set_RVFI_DII_Execution_Packet_InstMetaData_rvfi_trap (r_ref : (RegisterRef (BitVec 192))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_trap r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_trap (v : (BitVec 704)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 687 680)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_trap (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_trap r v)

def _get_RVFI_DII_Execution_Packet_InstMetaData_rvfi_valid (v : (BitVec 192)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 175 168)

def _update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_valid (v : (BitVec 192)) (x : (BitVec 8)) : (BitVec 192) :=
  (Sail.BitVec.updateSubrange v 175 168 x)

def _set_RVFI_DII_Execution_Packet_InstMetaData_rvfi_valid (r_ref : (RegisterRef (BitVec 192))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_InstMetaData_rvfi_valid r v)

def undefined_RVFI_DII_Execution_Packet_PC (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector 128)

def Mk_RVFI_DII_Execution_Packet_PC (v : (BitVec 128)) : (BitVec 128) :=
  v

def _get_RVFI_DII_Execution_Packet_PC_rvfi_pc_rdata (v : (BitVec 128)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _update_RVFI_DII_Execution_Packet_PC_rvfi_pc_rdata (v : (BitVec 128)) (x : (BitVec 64)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_pc_rdata (v : (BitVec 704)) (x : (BitVec 64)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 127 64 x)

def _set_RVFI_DII_Execution_Packet_PC_rvfi_pc_rdata (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_PC_rvfi_pc_rdata r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_pc_rdata (v : (BitVec 704)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 127 64)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_pc_rdata (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_pc_rdata r v)

def _get_RVFI_DII_Execution_Packet_PC_rvfi_pc_wdata (v : (BitVec 128)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 127 64)

def _update_RVFI_DII_Execution_Packet_PC_rvfi_pc_wdata (v : (BitVec 128)) (x : (BitVec 64)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 127 64 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_pc_wdata (v : (BitVec 704)) (x : (BitVec 64)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 191 128 x)

def _set_RVFI_DII_Execution_Packet_PC_rvfi_pc_wdata (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_PC_rvfi_pc_wdata r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_pc_wdata (v : (BitVec 704)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 191 128)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_pc_wdata (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_pc_wdata r v)

def undefined_RVFI_DII_Execution_Packet_Ext_Integer (_ : Unit) : SailM (BitVec 320) := do
  (undefined_bitvector 320)

def Mk_RVFI_DII_Execution_Packet_Ext_Integer (v : (BitVec 320)) : (BitVec 320) :=
  v

def _get_RVFI_DII_Execution_Packet_Ext_Integer_magic (v : (BitVec 320)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _update_RVFI_DII_Execution_Packet_Ext_Integer_magic (v : (BitVec 320)) (x : (BitVec 64)) : (BitVec 320) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_RVFI_DII_Execution_PacketV2_magic (v : (BitVec 512)) (x : (BitVec 64)) : (BitVec 512) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_RVFI_DII_Execution_Packet_Ext_MemAccess_magic (v : (BitVec 704)) (x : (BitVec 64)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _set_RVFI_DII_Execution_Packet_Ext_Integer_magic (r_ref : (RegisterRef (BitVec 320))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_Integer_magic r v)

def _get_RVFI_DII_Execution_PacketV2_magic (v : (BitVec 512)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_RVFI_DII_Execution_Packet_Ext_MemAccess_magic (v : (BitVec 704)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _set_RVFI_DII_Execution_PacketV2_magic (r_ref : (RegisterRef (BitVec 512))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_PacketV2_magic r v)

def _set_RVFI_DII_Execution_Packet_Ext_MemAccess_magic (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_MemAccess_magic r v)

def _get_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rd_addr (v : (BitVec 320)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 263 256)

def _update_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rd_addr (v : (BitVec 320)) (x : (BitVec 8)) : (BitVec 320) :=
  (Sail.BitVec.updateSubrange v 263 256 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_rd_addr (v : (BitVec 704)) (x : (BitVec 8)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 679 672 x)

def _set_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rd_addr (r_ref : (RegisterRef (BitVec 320))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rd_addr r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_rd_addr (v : (BitVec 704)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 679 672)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_rd_addr (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_rd_addr r v)

def _get_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rd_wdata (v : (BitVec 320)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 127 64)

def _update_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rd_wdata (v : (BitVec 320)) (x : (BitVec 64)) : (BitVec 320) :=
  (Sail.BitVec.updateSubrange v 127 64 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_rd_wdata (v : (BitVec 704)) (x : (BitVec 64)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 447 384 x)

def _set_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rd_wdata (r_ref : (RegisterRef (BitVec 320))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rd_wdata r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_rd_wdata (v : (BitVec 704)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 447 384)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_rd_wdata (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_rd_wdata r v)

def _get_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs1_addr (v : (BitVec 320)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 271 264)

def _update_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs1_addr (v : (BitVec 320)) (x : (BitVec 8)) : (BitVec 320) :=
  (Sail.BitVec.updateSubrange v 271 264 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_rs1_addr (v : (BitVec 704)) (x : (BitVec 8)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 663 656 x)

def _set_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs1_addr (r_ref : (RegisterRef (BitVec 320))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs1_addr r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_rs1_addr (v : (BitVec 704)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 663 656)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_rs1_addr (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_rs1_addr r v)

def _get_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs1_rdata (v : (BitVec 320)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 191 128)

def _update_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs1_rdata (v : (BitVec 320)) (x : (BitVec 64)) : (BitVec 320) :=
  (Sail.BitVec.updateSubrange v 191 128 x)

def _set_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs1_rdata (r_ref : (RegisterRef (BitVec 320))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs1_rdata r v)

def _get_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs2_addr (v : (BitVec 320)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 279 272)

def _update_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs2_addr (v : (BitVec 320)) (x : (BitVec 8)) : (BitVec 320) :=
  (Sail.BitVec.updateSubrange v 279 272 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_rs2_addr (v : (BitVec 704)) (x : (BitVec 8)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 671 664 x)

def _set_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs2_addr (r_ref : (RegisterRef (BitVec 320))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs2_addr r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_rs2_addr (v : (BitVec 704)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 671 664)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_rs2_addr (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_rs2_addr r v)

def _get_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs2_rdata (v : (BitVec 320)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 255 192)

def _update_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs2_rdata (v : (BitVec 320)) (x : (BitVec 64)) : (BitVec 320) :=
  (Sail.BitVec.updateSubrange v 255 192 x)

def _set_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs2_rdata (r_ref : (RegisterRef (BitVec 320))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs2_rdata r v)

def undefined_RVFI_DII_Execution_Packet_Ext_MemAccess (_ : Unit) : SailM (BitVec 704) := do
  (undefined_bitvector 704)

def Mk_RVFI_DII_Execution_Packet_Ext_MemAccess (v : (BitVec 704)) : (BitVec 704) :=
  v

def _get_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_addr (v : (BitVec 704)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 703 640)

def _update_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_addr (v : (BitVec 704)) (x : (BitVec 64)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 703 640 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_mem_addr (v : (BitVec 704)) (x : (BitVec 64)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 511 448 x)

def _set_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_addr (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_addr r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_mem_addr (v : (BitVec 704)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 511 448)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_mem_addr (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_mem_addr r v)

def _get_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_rdata (v : (BitVec 704)) : (BitVec 256) :=
  (Sail.BitVec.extractLsb v 319 64)

def _update_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_rdata (v : (BitVec 704)) (x : (BitVec 256)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 319 64 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_mem_rdata (v : (BitVec 704)) (x : (BitVec 64)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 575 512 x)

def _set_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_rdata (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 256)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_rdata r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_mem_rdata (v : (BitVec 704)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 575 512)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_mem_rdata (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_mem_rdata r v)

def _get_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_rmask (v : (BitVec 704)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 607 576)

def _update_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_rmask (v : (BitVec 704)) (x : (BitVec 32)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 607 576 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_mem_rmask (v : (BitVec 704)) (x : (BitVec 8)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 647 640 x)

def _set_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_rmask (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_rmask r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_mem_rmask (v : (BitVec 704)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 647 640)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_mem_rmask (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_mem_rmask r v)

def _get_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_wdata (v : (BitVec 704)) : (BitVec 256) :=
  (Sail.BitVec.extractLsb v 575 320)

def _update_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_wdata (v : (BitVec 704)) (x : (BitVec 256)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 575 320 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_mem_wdata (v : (BitVec 704)) (x : (BitVec 64)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 639 576 x)

def _set_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_wdata (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 256)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_wdata r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_mem_wdata (v : (BitVec 704)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 639 576)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_mem_wdata (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_mem_wdata r v)

def _get_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_wmask (v : (BitVec 704)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 639 608)

def _update_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_wmask (v : (BitVec 704)) (x : (BitVec 32)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 639 608 x)

def _update_RVFI_DII_Execution_Packet_V1_rvfi_mem_wmask (v : (BitVec 704)) (x : (BitVec 8)) : (BitVec 704) :=
  (Sail.BitVec.updateSubrange v 655 648 x)

def _set_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_wmask (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_wmask r v)

def _get_RVFI_DII_Execution_Packet_V1_rvfi_mem_wmask (v : (BitVec 704)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 655 648)

def _set_RVFI_DII_Execution_Packet_V1_rvfi_mem_wmask (r_ref : (RegisterRef (BitVec 704))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVFI_DII_Execution_Packet_V1_rvfi_mem_wmask r v)

def rvfi_zero_exec_packet (_ : Unit) : SailM Unit := do
  writeReg rvfi_inst_data (Mk_RVFI_DII_Execution_Packet_InstMetaData (zeros (n := 192)))
  writeReg rvfi_pc_data (Mk_RVFI_DII_Execution_Packet_PC (zeros (n := 128)))
  writeReg rvfi_int_data (Mk_RVFI_DII_Execution_Packet_Ext_Integer (zeros (n := 320)))
  writeReg rvfi_int_data (_update_RVFI_DII_Execution_Packet_Ext_Integer_magic
    (← readReg rvfi_int_data) 0x617461642D746E69#64)
  writeReg rvfi_int_data_present false
  writeReg rvfi_mem_data (Mk_RVFI_DII_Execution_Packet_Ext_MemAccess (zeros (n := 704)))
  writeReg rvfi_mem_data (_update_RVFI_DII_Execution_Packet_Ext_MemAccess_magic
    (← readReg rvfi_mem_data) 0x617461642D6D656D#64)
  writeReg rvfi_mem_data_present false

def rvfi_halt_exec_packet (_ : Unit) : SailM Unit := do
  writeReg rvfi_inst_data (Sail.BitVec.updateSubrange (← readReg rvfi_inst_data) 143 136 0x01#8)

def rvfi_get_int_data (_ : Unit) : SailM (BitVec 320) := do
  «assert» (← readReg rvfi_int_data_present) "reading uninitialized data"
  readReg rvfi_int_data

def rvfi_get_mem_data (_ : Unit) : SailM (BitVec 704) := do
  «assert» (← readReg rvfi_mem_data_present) "reading uninitialized data"
  readReg rvfi_mem_data

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ 32 -/
def rvfi_encode_width_mask (width : Nat) : (BitVec 32) :=
  (0xFFFFFFFF#32 >>> (32 -i width))

def print_rvfi_exec (_ : Unit) : SailM Unit := do
  (pure (print_bits "rvfi_intr     : "
      (_get_RVFI_DII_Execution_Packet_InstMetaData_rvfi_intr (← readReg rvfi_inst_data))))
  (pure (print_bits "rvfi_halt     : "
      (_get_RVFI_DII_Execution_Packet_InstMetaData_rvfi_halt (← readReg rvfi_inst_data))))
  (pure (print_bits "rvfi_trap     : "
      (_get_RVFI_DII_Execution_Packet_InstMetaData_rvfi_trap (← readReg rvfi_inst_data))))
  (pure (print_bits "rvfi_rd_addr  : "
      (_get_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rd_addr (← readReg rvfi_int_data))))
  (pure (print_bits "rvfi_rs2_addr : "
      (_get_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs2_addr (← readReg rvfi_int_data))))
  (pure (print_bits "rvfi_rs1_addr : "
      (_get_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs1_addr (← readReg rvfi_int_data))))
  (pure (print_bits "rvfi_mem_wmask: "
      (_get_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_wmask (← readReg rvfi_mem_data))))
  (pure (print_bits "rvfi_mem_rmask: "
      (_get_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_rmask (← readReg rvfi_mem_data))))
  (pure (print_bits "rvfi_mem_wdata: "
      (_get_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_wdata (← readReg rvfi_mem_data))))
  (pure (print_bits "rvfi_mem_rdata: "
      (_get_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_rdata (← readReg rvfi_mem_data))))
  (pure (print_bits "rvfi_mem_addr : "
      (_get_RVFI_DII_Execution_Packet_Ext_MemAccess_rvfi_mem_addr (← readReg rvfi_mem_data))))
  (pure (print_bits "rvfi_rd_wdata : "
      (_get_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rd_wdata (← readReg rvfi_int_data))))
  (pure (print_bits "rvfi_rs2_data : "
      (_get_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs2_rdata (← readReg rvfi_int_data))))
  (pure (print_bits "rvfi_rs1_data : "
      (_get_RVFI_DII_Execution_Packet_Ext_Integer_rvfi_rs1_rdata (← readReg rvfi_int_data))))
  (pure (print_bits "rvfi_insn     : "
      (_get_RVFI_DII_Execution_Packet_InstMetaData_rvfi_insn (← readReg rvfi_inst_data))))
  (pure (print_bits "rvfi_pc_wdata : "
      (_get_RVFI_DII_Execution_Packet_PC_rvfi_pc_wdata (← readReg rvfi_pc_data))))
  (pure (print_bits "rvfi_pc_rdata : "
      (_get_RVFI_DII_Execution_Packet_PC_rvfi_pc_rdata (← readReg rvfi_pc_data))))
  (pure (print_bits "rvfi_order    : "
      (_get_RVFI_DII_Execution_Packet_InstMetaData_rvfi_order (← readReg rvfi_inst_data))))

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def rvfi_write (paddr : (BitVec 32)) (width : Nat) (value : (BitVec (8 * width))) : SailM Unit := do
  writeReg rvfi_mem_data (Sail.BitVec.updateSubrange (← readReg rvfi_mem_data) 703 640
    (zero_extend (m := 64) paddr))
  writeReg rvfi_mem_data_present true
  if ((width ≤b 16) : Bool)
  then
    (do
      writeReg rvfi_mem_data (Sail.BitVec.updateSubrange (← readReg rvfi_mem_data) 575 320
        (Sail.BitVec.zeroExtend value 256))
      writeReg rvfi_mem_data (Sail.BitVec.updateSubrange (← readReg rvfi_mem_data) 639 608
        (rvfi_encode_width_mask width)))
  else (internal_error "core/rvfi_dii.sail" 214 "Expected at most 16 bytes here!")

/-- Type quantifiers: width : Nat, width ≥ 0, width > 0 -/
def rvfi_read (paddr : (BitVec 32)) (width : Nat) (value : (BitVec (8 * width))) : SailM Unit := do
  writeReg rvfi_mem_data (Sail.BitVec.updateSubrange (← readReg rvfi_mem_data) 703 640
    (zero_extend (m := 64) paddr))
  writeReg rvfi_mem_data_present true
  if ((width ≤b 16) : Bool)
  then
    (do
      writeReg rvfi_mem_data (Sail.BitVec.updateSubrange (← readReg rvfi_mem_data) 319 64
        (Sail.BitVec.zeroExtend value 256))
      writeReg rvfi_mem_data (Sail.BitVec.updateSubrange (← readReg rvfi_mem_data) 607 576
        (rvfi_encode_width_mask width)))
  else (internal_error "core/rvfi_dii.sail" 227 "Expected at most 16 bytes here!")

def rvfi_mem_exception (paddr : (BitVec 32)) : SailM Unit := do
  writeReg rvfi_mem_data (Sail.BitVec.updateSubrange (← readReg rvfi_mem_data) 703 640
    (zero_extend (m := 64) paddr))
  writeReg rvfi_mem_data_present true

/-- Type quantifiers: r : Nat, 0 ≤ r ∧ r < 32 -/
def rvfi_wX (r : Nat) (v : (BitVec 32)) : SailM Unit := do
  writeReg rvfi_int_data (Sail.BitVec.updateSubrange (← readReg rvfi_int_data) 127 64
    (zero_extend (m := 64) v))
  writeReg rvfi_int_data (Sail.BitVec.updateSubrange (← readReg rvfi_int_data) 263 256
    (to_bits (l := 8) r))
  writeReg rvfi_int_data_present true

def rvfi_trap (_ : Unit) : SailM Unit := do
  writeReg rvfi_inst_data (Sail.BitVec.updateSubrange (← readReg rvfi_inst_data) 135 128 0x01#8)

