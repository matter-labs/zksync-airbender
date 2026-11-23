import SailRV32.SailRV32
import SailRV32.Flow
import SailRV32.Prelude
import SailRV32.Errors
import SailRV32.PmTypes
import SailRV32.IsaVersion
import SailRV32.Xlen
import SailRV32.MemAddrtype
import SailRV32.PlatformConfig
import SailRV32.Types

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

def undefined_Misa (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def _update_Misa_A (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PTE_Flags_A (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_Pmpcfg_ent_A (v : (BitVec 8)) (x : (BitVec 2)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 4 3 x)

def _set_Misa_A (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_A r v)

def _get_PTE_Flags_A (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_Pmpcfg_ent_A (v : (BitVec 8)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 4 3)

def _set_PTE_Flags_A (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_A r v)

def _set_Pmpcfg_ent_A (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_A r v)

def _update_Misa_B (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Misa_B (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_B r v)

def _update_Misa_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_Hstateen0_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_Mstateen0_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_Sstateen0_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Misa_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_C r v)

def _get_Hstateen0_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_Mstateen0_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_Sstateen0_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _set_Hstateen0_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstateen0_C r v)

def _set_Mstateen0_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstateen0_C r v)

def _set_Sstateen0_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstateen0_C r v)

def _update_Misa_D (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PTE_Flags_D (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Misa_D (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_D r v)

def _get_PTE_Flags_D (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _set_PTE_Flags_D (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_D r v)

def _get_Misa_E (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_Misa_E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _set_Misa_E (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_E r v)

def _update_Misa_F (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Misa_F (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_F r v)

def _get_Misa_G (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_Misa_G (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PTE_Flags_G (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Misa_G (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_G r v)

def _get_PTE_Flags_G (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _set_PTE_Flags_G (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_G r v)

def _update_Misa_H (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Misa_H (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_H r v)

def _update_Misa_I (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _set_Misa_I (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_I r v)

def _get_Misa_J (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_Misa_J (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _set_Misa_J (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_J r v)

def _get_Misa_K (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_Misa_K (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _set_Misa_K (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_K r v)

def _get_Misa_L (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_Misa_L (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_Pmpcfg_ent_L (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Misa_L (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_L r v)

def _get_Pmpcfg_ent_L (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _set_Pmpcfg_ent_L (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_L r v)

def _update_Misa_M (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _set_Misa_M (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_M r v)

def _get_Misa_MXL (v : (BitVec 32)) : (BitVec (32 - 1 - (32 - 2) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 1) (32 -i 2))

def _set_Misa_MXL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 1 - (32 - 2) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_MXL r v)

def _get_Misa_N (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_Misa_N (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PTE_Ext_N (v : (BitVec 10)) (x : (BitVec 1)) : (BitVec 10) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _set_Misa_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_N r v)

def _get_PTE_Ext_N (v : (BitVec 10)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _set_PTE_Ext_N (r_ref : (RegisterRef (BitVec 10))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Ext_N r v)

def _get_Misa_O (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_Misa_O (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _set_Misa_O (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_O r v)

def _get_Misa_P (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_Misa_P (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _set_Misa_P (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_P r v)

def _get_Misa_Q (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_Misa_Q (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _set_Misa_Q (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_Q r v)

def _get_Misa_R (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_Misa_R (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PTE_Flags_R (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_Pmpcfg_ent_R (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Misa_R (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_R r v)

def _get_PTE_Flags_R (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_Pmpcfg_ent_R (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _set_PTE_Flags_R (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_R r v)

def _set_Pmpcfg_ent_R (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_R r v)

def _update_Misa_S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _set_Misa_S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_S r v)

def _get_Misa_T (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_Misa_T (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _set_Misa_T (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_T r v)

def _update_Misa_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PTE_Flags_U (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _set_Misa_U (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_U r v)

def _get_PTE_Flags_U (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _set_PTE_Flags_U (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_U r v)

def _update_Misa_V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PTE_Flags_V (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Misa_V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_V r v)

def _get_PTE_Flags_V (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _set_PTE_Flags_V (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_V r v)

def _get_Misa_W (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_Misa_W (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PTE_Flags_W (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_Pmpcfg_ent_W (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Misa_W (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_W r v)

def _get_PTE_Flags_W (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_Pmpcfg_ent_W (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _set_PTE_Flags_W (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_W r v)

def _set_Pmpcfg_ent_W (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_W r v)

def _get_Misa_X (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_Misa_X (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PTE_Flags_X (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_Pmpcfg_ent_X (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _set_Misa_X (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_X r v)

def _get_PTE_Flags_X (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_Pmpcfg_ent_X (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _set_PTE_Flags_X (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_X r v)

def _set_Pmpcfg_ent_X (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_X r v)

def _get_Misa_Y (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_Misa_Y (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _set_Misa_Y (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_Y r v)

def _get_Misa_Z (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_Misa_Z (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _set_Misa_Z (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_Z r v)

def sys_hgatp_sv32x4_supported : Bool := true

def sys_hgatp_sv39x4_supported : Bool := false

def sys_hgatp_sv48x4_supported : Bool := false

def sys_hgatp_sv57x4_supported : Bool := false

def sys_vsatp_sv32_supported : Bool := true

def sys_vsatp_sv39_supported : Bool := false

def sys_vsatp_sv48_supported : Bool := false

def sys_vsatp_sv57_supported : Bool := false

def sys_misaligned_load_writes_tinst : Bool := true

def sys_load_access_fault_writes_tinst : Bool := true

def sys_load_page_fault_writes_tinst : Bool := true

def sys_load_guest_page_fault_writes_tinst : Bool := true

def sys_misaligned_samo_writes_tinst : Bool := true

def sys_samo_access_fault_writes_tinst : Bool := true

def sys_samo_page_fault_writes_tinst : Bool := true

def sys_samo_guest_page_fault_writes_tinst : Bool := true

def sys_guest_page_fault_writes_htval : Bool := true

def sys_writable_hpm_counters : (BitVec 32) := 0b11111111111111111111111111111111#32

def ext_veto_disable_C (_ : Unit) : Bool :=
  false

def legalize_misa (m : (BitVec 32)) (v : (BitVec 32)) : SailM (BitVec 32) := do
  let v := (Mk_Misa v)
  let A :=
    if ((hartSupports Ext_A) : Bool)
    then (_get_Misa_A v)
    else 0#1
  let B :=
    if ((hartSupports Ext_B) : Bool)
    then (_get_Misa_B v)
    else 0#1
  let C :=
    if ((hartSupports Ext_C) : Bool)
    then (_get_Misa_C v)
    else 0#1
  let M :=
    if ((hartSupports Ext_M) : Bool)
    then (_get_Misa_M v)
    else 0#1
  let F :=
    if ((hartSupports Ext_F) : Bool)
    then (_get_Misa_F v)
    else 0#1
  let D :=
    if (((hartSupports Ext_D) && (F == 1#1)) : Bool)
    then (_get_Misa_D v)
    else 0#1
  let V :=
    if (((hartSupports Ext_V) && ((F == 1#1) && (D == 1#1))) : Bool)
    then (_get_Misa_V v)
    else 0#1
  let U :=
    if ((hartSupports Ext_U) : Bool)
    then (_get_Misa_U v)
    else 0#1
  let S :=
    if (((hartSupports Ext_S) && (U == 1#1)) : Bool)
    then (_get_Misa_S v)
    else 0#1
  let H :=
    if (((hartSupports Ext_H) && ((S == 1#1) && (U == 1#1))) : Bool)
    then (_get_Misa_H v)
    else 0#1
  if (((C == 0#1) && (((_get_Misa_C m) == 1#1) && (((BitVec.access (← readReg nextPC) 1) == 1#1) || (ext_veto_disable_C
             ())))) : Bool)
  then (pure m)
  else
    (pure (_update_Misa_E
        (_update_Misa_I
          (_update_Misa_V
            (_update_Misa_U
              (_update_Misa_S
                (_update_Misa_M
                  (_update_Misa_H
                    (_update_Misa_F
                      (_update_Misa_D (_update_Misa_C (_update_Misa_B (_update_Misa_A m A) B) C) D)
                      F) H) M) S) U) V) (bool_to_bit (not base_E_enabled)))
        (bool_to_bit base_E_enabled)))

def lowest_supported_privLevel (_ : Unit) : SailM Privilege := do
  if ((← (currentlyEnabled Ext_U)) : Bool)
  then (pure User)
  else (pure Machine)

def have_nominal_privLevel (priv : (BitVec 2)) : SailM Bool := do
  match priv with
  | 0b00 => (currentlyEnabled Ext_U)
  | 0b01 => (currentlyEnabled Ext_S)
  | 0b10 => (pure false)
  | _ => (pure true)

def undefined_Mstatus (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _update_Mstatus_FS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 13 x)

def _update_Sstatus_FS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 13 x)

def _set_Mstatus_FS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_FS r v)

def _get_Sstatus_FS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 14 13)

def _set_Sstatus_FS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_FS r v)

def _get_Mstatus_GVA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)

def _update_Mstatus_GVA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _update_Hstatus_GVA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _set_Mstatus_GVA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_GVA r v)

def _get_Hstatus_GVA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _set_Hstatus_GVA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstatus_GVA r v)

def _get_Mstatus_MBE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _update_Mstatus_MBE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _set_Mstatus_MBE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MBE r v)

def _get_Mstatus_MDT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 42 42)

def _update_Mstatus_MDT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _set_Mstatus_MDT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MDT r v)

def _get_Mstatus_MIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_Mstatus_MIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _set_Mstatus_MIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MIE r v)

def _get_Mstatus_MPELP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)

def _update_Mstatus_MPELP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _set_Mstatus_MPELP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MPELP r v)

def _get_Mstatus_MPIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_Mstatus_MPIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Mstatus_MPIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MPIE r v)

def _get_Mstatus_MPP (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 12 11)

def _update_Mstatus_MPP (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 11 x)

def _set_Mstatus_MPP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MPP r v)

def _get_Mstatus_MPRV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_Mstatus_MPRV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _set_Mstatus_MPRV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MPRV r v)

def _get_Mstatus_MPV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)

def _update_Mstatus_MPV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)

def _set_Mstatus_MPV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MPV r v)

def _get_Mstatus_MXR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_Mstatus_MXR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_Sstatus_MXR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _set_Mstatus_MXR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MXR r v)

def _get_Sstatus_MXR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _set_Sstatus_MXR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_MXR r v)

def _get_Mstatus_SBE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _update_Mstatus_SBE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _set_Mstatus_SBE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SBE r v)

def _get_Mstatus_SD (v : (BitVec 64)) : (BitVec (32 - 1 - (32 - 1) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 1) (32 -i 1))

def _update_Mstatus_SD (v : (BitVec 64)) (x : (BitVec (32 - 1 - (32 - 1) + 1))) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) (32 -i 1) x)

def _update_Sstatus_SD (v : (BitVec 64)) (x : (BitVec (32 - 1 - (32 - 1) + 1))) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) (32 -i 1) x)

def _set_Mstatus_SD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec (32 - 1 - (32 - 1) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SD r v)

def _get_Sstatus_SD (v : (BitVec 64)) : (BitVec (32 - 1 - (32 - 1) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 1) (32 -i 1))

def _set_Sstatus_SD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec (32 - 1 - (32 - 1) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SD r v)

def _get_Mstatus_SDT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_Mstatus_SDT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_Sstatus_SDT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _set_Mstatus_SDT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SDT r v)

def _get_Sstatus_SDT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _set_Sstatus_SDT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SDT r v)

def _get_Mstatus_SIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Mstatus_SIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_Sstatus_SIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Mstatus_SIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SIE r v)

def _get_Sstatus_SIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _set_Sstatus_SIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SIE r v)

def _get_Mstatus_SPELP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_Mstatus_SPELP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_Sstatus_SPELP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _set_Mstatus_SPELP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SPELP r v)

def _get_Sstatus_SPELP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _set_Sstatus_SPELP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SPELP r v)

def _get_Mstatus_SPIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_Mstatus_SPIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_Sstatus_SPIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Mstatus_SPIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SPIE r v)

def _get_Sstatus_SPIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _set_Sstatus_SPIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SPIE r v)

def _get_Mstatus_SPP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_Mstatus_SPP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_Sstatus_SPP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _set_Mstatus_SPP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SPP r v)

def _get_Sstatus_SPP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _set_Sstatus_SPP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SPP r v)

def _get_Mstatus_SUM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_Mstatus_SUM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_Sstatus_SUM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _set_Mstatus_SUM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SUM r v)

def _get_Sstatus_SUM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _set_Sstatus_SUM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SUM r v)

def _get_Mstatus_SXL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 35 34)

def _set_Mstatus_SXL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SXL r v)

def _get_Mstatus_TSR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_Mstatus_TSR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _set_Mstatus_TSR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_TSR r v)

def _get_Mstatus_TVM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_Mstatus_TVM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _set_Mstatus_TVM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_TVM r v)

def _get_Mstatus_TW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_Mstatus_TW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _set_Mstatus_TW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_TW r v)

def _get_Mstatus_UXL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _update_Sstatus_UXL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _set_Mstatus_UXL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_UXL r v)

def _get_Sstatus_UXL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _set_Sstatus_UXL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_UXL r v)

def _update_Mstatus_VS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 9 x)

def _update_Sstatus_VS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 9 x)

def _set_Mstatus_VS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_VS r v)

def _get_Sstatus_VS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 10 9)

def _set_Sstatus_VS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_VS r v)

def _get_Mstatus_XS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 16 15)

def _update_Mstatus_XS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 15 x)

def _update_Sstatus_XS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 15 x)

def _set_Mstatus_XS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_XS r v)

def _get_Sstatus_XS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 16 15)

def _set_Sstatus_XS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_XS r v)

def legalize_mstatus (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_Mstatus v)
  let o ← do
    (pure (_update_Mstatus_SIE
        (_update_Mstatus_MIE
          (_update_Mstatus_SPIE
            (_update_Mstatus_MPIE
              (_update_Mstatus_SPP
                (_update_Mstatus_MPP
                  (_update_Mstatus_VS
                    (_update_Mstatus_FS
                      (_update_Mstatus_XS
                        (_update_Mstatus_MPRV
                          (_update_Mstatus_SUM
                            (_update_Mstatus_MXR
                              (_update_Mstatus_TVM
                                (_update_Mstatus_TW
                                  (_update_Mstatus_TSR
                                    (_update_Mstatus_SPELP
                                      (_update_Mstatus_SDT
                                        (_update_Mstatus_GVA
                                          (_update_Mstatus_MPV
                                            (_update_Mstatus_MPELP
                                              (_update_Mstatus_MDT o
                                                (← do
                                                  if ((← (currentlyEnabled Ext_Smdbltrp)) : Bool)
                                                  then (pure (_get_Mstatus_MDT v))
                                                  else (pure 0#1)))
                                              (if ((hartSupports Ext_Zicfilp) : Bool)
                                              then (_get_Mstatus_MPELP v)
                                              else 0#1))
                                            (← do
                                              if ((← (currentlyEnabled Ext_H)) : Bool)
                                              then (pure (_get_Mstatus_MPV v))
                                              else (pure 0#1)))
                                          (← do
                                            if ((← (currentlyEnabled Ext_H)) : Bool)
                                            then (pure (_get_Mstatus_GVA v))
                                            else (pure 0#1)))
                                        (← do
                                          if ((← (currentlyEnabled Ext_Ssdbltrp)) : Bool)
                                          then (pure (_get_Mstatus_SDT v))
                                          else (pure 0#1)))
                                      (← do
                                        if (((hartSupports Ext_Zicfilp) && (← (currentlyEnabled
                                                 Ext_S))) : Bool)
                                        then (pure (_get_Mstatus_SPELP v))
                                        else (pure 0#1)))
                                    (← do
                                      if ((← (currentlyEnabled Ext_S)) : Bool)
                                      then (pure (_get_Mstatus_TSR v))
                                      else (pure 0#1)))
                                  (← do
                                    if ((← (currentlyEnabled Ext_U)) : Bool)
                                    then (pure (_get_Mstatus_TW v))
                                    else (pure 0#1)))
                                (← do
                                  if ((← (currentlyEnabled Ext_S)) : Bool)
                                  then (pure (_get_Mstatus_TVM v))
                                  else (pure 0#1)))
                              (← do
                                if ((← (currentlyEnabled Ext_S)) : Bool)
                                then (pure (_get_Mstatus_MXR v))
                                else (pure 0#1)))
                            (← do
                              if ((← (virtual_memory_supported ())) : Bool)
                              then (pure (_get_Mstatus_SUM v))
                              else (pure 0#1)))
                          (← do
                            if ((← (currentlyEnabled Ext_U)) : Bool)
                            then (pure (_get_Mstatus_MPRV v))
                            else (pure 0#1))) (extStatus_map_forwards Off))
                      (legalize_extStatus plat_mstatus_legal_fs (_get_Mstatus_FS v)))
                    (legalize_extStatus plat_mstatus_legal_vs (_get_Mstatus_VS v)))
                  (← do
                    if ((← (have_nominal_privLevel (_get_Mstatus_MPP v))) : Bool)
                    then (pure (_get_Mstatus_MPP v))
                    else (pure (privLevel_to_bits (← (lowest_supported_privLevel ()))))))
                (← do
                  if ((← (currentlyEnabled Ext_S)) : Bool)
                  then (pure (_get_Mstatus_SPP v))
                  else (pure 0#1))) (_get_Mstatus_MPIE v))
            (← do
              if ((← (currentlyEnabled Ext_S)) : Bool)
              then (pure (_get_Mstatus_SPIE v))
              else (pure 0#1)))
          (← do
            if ((not ((← (currentlyEnabled Ext_Smdbltrp)) && ((_get_Mstatus_MDT v) == 1#1))) : Bool)
            then (pure (_get_Mstatus_MIE v))
            else (pure 0#1)))
        (← do
          if (((not ((← (currentlyEnabled Ext_Ssdbltrp)) && ((_get_Mstatus_SDT v) == 1#1))) && (← (currentlyEnabled
                   Ext_S))) : Bool)
          then (pure (_get_Mstatus_SIE v))
          else (pure 0#1))))
  let dirty :=
    (((extStatus_map_backwards (_get_Mstatus_FS o)) == Dirty) || (((extStatus_map_backwards
            (_get_Mstatus_XS o)) == Dirty) || ((extStatus_map_backwards (_get_Mstatus_VS o)) == Dirty)))
  (pure (_update_Mstatus_SD o (bool_to_bit dirty)))

def read_mstatus (_ : Unit) : SailM (BitVec 64) := do
  (pure (_update_Mstatus_SDT (← readReg mstatus)
      (← do
        if ((← (currentlyEnabled Ext_Ssdbltrp)) : Bool)
        then (pure (_get_Mstatus_SDT (← readReg mstatus)))
        else (pure 0#1))))

def undefined_Hstatus (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Hstatus (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Hstatus_HU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_Hstatus_HU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _set_Hstatus_HU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstatus_HU r v)

def _get_Hstatus_HUKTE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_Hstatus_HUKTE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _set_Hstatus_HUKTE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstatus_HUKTE r v)

def _get_Hstatus_HUPMM (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 49 48)

def _update_Hstatus_HUPMM (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 48 x)

def _set_Hstatus_HUPMM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstatus_HUPMM r v)

def _get_Hstatus_SPV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_Hstatus_SPV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Hstatus_SPV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstatus_SPV r v)

def _get_Hstatus_SPVP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_Hstatus_SPVP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _set_Hstatus_SPVP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstatus_SPVP r v)

def _get_Hstatus_VGEIN (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 17 12)

def _update_Hstatus_VGEIN (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 12 x)

def _set_Hstatus_VGEIN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstatus_VGEIN r v)

def _get_Hstatus_VSBE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_Hstatus_VSBE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Hstatus_VSBE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstatus_VSBE r v)

def _get_Hstatus_VSXL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _update_Hstatus_VSXL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _set_Hstatus_VSXL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstatus_VSXL r v)

def _get_Hstatus_VTSR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_Hstatus_VTSR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _set_Hstatus_VTSR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstatus_VTSR r v)

def _get_Hstatus_VTVM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_Hstatus_VTVM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _set_Hstatus_VTVM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstatus_VTVM r v)

def _get_Hstatus_VTW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_Hstatus_VTW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _set_Hstatus_VTW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hstatus_VTW r v)

def legalize_hstatus (h : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_Hstatus v)
  (pure (_update_Hstatus_GVA
      (_update_Hstatus_SPV
        (_update_Hstatus_SPVP
          (_update_Hstatus_HU
            (_update_Hstatus_VGEIN
              (_update_Hstatus_VTVM
                (_update_Hstatus_VTW
                  (_update_Hstatus_VTSR
                    (_update_Hstatus_HUKTE
                      (_update_Hstatus_HUPMM h
                        (← do
                          if (((← (currentlyEnabled Ext_Ssnpm)) && (is_supported_pmm PM_SSNPM
                                 (pmm_mode_backwards (_get_Hstatus_HUPMM v)))) : Bool)
                          then (pure (_get_Hstatus_HUPMM v))
                          else (pure (_get_Hstatus_HUPMM h))))
                      (← do
                        if ((← (currentlyEnabled Ext_Svukte)) : Bool)
                        then (pure (_get_Hstatus_HUKTE v))
                        else (pure 0#1))) (_get_Hstatus_VTSR v)) (_get_Hstatus_VTW v))
                (_get_Hstatus_VTVM v))
              (if (((BitVec.toNatInt (_get_Hstatus_VGEIN v)) ≤b geilen) : Bool)
              then (_get_Hstatus_VGEIN v)
              else (_get_Hstatus_VGEIN h))) (_get_Hstatus_HU v)) (_get_Hstatus_SPVP v))
        (_get_Hstatus_SPV v)) (_get_Hstatus_GVA v)))

def undefined_Seccfg (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _set_Seccfg_MLPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Seccfg_MLPE r v)

def _set_Seccfg_PMM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Seccfg_PMM r v)

def _set_HEnvcfg_PMM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HEnvcfg_PMM r v)

def _set_MEnvcfg_PMM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_PMM r v)

def _set_SEnvcfg_PMM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_PMM r v)

def _set_Seccfg_SSEED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Seccfg_SSEED r v)

def _set_Seccfg_USEED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Seccfg_USEED r v)

def undefined_MEnvcfg (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _set_MEnvcfg_ADUE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_ADUE r v)

def _set_HEnvcfg_ADUE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HEnvcfg_ADUE r v)

def _set_MEnvcfg_CBCFE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_CBCFE r v)

def _set_HEnvcfg_CBCFE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HEnvcfg_CBCFE r v)

def _set_SEnvcfg_CBCFE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_CBCFE r v)

def _set_MEnvcfg_CBIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_CBIE r v)

def _set_HEnvcfg_CBIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HEnvcfg_CBIE r v)

def _set_SEnvcfg_CBIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_CBIE r v)

def _set_MEnvcfg_CBZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_CBZE r v)

def _set_HEnvcfg_CBZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HEnvcfg_CBZE r v)

def _set_SEnvcfg_CBZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_CBZE r v)

def _set_MEnvcfg_DTE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_DTE r v)

def _set_HEnvcfg_DTE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HEnvcfg_DTE r v)

def _set_MEnvcfg_FIOM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_FIOM r v)

def _set_HEnvcfg_FIOM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HEnvcfg_FIOM r v)

def _set_SEnvcfg_FIOM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_FIOM r v)

def _set_MEnvcfg_LPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_LPE r v)

def _set_HEnvcfg_LPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HEnvcfg_LPE r v)

def _set_SEnvcfg_LPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_LPE r v)

def _set_MEnvcfg_PBMTE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_PBMTE r v)

def _set_HEnvcfg_PBMTE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HEnvcfg_PBMTE r v)

def _set_MEnvcfg_SSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_SSE r v)

def _set_HEnvcfg_SSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HEnvcfg_SSE r v)

def _set_SEnvcfg_SSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_SSE r v)

def _set_MEnvcfg_STCE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_STCE r v)

def _set_HEnvcfg_STCE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HEnvcfg_STCE r v)

def undefined_SEnvcfg (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _set_SEnvcfg_UKTE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_UKTE r v)

def undefined_HEnvcfg (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def is_fiom_active (_ : Unit) : SailM Bool := do
  match (← readReg cur_privilege) with
  | .Machine => (pure false)
  | .Supervisor => (pure ((_get_MEnvcfg_FIOM (← readReg menvcfg)) == 1#1))
  | .User =>
    (pure (((_get_MEnvcfg_FIOM (← readReg menvcfg)) ||| (_get_SEnvcfg_FIOM (← readReg senvcfg))) == 1#1))
  | .VirtualSupervisor =>
    (pure (((_get_MEnvcfg_FIOM (← readReg menvcfg)) ||| (_get_HEnvcfg_FIOM (← readReg henvcfg))) == 1#1))
  | .VirtualUser =>
    (pure (((_get_MEnvcfg_FIOM (← readReg menvcfg)) ||| ((_get_HEnvcfg_FIOM (← readReg henvcfg)) ||| (_get_SEnvcfg_FIOM
              (← readReg senvcfg)))) == 1#1))

def undefined_Mtvec (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Mtvec (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_Mtvec_Base (v : (BitVec 32)) : (BitVec (32 - 2)) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 2)

def _update_Mtvec_Base (v : (BitVec 32)) (x : (BitVec (32 - 2))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 2 x)

def _set_Mtvec_Base (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 2))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mtvec_Base r v)

def _get_Mtvec_Mode (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _update_Mtvec_Mode (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _update_Hgatp32_Mode (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_Hgatp64_Mode (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_Satp32_Mode (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_Satp64_Mode (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _set_Mtvec_Mode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mtvec_Mode r v)

def _get_Hgatp32_Mode (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_Hgatp64_Mode (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_Satp32_Mode (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_Satp64_Mode (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _set_Hgatp32_Mode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hgatp32_Mode r v)

def _set_Hgatp64_Mode (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hgatp64_Mode r v)

def _set_Satp32_Mode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp32_Mode r v)

def _set_Satp64_Mode (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp64_Mode r v)

/-- Type quantifiers: vectored_alignment_exp : Nat, k_ex1821835_ : Bool, direct_alignment_exp : Nat, k_ex1821833_
  : Bool, 2 ≤ direct_alignment_exp ∧ direct_alignment_exp ≤ 24, 2 ≤ vectored_alignment_exp
  ∧ vectored_alignment_exp ≤ 24 -/
def legalize_tvec (o : (BitVec 32)) (v : (BitVec 32)) (direct_supported : Bool) (direct_alignment_exp : Nat) (vectored_supported : Bool) (vectored_alignment_exp : Nat) : SailM (BitVec 32) := do
  let v := (Mk_Mtvec v)
  let v ← (( do
    match (trapVectorMode_forwards (_get_Mtvec_Mode v)) with
    | .TV_Direct =>
      (if (direct_supported : Bool)
      then (pure v)
      else (pure (_update_Mtvec_Mode v (_get_Mtvec_Mode o))))
    | .TV_Vector =>
      (if (vectored_supported : Bool)
      then (pure v)
      else (pure (_update_Mtvec_Mode v (_get_Mtvec_Mode o))))
    | _ =>
      (do
        match xtvec_mode_reserved_behavior with
        | .Xtvec_Fatal =>
          (reserved_behavior
            (HAppend.hAppend "Tried to write a reserved value ("
              (HAppend.hAppend (Int.repr (BitVec.toNatInt (_get_Mtvec_Mode v)))
                ") to the MODE field of xtvec.")))
        | .Xtvec_Ignore => (pure (_update_Mtvec_Mode v (_get_Mtvec_Mode o)))) ) : SailM Mtvec )
  let base_alignment ← (( do
    match (trapVectorMode_forwards (_get_Mtvec_Mode v)) with
    | .TV_Direct => (pure direct_alignment_exp)
    | .TV_Vector => (pure vectored_alignment_exp)
    | .TV_Reserved => (internal_error "core/sys_regs.sail" 672 "Reserved mode in xtvec.") ) : SailM
    tvec_alignment )
  if ((base_alignment >b 2) : Bool)
  then
    (pure (_update_Mtvec_Base v
        (Sail.BitVec.updateSubrange (_get_Mtvec_Base v) (base_alignment -i 3) 0
          (zeros (n := ((base_alignment -i 3) -i (0 -i 1)))))))
  else (pure v)

def undefined_Mcause (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Mcause (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_Mcause_Cause (v : (BitVec 32)) : (BitVec (32 - 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 2) 0)

def _update_Mcause_Cause (v : (BitVec 32)) (x : (BitVec (32 - 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 2) 0 x)

def _set_Mcause_Cause (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mcause_Cause r v)

def _get_Mcause_IsInterrupt (v : (BitVec 32)) : (BitVec (32 - 1 - (32 - 1) + 1)) :=
  (Sail.BitVec.extractLsb v (32 -i 1) (32 -i 1))

def _update_Mcause_IsInterrupt (v : (BitVec 32)) (x : (BitVec (32 - 1 - (32 - 1) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) (32 -i 1) x)

def _set_Mcause_IsInterrupt (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec (32 - 1 - (32 - 1) + 1))) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mcause_IsInterrupt r v)

/-- Type quantifiers: k_ex1821837_ : Bool -/
def legalize_cause (o : (BitVec 32)) (v : (BitVec 32)) (is_scause : Bool) : SailM (BitVec 32) := SailME.run do
  let v := (Mk_Mcause v)
  let code := (_get_Mcause_Cause v)
  if ((is_scause && (((BitVec.toNatInt code) ≤b 31) : Bool)) : Bool)
  then (pure v)
  else
    (do
      if (((_get_Mcause_IsInterrupt v) == 1#1) : Bool)
      then
        (do
          let is_platform_interrupt :=
            ((code &&& (sign_extend (m := (32 -i 1)) 0xF0#8)) != (zeros (n := (32 -i 1))))
          if (is_platform_interrupt : Bool)
          then SailME.throw (o : (BitVec 32))
          else
            (do
              let intr ← do (interruptType_bits_backwards (Sail.BitVec.extractLsb code 5 0))
              if ((is_reserved_interrupt intr) : Bool)
              then SailME.throw (o : (BitVec 32))
              else
                (do
                  if (((intr == I_COF) && (not (hartSupports Ext_Sscofpmf))) : Bool)
                  then SailME.throw (o : (BitVec 32))
                  else
                    (do
                      if (((is_hypervisor_interrupt intr) && (not (hartSupports Ext_H))) : Bool)
                      then SailME.throw (o : (BitVec 32))
                      else (pure ())))))
      else
        (do
          if (((code &&& (sign_extend (m := (32 -i 1)) 0xC0#8)) != (zeros (n := (32 -i 1)))) : Bool)
          then SailME.throw (o : (BitVec 32))
          else
            (do
              let code := (Sail.BitVec.extractLsb code 5 0)
              if ((not (← (exceptionType_bits_backwards_matches code))) : Bool)
              then SailME.throw (o : (BitVec 32))
              else
                (do
                  let exc ← do (exceptionType_bits_backwards code)
                  if ((is_reserved_or_custom_exception exc) : Bool)
                  then SailME.throw (o : (BitVec 32))
                  else
                    (do
                      if (((exc == (E_Double_Trap ())) && (not (hartSupports Ext_Ssdbltrp))) : Bool)
                      then SailME.throw (o : (BitVec 32))
                      else
                        (do
                          if (((exc == (E_Software_Check ())) && (not
                                 ((hartSupports Ext_Zicfilp) || (hartSupports Ext_Zicfiss)))) : Bool)
                          then SailME.throw (o : (BitVec 32))
                          else
                            (do
                              if (((exc == (E_Hardware_Error ())) && (privileged_isa_version_lt
                                     priv_isa_version Privileged_ISA_1_13)) : Bool)
                              then SailME.throw (o : (BitVec 32))
                              else
                                (do
                                  if (((is_hypervisor_exception exc) && (not (hartSupports Ext_H))) : Bool)
                                  then SailME.throw (o : (BitVec 32))
                                  else (pure ()))))))))
      (pure v))

def tvec_addr (m : (BitVec 32)) (c : (BitVec 32)) : (Option (BitVec 32)) :=
  let base : xlenbits := ((_get_Mtvec_Base m) +++ 0b00#2)
  match (trapVectorMode_forwards (_get_Mtvec_Mode m)) with
  | .TV_Direct => (some base)
  | .TV_Vector =>
    (if (((_get_Mcause_IsInterrupt c) == 1#1) : Bool)
    then (some (base + ((zero_extend (m := 32) (_get_Mcause_Cause c)) <<< 2)))
    else (some base))
  | .TV_Reserved => none

def legalize_xepc (v : (BitVec 32)) : (BitVec 32) :=
  if ((hartSupports Ext_Zca) : Bool)
  then (BitVec.update v 0 0#1)
  else (Sail.BitVec.updateSubrange v 1 0 (zeros (n := (1 -i (0 -i 1)))))

def align_pc (addr : (BitVec 32)) : SailM (BitVec 32) := do
  if ((← (currentlyEnabled Ext_Zca)) : Bool)
  then (pure (BitVec.update addr 0 0#1))
  else (pure (Sail.BitVec.updateSubrange addr 1 0 (zeros (n := (1 -i (0 -i 1))))))

def undefined_Counteren (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Counteren (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_Counteren_CY (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_Counteren_CY (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_Counterin_CY (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Counteren_CY (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counteren_CY r v)

def _get_Counterin_CY (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _set_Counterin_CY (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counterin_CY r v)

def _get_Counteren_HPM (v : (BitVec 32)) : (BitVec 29) :=
  (Sail.BitVec.extractLsb v 31 3)

def _update_Counteren_HPM (v : (BitVec 32)) (x : (BitVec 29)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 3 x)

def _update_Counterin_HPM (v : (BitVec 32)) (x : (BitVec 29)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 3 x)

def _set_Counteren_HPM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 29)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counteren_HPM r v)

def _get_Counterin_HPM (v : (BitVec 32)) : (BitVec 29) :=
  (Sail.BitVec.extractLsb v 31 3)

def _set_Counterin_HPM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 29)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counterin_HPM r v)

def _get_Counteren_IR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_Counteren_IR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_Counterin_IR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _set_Counteren_IR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counteren_IR r v)

def _get_Counterin_IR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _set_Counterin_IR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counterin_IR r v)

def _get_Counteren_TM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Counteren_TM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Counteren_TM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counteren_TM r v)

def sys_scounteren_writable_bits : (BitVec 32) := 0b11111111111111111111111111111111#32

def legalize_scounteren (_c : (BitVec 32)) (v : (BitVec 32)) : (BitVec 32) :=
  (Mk_Counteren ((Sail.BitVec.extractLsb v 31 0) &&& sys_scounteren_writable_bits))

def sys_hcounteren_writable_bits : (BitVec 32) := 0b11111111111111111111111111111111#32

def legalize_hcounteren (_c : (BitVec 32)) (v : (BitVec 32)) : (BitVec 32) :=
  (Mk_Counteren ((Sail.BitVec.extractLsb v 31 0) &&& sys_hcounteren_writable_bits))

def sys_mcounteren_writable_bits : (BitVec 32) := 0b11111111111111111111111111111111#32

def legalize_mcounteren (_c : (BitVec 32)) (v : (BitVec 32)) : (BitVec 32) :=
  (Mk_Counteren ((Sail.BitVec.extractLsb v 31 0) &&& sys_mcounteren_writable_bits))

def undefined_Counterin (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Counterin (v : (BitVec 32)) : (BitVec 32) :=
  v

def legalize_mcountinhibit (_c : (BitVec 32)) (v : (BitVec 32)) : (BitVec 32) :=
  (Mk_Counterin ((Sail.BitVec.extractLsb v 31 0) &&& plat_mcountinhibit_writable_bits))

def undefined_Sstatus (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Sstatus (v : (BitVec 64)) : (BitVec 64) :=
  v

/-- Type quantifiers: k_ex1821863_ : Bool -/
def lower_mstatus (m : (BitVec 64)) (virt : Bool) : SailM (BitVec 64) := do
  let s := (Mk_Sstatus (zeros (n := 64)))
  (pure (_update_Sstatus_SIE
      (_update_Sstatus_SPIE
        (_update_Sstatus_SPP
          (_update_Sstatus_VS
            (_update_Sstatus_FS
              (_update_Sstatus_XS
                (_update_Sstatus_SUM
                  (_update_Sstatus_MXR
                    (_update_Sstatus_SPELP
                      (_update_Sstatus_SDT
                        (_update_Sstatus_UXL (_update_Sstatus_SD s (_get_Mstatus_SD m))
                          (_get_Mstatus_UXL m))
                        (← do
                          if (((← (currentlyEnabled Ext_Ssdbltrp)) && ((not virt) || ((_get_HEnvcfg_DTE
                                     (← (read_henvcfg ()))) == 1#1))) : Bool)
                          then (pure (_get_Mstatus_SDT m))
                          else (pure 0#1))) (_get_Mstatus_SPELP m)) (_get_Mstatus_MXR m))
                  (_get_Mstatus_SUM m)) (_get_Mstatus_XS m)) (_get_Mstatus_FS m))
            (_get_Mstatus_VS m)) (_get_Mstatus_SPP m)) (_get_Mstatus_SPIE m)) (_get_Mstatus_SIE m)))

def lift_sstatus (m : (BitVec 64)) (s : (BitVec 64)) : (BitVec 64) :=
  let dirty :=
    (((extStatus_map_backwards (_get_Sstatus_FS s)) == Dirty) || (((extStatus_map_backwards
            (_get_Sstatus_XS s)) == Dirty) || ((extStatus_map_backwards (_get_Sstatus_VS s)) == Dirty)))
  (_update_Mstatus_SIE
    (_update_Mstatus_SPIE
      (_update_Mstatus_SPP
        (_update_Mstatus_VS
          (_update_Mstatus_FS
            (_update_Mstatus_XS
              (_update_Mstatus_SUM
                (_update_Mstatus_MXR
                  (_update_Mstatus_SPELP
                    (_update_Mstatus_SDT
                      (_update_Mstatus_UXL (_update_Mstatus_SD m (bool_to_bit dirty))
                        (_get_Sstatus_UXL s)) (_get_Sstatus_SDT s)) (_get_Sstatus_SPELP s))
                  (_get_Sstatus_MXR s)) (_get_Sstatus_SUM s)) (_get_Sstatus_XS s))
            (_get_Sstatus_FS s)) (_get_Sstatus_VS s)) (_get_Sstatus_SPP s)) (_get_Sstatus_SPIE s))
    (_get_Sstatus_SIE s))

/-- Type quantifiers: k_ex1821864_ : Bool -/
def legalize_sstatus (m : (BitVec 64)) (v : (BitVec 32)) (virt : Bool) : SailM (BitVec 64) := do
  let s := (Mk_Sstatus (zero_extend (m := 64) v))
  let s ← do
    (pure (_update_Sstatus_SDT s
        (← do
          if ((virt && ((_get_HEnvcfg_DTE (← (read_henvcfg ()))) == 0#1)) : Bool)
          then (pure 0#1)
          else (pure (_get_Sstatus_SDT s)))))
  (legalize_mstatus m (lift_sstatus m s))

def undefined_Hgatp64 (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Hgatp64 (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Hgatp64_PPN (v : (BitVec 64)) : (BitVec 44) :=
  (Sail.BitVec.extractLsb v 43 0)

def _update_Hgatp64_PPN (v : (BitVec 64)) (x : (BitVec 44)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 0 x)

def _update_Hgatp32_PPN (v : (BitVec 32)) (x : (BitVec 22)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 0 x)

def _update_Satp32_PPN (v : (BitVec 32)) (x : (BitVec 22)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 0 x)

def _update_Satp64_PPN (v : (BitVec 64)) (x : (BitVec 44)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 0 x)

def _set_Hgatp64_PPN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 44)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hgatp64_PPN r v)

def _get_Hgatp32_PPN (v : (BitVec 32)) : (BitVec 22) :=
  (Sail.BitVec.extractLsb v 21 0)

def _get_Satp32_PPN (v : (BitVec 32)) : (BitVec 22) :=
  (Sail.BitVec.extractLsb v 21 0)

def _get_Satp64_PPN (v : (BitVec 64)) : (BitVec 44) :=
  (Sail.BitVec.extractLsb v 43 0)

def _set_Hgatp32_PPN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 22)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hgatp32_PPN r v)

def _set_Satp32_PPN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 22)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp32_PPN r v)

def _set_Satp64_PPN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 44)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp64_PPN r v)

def _get_Hgatp64_VMID (v : (BitVec 64)) : (BitVec 14) :=
  (Sail.BitVec.extractLsb v 57 44)

def _update_Hgatp64_VMID (v : (BitVec 64)) (x : (BitVec 14)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 44 x)

def _update_Hgatp32_VMID (v : (BitVec 32)) (x : (BitVec 7)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 22 x)

def _set_Hgatp64_VMID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 14)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hgatp64_VMID r v)

def _get_Hgatp32_VMID (v : (BitVec 32)) : (BitVec 7) :=
  (Sail.BitVec.extractLsb v 28 22)

def _set_Hgatp32_VMID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 7)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Hgatp32_VMID r v)

def undefined_Hgatp32 (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Hgatp32 (v : (BitVec 32)) : (BitVec 32) :=
  v

def legalize_hgatp (arch : Architecture) (prev_value : (BitVec 32)) (written_value : (BitVec 32)) : SailM (BitVec 32) := do
  let v := (Mk_Hgatp32 written_value)
  let h :=
    (Mk_Hgatp32
      ((_get_Hgatp32_Mode v) +++ (0b00#2 +++ ((_get_Hgatp32_VMID v) +++ ((Sail.BitVec.extractLsb
                (_get_Hgatp32_PPN v) 21 2) +++ 0b00#2)))))
  let h :=
    (_update_Hgatp32_PPN
      (_update_Hgatp32_VMID h
        (zero_extend (m := 7) (Sail.BitVec.extractLsb (_get_Hgatp32_VMID h) (vmidlen -i 1) 0)))
      (zero_extend (m := 22)
        (Sail.BitVec.extractLsb (_get_Hgatp32_PPN h) ((physaddr_bits -i pagesize_bits) -i 1) 0)))
  match (← (hgatpMode_of_bits arch (0b000#3 +++ (_get_Hgatp32_Mode h)))) with
  | none => (pure (_update_Hgatp32_Mode h (_get_Hgatp32_Mode (Mk_Hgatp32 prev_value))))
  | .some mode =>
    (match mode with
    | .HBare => (pure h)
    | .Sv32x4 =>
      (if (sys_hgatp_sv32x4_supported : Bool)
      then (pure h)
      else (pure (_update_Hgatp32_Mode h (_get_Hgatp32_Mode (Mk_Hgatp32 prev_value)))))
    | _ => (pure (_update_Hgatp32_Mode h (_get_Hgatp32_Mode (Mk_Hgatp32 prev_value)))))

def undefined_Satp64 (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Satp64 (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Satp64_Asid (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 59 44)

def _update_Satp64_Asid (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 44 x)

def _update_Satp32_Asid (v : (BitVec 32)) (x : (BitVec 9)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 22 x)

def _set_Satp64_Asid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp64_Asid r v)

def _get_Satp32_Asid (v : (BitVec 32)) : (BitVec 9) :=
  (Sail.BitVec.extractLsb v 30 22)

def _set_Satp32_Asid (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 9)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp32_Asid r v)

def undefined_Satp32 (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Satp32 (v : (BitVec 32)) : (BitVec 32) :=
  v

/-- Type quantifiers: k_ex1821865_ : Bool -/
def legalize_satp (arch : Architecture) (is_vsatp : Bool) (prev_value : (BitVec 32)) (written_value : (BitVec 32)) : SailM (BitVec 32) := do
  let s := (Mk_Satp32 written_value)
  let s :=
    (_update_Satp32_Asid s
      (zero_extend (m := 9) (Sail.BitVec.extractLsb (_get_Satp32_Asid s) (asidlen -i 1) 0)))
  let s :=
    if (is_vsatp : Bool)
    then s
    else
      (_update_Satp32_PPN s
        (zero_extend (m := 22)
          (Sail.BitVec.extractLsb (_get_Satp32_PPN s) ((physaddr_bits -i pagesize_bits) -i 1) 0)))
  let sv32_supported ← do
    if (is_vsatp : Bool)
    then (pure sys_vsatp_sv32_supported)
    else (currentlyEnabled Ext_Sv32)
  match (← (satpMode_of_bits arch (0b000#3 +++ (_get_Satp32_Mode s)))) with
  | none => (pure prev_value)
  | .some Sv_mode =>
    (do
      match Sv_mode with
      | .Bare =>
        (do
          if ((is_vsatp || (← (currentlyEnabled Ext_Svbare))) : Bool)
          then (pure s)
          else (pure prev_value))
      | .Sv32 =>
        (if (sv32_supported : Bool)
        then (pure s)
        else (pure prev_value))
      | _ => (pure prev_value))

def undefined_FeatureEnabledResult (_ : Unit) : SailM FeatureEnabledResult := do
  (internal_pick [FEATURE_ENABLED, FEATURE_ILLEGAL, FEATURE_VIRTUAL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def FeatureEnabledResult_of_num (arg_ : Nat) : FeatureEnabledResult :=
  match arg_ with
  | 0 => FEATURE_ENABLED
  | 1 => FEATURE_ILLEGAL
  | _ => FEATURE_VIRTUAL

def num_of_FeatureEnabledResult (arg_ : FeatureEnabledResult) : Int :=
  match arg_ with
  | .FEATURE_ENABLED => 0
  | .FEATURE_ILLEGAL => 1
  | .FEATURE_VIRTUAL => 2

def feature_enabled_for_priv (p : Privilege) (machine_enable_bit : (BitVec 1)) (supervisor_enable_bit : (BitVec 1)) (hypervisor_enable_bit : (BitVec 1)) : SailM FeatureEnabledResult := do
  match p with
  | .Machine => (pure FEATURE_ENABLED)
  | .Supervisor =>
    (if ((machine_enable_bit == 1#1) : Bool)
    then (pure FEATURE_ENABLED)
    else (pure FEATURE_ILLEGAL))
  | .User =>
    (do
      if (((machine_enable_bit == 1#1) && ((not (← (currentlyEnabled Ext_S))) || (supervisor_enable_bit == 1#1))) : Bool)
      then (pure FEATURE_ENABLED)
      else (pure FEATURE_ILLEGAL))
  | .VirtualSupervisor =>
    (if ((machine_enable_bit == 0#1) : Bool)
    then (pure FEATURE_ILLEGAL)
    else
      (if ((hypervisor_enable_bit == 0#1) : Bool)
      then (pure FEATURE_VIRTUAL)
      else (pure FEATURE_ENABLED)))
  | .VirtualUser =>
    (if ((machine_enable_bit == 0#1) : Bool)
    then (pure FEATURE_ILLEGAL)
    else
      (if (((hypervisor_enable_bit == 0#1) || (supervisor_enable_bit == 0#1)) : Bool)
      then (pure FEATURE_VIRTUAL)
      else (pure FEATURE_ENABLED)))

/-- Type quantifiers: index : Nat, 0 ≤ index ∧ index ≤ 31 -/
def counter_enabled (index : Nat) (priv : Privilege) : SailM Bool := do
  match (← (feature_enabled_for_priv priv (BitVec.access (← readReg mcounteren) index)
      (BitVec.access (← readReg scounteren) index) (BitVec.access (← readReg hcounteren) index))) with
  | .FEATURE_ENABLED => (pure true)
  | _ => (pure false)

