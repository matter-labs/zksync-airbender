import SailRV32.Flow
import SailRV32.Prelude
import SailRV32.RvfiDii
import SailRV32.PlatformConfig
import SailRV32.Types
import SailRV32.PcAccess
import SailRV32.SysRegs
import SailRV32.AddrChecks
import SailRV32.SyncException
import SailRV32.SysControl
import SailRV32.Vmem

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

def rvfi_fetch (_ : Unit) : SailM FetchResult := SailME.run do
  writeReg rvfi_inst_data (Sail.BitVec.updateSubrange (← readReg rvfi_inst_data) 63 0
    (← readReg minstret))
  writeReg rvfi_pc_data (Sail.BitVec.updateSubrange (← readReg rvfi_pc_data) 63 0
    (zero_extend (m := 64) (← (get_arch_pc ()))))
  writeReg rvfi_inst_data (Sail.BitVec.updateSubrange (← readReg rvfi_inst_data) 159 152
    (zero_extend (m := 8) (privLevel_to_bits (← readReg cur_privilege))))
  writeReg rvfi_inst_data (Sail.BitVec.updateSubrange (← readReg rvfi_inst_data) 167 160
    (zero_extend (m := 8) (_get_Misa_MXL (← readReg misa))))
  match (ext_fetch_check_pc (← readReg PC) (← readReg PC)) with
  | .some e => SailME.throw ((F_Ext_Error e) : FetchResult)
  | none => (pure ())
  if ((((BitVec.access (← readReg PC) 0) != 0#1) || (((BitVec.access (← readReg PC) 1) != 0#1) && (not
           (← (currentlyEnabled Ext_Zca))))) : Bool)
  then (pure (F_Error (← (exception_context (E_Fetch_Addr_Align ()) (← readReg PC)))))
  else
    (do
      let access : (MemoryAccessType mem_payload) := (InstructionFetch ())
      let eff_priv ← do
        (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))
      match (← (translateAddr (Virtaddr (← readReg PC)) access eff_priv)) with
      | .Err (e, _) => SailME.throw ((F_Error e) : FetchResult)
      | .Ok (_, _, _) => (pure ())
      let i ← do
        (pure (_get_RVFI_DII_Instruction_Packet_rvfi_insn (← readReg rvfi_instruction)))
      writeReg rvfi_inst_data (Sail.BitVec.updateSubrange (← readReg rvfi_inst_data) 127 64
        (zero_extend (m := 64) i))
      if (((Sail.BitVec.extractLsb i 1 0) != 0b11#2) : Bool)
      then (pure (F_RVC (Sail.BitVec.extractLsb i 15 0)))
      else
        (do
          let PC_hi ← do (pure (BitVec.addInt (← readReg PC) 2))
          match (ext_fetch_check_pc (← readReg PC) PC_hi) with
          | .some e => SailME.throw ((F_Ext_Error e) : FetchResult)
          | none => (pure ())
          match (← (translateAddr (Virtaddr PC_hi) access eff_priv)) with
          | .Err (e, _) => (pure (F_Error { e with excinfo := ← readReg PC }))
          | .Ok (_, _, _) => (pure (F_Base i))))

