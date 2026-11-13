import SailRV32.Flow
import SailRV32.Arith
import SailRV32.Prelude
import SailRV32.Errors
import SailRV32.MemAddrtype
import SailRV32.PlatformConfig
import SailRV32.Regs
import SailRV32.Mem
import SailRV32.Vmem
import SailRV32.InstsBegin
import SailRV32.VmemUtils

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

def encdec_cbop_backwards (arg_ : (BitVec 12)) : SailM cbop_zicbom := do
  match arg_ with
  | 0b000000000001 => (pure CBO_CLEAN)
  | 0b000000000010 => (pure CBO_FLUSH)
  | 0b000000000000 => (pure CBO_INVAL)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_cbop_forwards_matches (arg_ : cbop_zicbom) : Bool :=
  match arg_ with
  | .CBO_CLEAN => true
  | .CBO_FLUSH => true
  | .CBO_INVAL => true

def encdec_cbop_backwards_matches (arg_ : (BitVec 12)) : Bool :=
  match arg_ with
  | 0b000000000001 => true
  | 0b000000000010 => true
  | 0b000000000000 => true
  | _ => false

def cbop_mnemonic_backwards (arg_ : String) : SailM cbop_zicbom := do
  match arg_ with
  | "cbo.clean" => (pure CBO_CLEAN)
  | "cbo.flush" => (pure CBO_FLUSH)
  | "cbo.inval" => (pure CBO_INVAL)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def cbop_mnemonic_forwards_matches (arg_ : cbop_zicbom) : Bool :=
  match arg_ with
  | .CBO_CLEAN => true
  | .CBO_FLUSH => true
  | .CBO_INVAL => true

def cbop_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "cbo.clean" => true
  | "cbo.flush" => true
  | "cbo.inval" => true
  | _ => false

def undefined_cbie (_ : Unit) : SailM cbie := do
  (internal_pick [CBIE_ILLEGAL, CBIE_EXEC_FLUSH, CBIE_EXEC_INVAL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def cbie_of_num (arg_ : Nat) : cbie :=
  match arg_ with
  | 0 => CBIE_ILLEGAL
  | 1 => CBIE_EXEC_FLUSH
  | _ => CBIE_EXEC_INVAL

def num_of_cbie (arg_ : cbie) : Int :=
  match arg_ with
  | .CBIE_ILLEGAL => 0
  | .CBIE_EXEC_FLUSH => 1
  | .CBIE_EXEC_INVAL => 2

def encdec_cbie_forwards (arg_ : cbie) : (BitVec 2) :=
  match arg_ with
  | .CBIE_ILLEGAL => 0b00#2
  | .CBIE_EXEC_FLUSH => 0b01#2
  | .CBIE_EXEC_INVAL => 0b11#2

def encdec_cbie_backwards (arg_ : (BitVec 2)) : SailM cbie := do
  match arg_ with
  | 0b00 => (pure CBIE_ILLEGAL)
  | 0b01 => (pure CBIE_EXEC_FLUSH)
  | 0b11 => (pure CBIE_EXEC_INVAL)
  | _ => (internal_error "extensions/Zicbom/zicbom_insts.sail" 43 "reserved CBIE")

def encdec_cbie_forwards_matches (arg_ : cbie) : Bool :=
  match arg_ with
  | .CBIE_ILLEGAL => true
  | .CBIE_EXEC_FLUSH => true
  | .CBIE_EXEC_INVAL => true

def encdec_cbie_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b11 => true
  | 0b10 => true
  | _ => false

def undefined_checked_cbop (_ : Unit) : SailM checked_cbop := do
  (internal_pick [CBOP_ILLEGAL, CBOP_ILLEGAL_VIRTUAL, CBOP_INVAL_FLUSH, CBOP_INVAL_INVAL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def checked_cbop_of_num (arg_ : Nat) : checked_cbop :=
  match arg_ with
  | 0 => CBOP_ILLEGAL
  | 1 => CBOP_ILLEGAL_VIRTUAL
  | 2 => CBOP_INVAL_FLUSH
  | _ => CBOP_INVAL_INVAL

def num_of_checked_cbop (arg_ : checked_cbop) : Int :=
  match arg_ with
  | .CBOP_ILLEGAL => 0
  | .CBOP_ILLEGAL_VIRTUAL => 1
  | .CBOP_INVAL_FLUSH => 2
  | .CBOP_INVAL_INVAL => 3

def cbop_priv_check (p : Privilege) : SailM checked_cbop := do
  let mCBIE ← (( do (encdec_cbie_backwards (_get_MEnvcfg_CBIE (← readReg menvcfg))) ) : SailM
    cbie )
  let sCBIE ← (( do
    if ((← (currentlyEnabled Ext_S)) : Bool)
    then (encdec_cbie_backwards (_get_SEnvcfg_CBIE (← (read_senvcfg ()))))
    else (encdec_cbie_backwards (_get_MEnvcfg_CBIE (← readReg menvcfg))) ) : SailM cbie )
  let hCBIE ← (( do
    if ((← (currentlyEnabled Ext_H)) : Bool)
    then (encdec_cbie_backwards (_get_HEnvcfg_CBIE (← (read_henvcfg ()))))
    else (encdec_cbie_backwards (_get_MEnvcfg_CBIE (← readReg menvcfg))) ) : SailM cbie )
  if ((((bne p Machine) && (mCBIE == CBIE_ILLEGAL)) || ((p == User) && (sCBIE == CBIE_ILLEGAL))) : Bool)
  then (pure CBOP_ILLEGAL)
  else
    (if ((((p == VirtualSupervisor) && (hCBIE == CBIE_ILLEGAL)) || ((p == VirtualUser) && ((hCBIE == CBIE_ILLEGAL) || (sCBIE == CBIE_ILLEGAL)))) : Bool)
    then (pure CBOP_ILLEGAL_VIRTUAL)
    else
      (if ((((bne p Machine) && (mCBIE == CBIE_EXEC_FLUSH)) || (((p == User) && (sCBIE == CBIE_EXEC_FLUSH)) || (((p == VirtualSupervisor) && (hCBIE == CBIE_EXEC_FLUSH)) || ((p == VirtualUser) && ((hCBIE == CBIE_EXEC_FLUSH) || (sCBIE == CBIE_EXEC_FLUSH)))))) : Bool)
      then (pure CBOP_INVAL_FLUSH)
      else (pure CBOP_INVAL_INVAL)))

def process_clean_inval (rs1 : regidx) (cbop : cbop_zicbom) : SailM ExecutionResult := do
  let rs1_val ← do (rX_bits rs1)
  let cache_block_size := (2 ^i plat_cache_block_size_exp)
  let access : (MemoryAccessType mem_payload) := (CacheAccess (CB_manage cbop))
  let access_info ← do (default_access_info access)
  let eff_priv := access_info.eff_privilege
  let negative_offset :=
    ((rs1_val &&& (Complement.complement
          (zero_extend (m := 32) (ones (n := plat_cache_block_size_exp))))) - rs1_val)
  match (← (get_transformed_data_addr rs1 negative_offset access access_info cache_block_size)) with
  | .Ext_DataAddr_Error e => (pure (Ext_DataAddr_Check_Failure e))
  | .Ext_DataAddr_OK vaddr =>
    (do
      let vaddr_for_error := (sub_virtaddr_xlenbits vaddr negative_offset)
      match (← (translateAddr vaddr access eff_priv)) with
      | .Ok (paddr, pbmt, _) =>
        (do
          match (← (phys_access_check access pbmt eff_priv paddr cache_block_size false)) with
          | .Err e => (memory_exception e (bits_of_virtaddr vaddr_for_error) access_info)
          | .Ok _ => (pure RETIRE_SUCCESS))
      | .Err (e, _) => (trap { e with excinfo := (bits_of_virtaddr vaddr_for_error) }))

