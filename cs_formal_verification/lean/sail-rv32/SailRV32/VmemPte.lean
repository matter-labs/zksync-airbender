import SailRV32.Flow
import SailRV32.Prelude
import SailRV32.Errors
import SailRV32.IsaVersion
import SailRV32.PlatformConfig
import SailRV32.Types
import SailRV32.VmemTypes
import SailRV32.SysRegs
import SailRV32.VextRegs

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

def undefined_PTE_Ext (_ : Unit) : SailM (BitVec 10) := do
  (undefined_bitvector 10)

def Mk_PTE_Ext (v : (BitVec 10)) : (BitVec 10) :=
  v

def _get_PTE_Ext_PBMT (v : (BitVec 10)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 8 7)

def _update_PTE_Ext_PBMT (v : (BitVec 10)) (x : (BitVec 2)) : (BitVec 10) :=
  (Sail.BitVec.updateSubrange v 8 7 x)

def _set_PTE_Ext_PBMT (r_ref : (RegisterRef (BitVec 10))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Ext_PBMT r v)

def _get_PTE_Ext_RSW_60t59b (v : (BitVec 10)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 6 5)

def _update_PTE_Ext_RSW_60t59b (v : (BitVec 10)) (x : (BitVec 2)) : (BitVec 10) :=
  (Sail.BitVec.updateSubrange v 6 5 x)

def _set_PTE_Ext_RSW_60t59b (r_ref : (RegisterRef (BitVec 10))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Ext_RSW_60t59b r v)

def default_sv32_ext_pte : pte_ext_bits := (zeros (n := 10))

/-- Type quantifiers: k_pte_size : Nat, k_pte_size ≥ 0, List.elem k_pte_size [32, 64] -/
def ext_bits_of_PTE (pte : (BitVec k_pte_size)) : (BitVec 10) :=
  (Mk_PTE_Ext
    (if (((Sail.BitVec.length pte) == 64) : Bool)
    then (Sail.BitVec.extractLsb pte 63 54)
    else default_sv32_ext_pte))

/-- Type quantifiers: k_pte_size : Nat, k_pte_size ≥ 0, List.elem k_pte_size [32, 64] -/
def PPN_of_PTE (pte : (BitVec k_pte_size)) : (BitVec (if ( k_pte_size = 32  : Bool) then 22 else 44)) :=
  if (((Sail.BitVec.length pte) == 32) : Bool)
  then (Sail.BitVec.extractLsb pte 31 10)
  else (Sail.BitVec.extractLsb pte 53 10)

def undefined_PTE_Flags (_ : Unit) : SailM (BitVec 8) := do
  (undefined_bitvector 8)

def Mk_PTE_Flags (v : (BitVec 8)) : (BitVec 8) :=
  v

def pte_is_non_leaf (pte_flags : (BitVec 8)) : Bool :=
  (((_get_PTE_Flags_X pte_flags) == 0#1) && (((_get_PTE_Flags_W pte_flags) == 0#1) && ((_get_PTE_Flags_R
          pte_flags) == 0#1)))

def pte_is_invalid (pte_flags : (BitVec 8)) (pte_ext : (BitVec 10)) (stage : TranslationStage) : SailM Bool := do
  (pure (((_get_PTE_Flags_V pte_flags) == 0#1) || ((((_get_PTE_Flags_R pte_flags) == 0#1) && (((_get_PTE_Flags_W
                pte_flags) == 1#1) && (((_get_PTE_Flags_X pte_flags) == 0#1) && (← do
                match stage with
                | .G_Stage => (pure true)
                | .VS_Stage =>
                  (pure (((_get_MEnvcfg_SSE (← readReg menvcfg)) == 0#1) || ((_get_HEnvcfg_SSE
                          (← (read_henvcfg ()))) == 0#1)))
                | .S_Stage => (pure ((_get_MEnvcfg_SSE (← readReg menvcfg)) == 0#1)))))) || ((((_get_PTE_Flags_R
                pte_flags) == 0#1) && (((_get_PTE_Flags_W pte_flags) == 1#1) && ((_get_PTE_Flags_X
                  pte_flags) == 1#1))) || (((not
                (page_based_mem_type_forwards_matches (_get_PTE_Ext_PBMT pte_ext))) && (← (currentlyEnabled
                  Ext_Svpbmt))) || (pte_reserved_bits_must_be_zero && (((pte_is_non_leaf pte_flags) && (((_get_PTE_Flags_A
                        pte_flags) == 1#1) || (((_get_PTE_Flags_D pte_flags) == 1#1) || (((_get_PTE_Flags_U
                            pte_flags) == 1#1) || ((_update_PTE_Ext_RSW_60t59b pte_ext
                            (zeros (n := 2))) != (zeros (n := 10))))))) || ((((_get_PTE_Ext_N
                        pte_ext) != (zeros (n := 1))) && (not (← (currentlyEnabled Ext_Svnapot)))) || ((((_get_PTE_Ext_PBMT
                          pte_ext) != (zeros (n := 2))) && (((_get_MEnvcfg_PBMTE
                            (← readReg menvcfg)) == 0#1) || (((stage == VS_Stage) && ((_get_HEnvcfg_PBMTE
                                (← (read_henvcfg ()))) == 0#1)) || (not
                            (page_based_mem_type_forwards_matches (_get_PTE_Ext_PBMT pte_ext)))))) || ((((_get_PTE_Ext_RSW_60t59b
                            pte_ext) != (zeros (n := 2))) && (not
                          (← (currentlyEnabled Ext_Svrsw60t59b)))) || ((_get_PTE_Ext_reserved
                          pte_ext) != (zeros (n := 5)))))))))))))

/-- Type quantifiers: k_ex1822091_ : Bool, k_ex1822090_ : Bool -/
def check_PTE_permission (access : (MemoryAccessType mem_payload)) (priv : Privilege) (stage : TranslationStage) (mxr : Bool) (do_sum : Bool) (pte_flags : (BitVec 8)) (_ext : (BitVec 10)) (_ext_ptw : Unit) : SailM PTE_Check := SailME.run do
  let pte_U := (bit_to_bool (_get_PTE_Flags_U pte_flags))
  let pte_R := (bit_to_bool (_get_PTE_Flags_R pte_flags))
  let pte_W := (bit_to_bool (_get_PTE_Flags_W pte_flags))
  let pte_X := (bit_to_bool (_get_PTE_Flags_X pte_flags))
  «assert» (zopz0zJzJzK pte_W (pte_R || (not pte_X))) "sys/vmem_pte.sail:160.39-160.40"
  let priv_ok ← (( do
    match priv with
    | .User => (pure pte_U)
    | .Supervisor => (pure ((not pte_U) || (do_sum && (is_load_store access))))
    | .Machine => (internal_error "sys/vmem_pte.sail" 168 "m-mode mem perm check")
    | .VirtualUser => (pure pte_U)
    | .VirtualSupervisor => (pure ((not pte_U) || (do_sum && (is_load_store access)))) ) : SailME
    PTE_Check Bool )
  if ((not priv_ok) : Bool)
  then (pure (PTE_Check_Failure ((), (PTE_No_Permission ()))))
  else
    (do
      if ((stage == G_Stage) : Bool)
      then
        (do
          if (((← (is_shadow_stack_access access)) && (not (pte_R && pte_W))) : Bool)
          then SailME.throw ((PTE_Check_Failure ((), (PTE_No_Permission ()))) : PTE_Check)
          else (pure ()))
      else
        (do
          if (((not pte_R) && (pte_W && (not pte_X))) : Bool)
          then
            SailME.throw (← do
                «assert» (bool_bit_backwards (_get_MEnvcfg_SSE (← readReg menvcfg))) "sys/vmem_pte.sail:186.33-186.34"
                let shadow_stack_ok ← (( do
                  match access with
                  | .InstructionFetch () => (pure false)
                  | .Load .PageTableEntry => (pure false)
                  | .Store .PageTableEntry => (pure false)
                  | .Load .Data => (pure true)
                  | .Load .Vector => (pure true)
                  | .Load .ShadowStack => (pure true)
                  | .LoadExecute .Data => (pure true)
                  | .LoadReserved (_, _, .Data) => (pure true)
                  | .Store .Data => (pure false)
                  | .Store .Vector => (pure false)
                  | .StoreConditional (_, _, .Data) => (pure false)
                  | .Atomic (_, _, _, .Data, .Data) => (pure false)
                  | .Store .ShadowStack => (pure true)
                  | .Atomic (_, _, _, .ShadowStack, .ShadowStack) => (pure true)
                  | .CacheAccess _ => (pure false)
                  | .LoadExecute p =>
                    (internal_error "sys/vmem_pte.sail" 216
                      (HAppend.hAppend "Invalid payload ("
                        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadExecute.")))
                  | .LoadReserved (_, _, p) =>
                    (internal_error "sys/vmem_pte.sail" 217
                      (HAppend.hAppend "Invalid payload ("
                        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadReserved.")))
                  | .StoreConditional (_, _, p) =>
                    (internal_error "sys/vmem_pte.sail" 218
                      (HAppend.hAppend "Invalid payload ("
                        (HAppend.hAppend (mem_payload_name_forwards p) ") for StoreConditional.")))
                  | .Atomic (_, _, _, rp, wp) =>
                    (internal_error "sys/vmem_pte.sail" 219
                      (HAppend.hAppend "Invalid payloads ("
                        (HAppend.hAppend (mem_payload_name_forwards rp)
                          (HAppend.hAppend ", "
                            (HAppend.hAppend (mem_payload_name_forwards wp) ") for Atomic."))))) ) :
                  SailME PTE_Check Bool )
                if ((not shadow_stack_ok) : Bool)
                then (pure (PTE_Check_Failure ((), (PTE_No_Access ()))))
                else (pure (PTE_Check_Success ())))
          else
            (do
              if ((← (is_shadow_stack_access access)) : Bool)
              then
                SailME.throw (let is_read_only := (pte_R && ((not pte_W) && (not pte_X)))
                  (PTE_Check_Failure
                    ((), (if (is_read_only : Bool)
                    then (PTE_No_Permission ())
                    else (PTE_No_Access ())))) : PTE_Check)
              else (pure ())))
      let pte_R := (pte_R || (pte_X && mxr))
      let access_ok : Bool :=
        match access with
        | .Load _ => pte_R
        | .LoadReserved _ => pte_R
        | .Store _ => pte_W
        | .StoreConditional _ => pte_W
        | .Atomic _ => (pte_W && pte_R)
        | .InstructionFetch _ => pte_X
        | .LoadExecute _ => pte_X
        | .CacheAccess (.CB_zero ()) => pte_W
        | .CacheAccess (.CB_prefetch p) =>
          (match p with
          | .PREFETCH_R => pte_R
          | .PREFETCH_W => pte_W
          | .PREFETCH_I => pte_X)
        | .CacheAccess (.CB_manage _) => (pte_R || pte_W)
      if ((not access_ok) : Bool)
      then (pure (PTE_Check_Failure ((), (PTE_No_Permission ()))))
      else (pure (PTE_Check_Success ())))

/-- Type quantifiers: k_pte_size : Nat, k_pte_size ≥ 0, List.elem k_pte_size [32, 64] -/
def update_PTE_Bits (pte : (BitVec k_pte_size)) (access : (MemoryAccessType mem_payload)) : (Option (BitVec k_pte_size)) :=
  let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
  let update_d : Bool :=
    (((_get_PTE_Flags_D pte_flags) == 0#1) && (match access with
      | .InstructionFetch () => false
      | .LoadExecute _ => false
      | .Load _ => false
      | .LoadReserved _ => false
      | .Store _ => true
      | .StoreConditional _ => true
      | .Atomic _ => true
      | .CacheAccess (.CB_manage _) => false
      | .CacheAccess (.CB_zero ()) => true
      | .CacheAccess (.CB_prefetch _) => false : Bool))
  let update_a := (((_get_PTE_Flags_A pte_flags) == 0#1) && (not (is_prefetch_access access)))
  if ((update_d || update_a) : Bool)
  then
    (let pte_flags :=
      (_update_PTE_Flags_D (_update_PTE_Flags_A pte_flags 1#1)
        (if (update_d : Bool)
        then 1#1
        else (_get_PTE_Flags_D pte_flags)))
    (some (Sail.BitVec.updateSubrange pte 7 0 pte_flags)))
  else none

