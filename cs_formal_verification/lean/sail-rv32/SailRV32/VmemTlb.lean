import SailRV32.SailRV32
import SailRV32.Prelude
import SailRV32.Types
import SailRV32.VmemTypes
import SailRV32.VmemPte

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

def tlb_vpn_bits := (59 -i 12)

def tlb_ppn_bits := 44

/-- Type quantifiers: pte_size : Nat, pte_size ≥ 0, List.elem pte_size [4, 8] -/
def tlb_get_pte (pte_size : Nat) (ent : TLB_Entry) : (BitVec (pte_size * 8)) :=
  (Sail.BitVec.extractLsb ent.pte ((pte_size *i 8) -i 1) 0)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, List.elem k_n [4, 8] -/
def tlb_set_pte (ent : TLB_Entry) (pte : (BitVec (k_n * 8))) : TLB_Entry :=
  { ent with pte := (zero_extend (m := 64) pte) }

/-- Type quantifiers: sv_width : Nat, (is_sv_or_svx4_mode sv_width) -/
def tlb_get_ppn (sv_width : Nat) (ent : TLB_Entry) (vpn : (BitVec (sv_width - 12))) : (BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) :=
  let vpn : (BitVec 64) := (sign_extend (m := 64) vpn)
  let levelMask : (BitVec 64) := (zero_extend (m := 64) ent.levelMask)
  let ppn : (BitVec 64) := (zero_extend (m := 64) ent.ppn)
  (trunc
    (m := (if (((sv_width == 32) || (sv_width == 34)) : Bool)
    then 22
    else 44)) (ppn ||| (vpn &&& levelMask)))

def tlb_get_pbmt (ent : TLB_Entry) : SailM page_based_mem_type := do
  let pte_ext := (ext_bits_of_PTE ent.pte)
  (page_based_mem_type_forwards (_get_PTE_Ext_PBMT pte_ext))

def num_tlb_entries_exp := 6

/-- Type quantifiers: x_1 : Nat, 0 ≤ x_1 ∧ x_1 ≤ (2 ^ 6) -/
def tlb_add_callback (x_0 : (Vector (Option TLB_Entry) (2 ^ 6))) (x_1 : Nat) : Unit :=
  ()

def tlb_flush_begin_callback (x_0 : Unit) : Unit :=
  ()

/-- Type quantifiers: x_0 : Nat, 0 ≤ x_0 ∧ x_0 ≤ (2 ^ 6) -/
def tlb_flush_callback (x_0 : Nat) : Unit :=
  ()

def tlb_flush_end_callback (x_0 : (Vector (Option TLB_Entry) (2 ^ 6))) : Unit :=
  ()

/-- Type quantifiers: _sv_mode : Nat, (is_sv_or_svx4_mode _sv_mode) -/
def tlb_hash (_sv_mode : Nat) (vpn : (BitVec (_sv_mode - 12))) (stage : TranslationStage) : Nat :=
  let stage_bits : (BitVec num_tlb_entries_exp) :=
    match stage with
    | .S_Stage => (zero_extend (m := 6) 0b00#2)
    | .VS_Stage => (zero_extend (m := 6) 0b01#2)
    | .G_Stage => (zero_extend (m := 6) 0b10#2)
  (BitVec.toNatInt ((Sail.BitVec.extractLsb vpn (num_tlb_entries_exp -i 1) 0) ^^^ stage_bits))

def reset_TLB (_ : Unit) : SailM Unit := do
  writeReg tlb (vectorInit none)

/-- Type quantifiers: index : Nat, 0 ≤ index ∧ index ≤ (2 ^ 6 - 1) -/
def write_TLB (index : Nat) (entry : TLB_Entry) : SailM Unit := do
  writeReg tlb (vectorUpdate (← readReg tlb) index (some entry))

def match_TLB_Entry (ent : TLB_Entry) (asid : (BitVec (if ( 32 = 32  : Bool) then 9 else 16))) (vmid : (BitVec (if ( 32
  = 32  : Bool) then 7 else 14))) (vpn : (BitVec (59 - 12))) (stage : TranslationStage) : Bool :=
  let asid_matches := (ent.global || (ent.asid == asid))
  let vmid_matches := (ent.vmid == vmid)
  let vpn_matches := (ent.vpn == (vpn &&& (Complement.complement ent.levelMask)))
  let stage_matches := (ent.stage == stage)
  match stage with
  | .S_Stage => (asid_matches && (vpn_matches && stage_matches))
  | .VS_Stage => (asid_matches && (vmid_matches && (vpn_matches && stage_matches)))
  | .G_Stage => (vmid_matches && (vpn_matches && stage_matches))

def flush_TLB_Entry (ent : TLB_Entry) (asid : (Option (BitVec (if ( 32 = 32  : Bool) then 9 else 16)))) (vmid : (Option (BitVec (if ( 32
  = 32  : Bool) then 7 else 14)))) (vaddr : (Option (BitVec 32))) (stage : TranslationStage) : Bool :=
  let asid_matches : Bool :=
    match asid with
    | .some asid => ((ent.asid == asid) && (not ent.global))
    | none => true
  let vmid_matches : Bool :=
    match vmid with
    | .some vmid => (ent.vmid == vmid)
    | none => true
  let addr_matches : Bool :=
    match vaddr with
    | .some vaddr =>
      (let vaddr : (BitVec 64) :=
        match stage with
        | .G_Stage => ((zero_extend (m := 64) vaddr) <<< 2)
        | _ => (sign_extend (m := 64) vaddr)
      (ent.vpn == ((Sail.BitVec.extractLsb vaddr 58 pagesize_bits) &&& (Complement.complement
            ent.levelMask))))
    | none => true
  let stage_matches := (ent.stage == stage)
  (asid_matches && (vmid_matches && (addr_matches && stage_matches)))

/-- Type quantifiers: sv_width : Nat, (is_sv_or_svx4_mode sv_width) -/
def lookup_TLB (sv_width : Nat) (asid : (BitVec (if ( 32 = 32  : Bool) then 9 else 16))) (vmid : (BitVec (if ( 32
  = 32  : Bool) then 7 else 14))) (vpn : (BitVec (sv_width - 12))) (stage : TranslationStage) : SailM (Option (Nat × TLB_Entry)) := do
  let index := (tlb_hash sv_width vpn stage)
  match (GetElem?.getElem! (← readReg tlb) index) with
  | none => (pure none)
  | .some entry =>
    (let vpn : (BitVec tlb_vpn_bits) :=
      if ((stage == G_Stage) : Bool)
      then (zero_extend (m := (59 -i 12)) vpn)
      else (sign_extend (m := (59 -i 12)) vpn)
    if ((match_TLB_Entry entry asid vmid vpn stage) : Bool)
    then (pure (some (index, entry)))
    else (pure none))

/-- Type quantifiers: k_ex1822122_ : Bool, level : Nat, sv_width : Nat, (is_sv_or_svx4_mode sv_width), 0
  ≤ level ∧
  level ≤
  (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 1 else (if ( sv_width = 39 ∨ sv_width = 41  : Bool) then 2 else (if ( sv_width
  = 48 ∨ sv_width = 50  : Bool) then 3 else 4))) -/
def add_to_TLB (sv_width : Nat) (asid : (BitVec (if ( 32 = 32  : Bool) then 9 else 16))) (vmid : (BitVec (if ( 32
  = 32  : Bool) then 7 else 14))) (vpn : (BitVec (sv_width - 12))) (ppn : (BitVec (if ( sv_width =
  32 ∨ sv_width = 34  : Bool) then 22 else 44))) (pte : (BitVec (if ( sv_width = 32 ∨
  sv_width = 34  : Bool) then 32 else 64))) (pteAddr : physaddr) (level : Nat) (global : Bool) (stage : TranslationStage) : SailM Unit := do
  let shift := (level *i (get_vpn_level_size sv_width))
  let levelMask := (ones (n := shift))
  let index := (tlb_hash sv_width vpn stage)
  let vpn := (vpn &&& (Complement.complement (zero_extend (m := (sv_width -i 12)) levelMask)))
  let ppn :=
    (ppn &&& (Complement.complement
        (zero_extend
          (m := (if (((sv_width == 32) || (sv_width == 34)) : Bool)
          then 22
          else 44)) levelMask)))
  let entry : TLB_Entry :=
    { asid := asid
      vmid := vmid
      stage := stage
      global := global
      pte := (zero_extend (m := 64) pte)
      pteAddr := pteAddr
      levelMask := (zero_extend (m := (59 -i 12)) levelMask)
      vpn := if ((stage == G_Stage) : Bool)
        then (zero_extend (m := (59 -i 12)) vpn)
        else (sign_extend (m := (59 -i 12)) vpn)
      ppn := (zero_extend (m := 44) ppn) }
  writeReg tlb (vectorUpdate (← readReg tlb) index (some entry))
  (pure (tlb_add_callback (← readReg tlb) index))

def flush_TLB (asid : (Option (BitVec (if ( 32 = 32  : Bool) then 9 else 16)))) (vmid : (Option (BitVec (if ( 32
  = 32  : Bool) then 7 else 14)))) (addr : (Option (BitVec 32))) (stage : TranslationStage) : SailM Unit := do
  let _ : Unit := (tlb_flush_begin_callback ())
  let loop_i_lower := 0
  let loop_i_upper ← do (pure ((Vector.length (← readReg tlb)) -i 1))
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      match (GetElem?.getElem! (← readReg tlb) i) with
      | none => (pure ())
      | .some entry =>
        (do
          if ((flush_TLB_Entry entry asid vmid addr stage) : Bool)
          then
            (do
              writeReg tlb (vectorUpdate (← readReg tlb) i none)
              (pure (tlb_flush_callback i)))
          else (pure ()))
  (pure loop_vars)
  (pure (tlb_flush_end_callback (← readReg tlb)))

