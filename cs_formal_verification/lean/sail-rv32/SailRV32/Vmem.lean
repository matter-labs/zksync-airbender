import SailRV32.SailRV32
import SailRV32.Flow
import SailRV32.Prelude
import SailRV32.Errors
import SailRV32.IsaVersion
import SailRV32.Xlen
import SailRV32.MemAddrtype
import SailRV32.PlatformConfig
import SailRV32.TypesExt
import SailRV32.Types
import SailRV32.VmemTypes
import SailRV32.SysRegs
import SailRV32.Events
import SailRV32.SyncException
import SailRV32.Mem
import SailRV32.VmemPte
import SailRV32.VmemPtw
import SailRV32.Callbacks0
import SailRV32.VmemTlb

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

/-- Type quantifiers: pte_size : Nat, pte_size ≥ 0, List.elem pte_size [4, 8] -/
def write_pte (paddr : physaddr) (pte_size : Nat) (pte : (BitVec (pte_size * 8))) : SailM (Result Bool (physaddr × ExceptionType)) := do
  (mem_write_value paddr pte_size pte Supervisor (Store PageTableEntry) PBMT_PMA false false false)

/-- Type quantifiers: pte_size : Nat, pte_size ≥ 0, List.elem pte_size [4, 8] -/
def read_pte (paddr : physaddr) (pte_size : Nat) : SailM (Result (BitVec (8 * pte_size)) (physaddr × ExceptionType)) := do
  (mem_read (Load PageTableEntry) PBMT_PMA Supervisor paddr pte_size false false false)

def hgatp_mode (_ : Unit) : SailM HGATPMode := do
  let arch ← do (architecture Supervisor)
  let mbits ← (( do
    match arch with
    | .RV64 =>
      (do
        «assert» (xlen ≥b 64) "sys/vmem.sail:377.31-377.32"
        throw Error.Exit)
    | .RV32 =>
      (pure (0b000#3 +++ (_get_Hgatp32_Mode
            (Mk_Hgatp32 (Sail.BitVec.extractLsb (← readReg hgatp) 31 0)))))
    | .RV128 => (internal_error "sys/vmem.sail" 379 "RV128 not supported") ) : SailM
    SailRV32.hgatp_mode )
  match (← (hgatpMode_of_bits arch mbits)) with
  | .some m => (pure m)
  | none => (internal_error "sys/vmem.sail" 384 "invalid translation mode in hgatp")

def hgatp_mode_width_forwards (arg_ : HGATPMode) : SailM Int := do
  match arg_ with
  | .Sv32x4 => (pure 34)
  | .Sv39x4 => (pure 41)
  | .Sv48x4 => (pure 50)
  | .Sv57x4 => (pure 59)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def get_asid (stage : TranslationStage) : SailM (BitVec (if ( 32 = 32  : Bool) then 9 else 16)) := do
  match stage with
  | .S_Stage => (pure (_get_Satp32_Asid (Mk_Satp32 (← readReg satp))))
  | .VS_Stage => (pure (_get_Satp32_Asid (Mk_Satp32 (← readReg vsatp))))
  | .G_Stage => (pure (zeros (n := 9)))

def get_mxr (stage : TranslationStage) : SailM Bool := do
  if ((stage == VS_Stage) : Bool)
  then
    (pure (((_get_Mstatus_MXR (← readReg mstatus)) == 1#1) || ((_get_Mstatus_MXR
            (← readReg vsstatus)) == 1#1)))
  else (pure ((_get_Mstatus_MXR (← readReg mstatus)) == 1#1))

def get_sum (stage : TranslationStage) : SailM Bool := do
  if ((stage == VS_Stage) : Bool)
  then (pure ((_get_Mstatus_SUM (← readReg vsstatus)) == 1#1))
  else (pure ((_get_Mstatus_SUM (← readReg mstatus)) == 1#1))

def get_vmid (stage : TranslationStage) : SailM (BitVec (if ( 32 = 32  : Bool) then 7 else 14)) := do
  if ((stage == S_Stage) : Bool)
  then (pure (zeros (n := 7)))
  else (pure (_get_Hgatp32_VMID (Mk_Hgatp32 (← readReg hgatp))))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, sv_width : Nat, sv_width ≥ 0, (is_sv_or_svx4_mode
  sv_width) ∧ k_n ≥ sv_width -/
def translate_validate_address (addr : (BitVec k_n)) (sv_width : Nat) (stage : TranslationStage) : (Result (BitVec sv_width) PTW_Error) :=
  let truncated := (Sail.BitVec.truncate addr sv_width)
  let extended : (BitVec k_n) :=
    if ((stage == G_Stage) : Bool)
    then (zero_extend (m := (Sail.BitVec.length addr)) truncated)
    else (sign_extend (m := (Sail.BitVec.length addr)) truncated)
  if ((addr == extended) : Bool)
  then (Ok truncated)
  else (Err (PTW_Invalid_Addr ()))

def xatp_to_ppn (stage : TranslationStage) : SailM (BitVec (if ( 32 = 32  : Bool) then 22 else 44)) := do
  match stage with
  | .S_Stage => (pure (_get_Satp32_PPN (Mk_Satp32 (← readReg satp))))
  | .VS_Stage => (pure (_get_Satp32_PPN (Mk_Satp32 (← readReg vsatp))))
  | .G_Stage => (pure (_get_Hgatp32_PPN (Mk_Hgatp32 (← readReg hgatp))))

def translate_PTE_addr_mutrec_vv_zG_Stagev (pte_addr : (BitVec (if ( 32 = 32  : Bool) then 34 else 64))) (access : (MemoryAccessType mem_payload)) (ext_ptw : Unit) : (Result (physaddr × page_based_mem_type × Unit) (PTW_Error × Unit)) :=
  (Ok ((Physaddr pte_addr), PBMT_PMA, ext_ptw))

/-- Type quantifiers: pteWidth : Nat, pteWidth ≥ 0, List.elem pteWidth [4, 8] -/
def update_and_write_pte_mutrec_vvvv_zG_Stagev (pteAddr : physaddr) (pteWidth : Nat) (pte : (BitVec (pteWidth * 8))) (access : (MemoryAccessType mem_payload)) (ext_ptw : Unit) : SailM (Result (Option (BitVec (pteWidth * 8))) PTW_Error) := SailME.run do
  match (update_PTE_Bits pte access) with
  | none => (pure (Ok none))
  | .some pte =>
    (do
      if ((((← (currentlyEnabled Ext_Svadu)) && (← do
               (pure ((_get_MEnvcfg_ADUE (← readReg menvcfg)) == 1#1)))) || ((not
               (← (currentlyEnabled Ext_Svadu))) && (not (← (currentlyEnabled Ext_Svade))))) : Bool)
      then
        (do
          let write_paddr ← do
            match (translate_PTE_addr_mutrec_vv_zG_Stagev (bits_of_physaddr pteAddr)
              (Store PageTableEntry) ext_ptw) with
            | .Ok (pa, _, _) => (pure pa)
            | .Err (e, _) =>
              SailME.throw (← do
                  (pure (Err
                      (PTW_Implicit_Error
                        ((← (translationException access e)), (bits_of_physaddr pteAddr), (Store
                          PageTableEntry))))))
          match (← (write_pte write_paddr pteWidth pte)) with
          | .Ok _ => (pure (Ok (some pte)))
          | .Err _ => (pure (Err (PTW_No_Access ()))))
      else (pure (Err (PTW_PTE_Needs_Update ()))))

/-- Type quantifiers: k_ex821738_ : Bool, k_ex821739_ : Bool, tlb_index : Nat, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width), 0 ≤ tlb_index ∧ tlb_index ≤ (2 ^ 6 - 1) -/
def translate_TLB_hit_mutrec_vvvvv_zUservvvv_zG_Stagev (sv_width : Nat) (_asid : (BitVec (if ( 32 =
  32  : Bool) then 9 else 16))) (_vmid : (BitVec (if ( 32 = 32  : Bool) then 7 else 14))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (mxr : Bool) (do_sum : Bool) (tlb_index : Nat) (ent : TLB_Entry) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  let pte_size :=
    if (((sv_width == 32) || (sv_width == 34)) : Bool)
    then 4
    else 8
  let pte := (tlb_get_pte pte_size ent)
  let ext_pte := (ext_bits_of_PTE pte)
  let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
  let pte_check ← do
    (check_PTE_permission access User G_Stage mxr do_sum pte_flags ext_pte ext_ptw)
  match pte_check with
  | .PTE_Check_Failure (ext_ptw, pte_failure) =>
    (pure (Err ((ext_get_ptw_error pte_failure), ext_ptw)))
  | .PTE_Check_Success ext_ptw =>
    (do
      match (← (update_and_write_pte_mutrec_vvvv_zG_Stagev ent.pteAddr pte_size pte access ext_ptw)) with
      | .Ok (.some pte) =>
        (do
          (write_TLB tlb_index (tlb_set_pte ent pte))
          (pure (Ok ((tlb_get_ppn sv_width ent vpn), (← (tlb_get_pbmt ent)), ext_ptw))))
      | .Ok none => (pure (Ok ((tlb_get_ppn sv_width ent vpn), (← (tlb_get_pbmt ent)), ext_ptw)))
      | .Err (.PTW_PTE_Needs_Update ()) => (pure (Err ((PTW_PTE_Needs_Update ()), ext_ptw)))
      | .Err e => (pure (Err (e, ext_ptw))))

/-- Type quantifiers: k_ex821728_ : Bool, k_ex821729_ : Bool, level : Nat, k_ex821731_ : Bool, sv_width
  : Nat, (is_sv_or_svx4_mode sv_width), 0 ≤ level ∧
  level ≤
  (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 1 else (if ( sv_width = 39 ∨ sv_width = 41  : Bool) then 2 else (if ( sv_width
  = 48 ∨ sv_width = 50  : Bool) then 3 else 4))) -/
def pt_walk_mutrec_vvv_zUservvvvv_zG_Stagev (sv_width : Nat) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (mxr : Bool) (do_sum : Bool) (pt_base : (BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (level : Nat) (global : Bool) (ext_ptw : Unit) : SailM (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)) := SailME.run do
  let _ : Unit := (ptw_start_callback G_Stage level (zero_extend (m := 64) vpn) access User)
  let log_pte_size_bytes :=
    if (((sv_width == 32) || (sv_width == 34)) : Bool)
    then 2
    else 3
  let vpn_i_size := (pagesize_bits -i log_pte_size_bytes)
  let is_svx4_root :=
    (((sv_width == 34) || ((sv_width == 41) || ((sv_width == 50) || (sv_width == 59)))) && (level == (get_root_level
          sv_width)))
  let vpn_lo := (level *i vpn_i_size)
  let vpn_hi :=
    if (is_svx4_root : Bool)
    then (((level +i 1) *i vpn_i_size) +i 1)
    else (((level +i 1) *i vpn_i_size) -i 1)
  let pte_addr :=
    ((pt_base +++ 0x000#12) + (zero_extend
        (m := ((if (((sv_width == 32) || (sv_width == 34)) : Bool)
          then 22
          else 44) +i 12))
        ((Sail.BitVec.extractLsb vpn vpn_hi vpn_lo) +++ (zeros (n := log_pte_size_bytes)))))
  «assert» ((sv_width == 32) || ((sv_width == 34) || false)) "sys/vmem.sail:176.41-176.42"
  let pte_addr_original := (Physaddr (zero_extend (m := 34) pte_addr))
  let pte_addr ← do
    match (translate_PTE_addr_mutrec_vv_zG_Stagev (zero_extend (m := 34) pte_addr)
      (Load PageTableEntry) ext_ptw) with
    | .Ok (pa, _, _) => (pure pa)
    | .Err (e, _) =>
      SailME.throw (← do
          (pure (Err
              ((PTW_Implicit_Error
                ((← (translationException access e)), (zero_extend (m := 34) pte_addr), (Load
                  PageTableEntry))), ext_ptw))))
  match (← (read_pte pte_addr (2 ^i log_pte_size_bytes))) with
  | .Err _ =>
    (let _ : Unit :=
      (ptw_fail_callback G_Stage level (PTW_No_Access ()) (bits_of_physaddr pte_addr))
    (pure (Err ((PTW_No_Access ()), ext_ptw))))
  | .Ok pte =>
    (do
      let _ : Unit :=
        (ptw_step_callback G_Stage level (bits_of_physaddr pte_addr) (zero_extend (m := 64) pte))
      let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
      let pte_ext := (ext_bits_of_PTE pte)
      if ((← (pte_is_invalid pte_flags pte_ext G_Stage)) : Bool)
      then
        (let _ : Unit :=
          (ptw_fail_callback G_Stage level (PTW_Invalid_PTE ()) (bits_of_physaddr pte_addr))
        (pure (Err ((PTW_Invalid_PTE ()), ext_ptw))))
      else
        (do
          let ppn := (PPN_of_PTE pte)
          let global := (global || ((bne G_Stage G_Stage) && ((_get_PTE_Flags_G pte_flags) == 1#1)))
          if ((pte_is_non_leaf pte_flags) : Bool)
          then
            (do
              if ((level >b 0) : Bool)
              then
                (pt_walk_mutrec_vvv_zUservvvvv_zG_Stagev sv_width vpn access mxr do_sum ppn
                  (level -i 1) global ext_ptw)
              else
                (let _ : Unit :=
                  (ptw_fail_callback G_Stage level (PTW_Invalid_PTE ()) (bits_of_physaddr pte_addr))
                (pure (Err ((PTW_Invalid_PTE ()), ext_ptw)))))
          else
            (do
              let low_bits := (vpn_i_size *i level)
              if ((level >b 0) : Bool)
              then
                (do
                  if (((Sail.BitVec.extractLsb ppn (low_bits -i 1) 0) != (zeros
                         (n := ((((vpn_i_size *i level) -i 1) -i 0) +i 1)))) : Bool)
                  then
                    SailME.throw (let _ : Unit :=
                        (ptw_fail_callback G_Stage level (PTW_Misaligned ())
                          (bits_of_physaddr pte_addr))
                      (Err ((PTW_Misaligned ()), ext_ptw)) : (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)))
                  else (pure ()))
              else (pure ())
              match (← (check_PTE_permission access User G_Stage mxr do_sum pte_flags pte_ext
                  ext_ptw)) with
              | .PTE_Check_Failure (ext_ptw, pte_failure) =>
                (let _ : Unit :=
                  (ptw_fail_callback G_Stage level (ext_get_ptw_error pte_failure)
                    (bits_of_physaddr pte_addr))
                (pure (Err ((ext_get_ptw_error pte_failure), ext_ptw))))
              | .PTE_Check_Success ext_ptw =>
                (do
                  let ppn ← do
                    if ((level >b 0) : Bool)
                    then
                      (do
                        if ((((_get_PTE_Ext_N pte_ext) == 1#1) && pte_reserved_bits_must_be_zero) : Bool)
                        then
                          SailME.throw ((Err ((PTW_Invalid_PTE ()), ext_ptw)) : (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)))
                        else
                          (pure ((Sail.BitVec.extractLsb ppn ((Sail.BitVec.length ppn) -i 1)
                                low_bits) +++ (Sail.BitVec.extractLsb vpn (low_bits -i 1) 0))))
                    else
                      (do
                        if (((← (currentlyEnabled Ext_Svnapot)) && ((_get_PTE_Ext_N pte_ext) == 1#1)) : Bool)
                        then
                          (do
                            if (((Sail.BitVec.extractLsb ppn 3 0) != 0b1000#4) : Bool)
                            then
                              SailME.throw ((Err ((PTW_Invalid_PTE ()), ext_ptw)) : (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)))
                            else
                              (pure (Sail.BitVec.updateSubrange ppn 3 0
                                  (Sail.BitVec.extractLsb vpn 3 0))))
                        else (pure ppn))
                  let pbmt ← do
                    if ((((_get_MEnvcfg_PBMTE (← readReg menvcfg)) == 0#1) || false) : Bool)
                    then (pure PBMT_PMA)
                    else (page_based_mem_type_forwards (_get_PTE_Ext_PBMT pte_ext))
                  let _ : Unit := (ptw_success_callback G_Stage level (zero_extend (m := 64) ppn))
                  (pure (Ok
                      ({ ppn := ppn
                         pte := pte
                         pteAddr := pte_addr_original
                         level := level
                         pbmt := pbmt
                         global := global }, ext_ptw)))))))
termination_by (let (_, _, _, _, _, _, level, _, _) :=
  (sv_width, vpn, access, mxr, do_sum, pt_base, level, global, ext_ptw)
level).toNat

/-- Type quantifiers: k_ex821728_ : Bool, k_ex821729_ : Bool, level : Nat, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width), 0 ≤ level ∧
  level ≤
  (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 1 else (if ( sv_width = 39 ∨ sv_width = 41  : Bool) then 2 else (if ( sv_width
  = 48 ∨ sv_width = 50  : Bool) then 3 else 4))) -/
def pt_walk_mutrec_vvv_zUservvvvF_zG_Stagev (sv_width : Nat) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (mxr : Bool) (do_sum : Bool) (pt_base : (BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (level : Nat) (ext_ptw : Unit) : SailM (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)) := SailME.run do
  let _ : Unit := (ptw_start_callback G_Stage level (zero_extend (m := 64) vpn) access User)
  let log_pte_size_bytes :=
    if (((sv_width == 32) || (sv_width == 34)) : Bool)
    then 2
    else 3
  let vpn_i_size := (pagesize_bits -i log_pte_size_bytes)
  let is_svx4_root :=
    (((sv_width == 34) || ((sv_width == 41) || ((sv_width == 50) || (sv_width == 59)))) && (level == (get_root_level
          sv_width)))
  let vpn_lo := (level *i vpn_i_size)
  let vpn_hi :=
    if (is_svx4_root : Bool)
    then (((level +i 1) *i vpn_i_size) +i 1)
    else (((level +i 1) *i vpn_i_size) -i 1)
  let pte_addr :=
    ((pt_base +++ 0x000#12) + (zero_extend
        (m := ((if (((sv_width == 32) || (sv_width == 34)) : Bool)
          then 22
          else 44) +i 12))
        ((Sail.BitVec.extractLsb vpn vpn_hi vpn_lo) +++ (zeros (n := log_pte_size_bytes)))))
  «assert» ((sv_width == 32) || ((sv_width == 34) || false)) "sys/vmem.sail:176.41-176.42"
  let pte_addr_original := (Physaddr (zero_extend (m := 34) pte_addr))
  let pte_addr ← do
    match (translate_PTE_addr_mutrec_vv_zG_Stagev (zero_extend (m := 34) pte_addr)
      (Load PageTableEntry) ext_ptw) with
    | .Ok (pa, _, _) => (pure pa)
    | .Err (e, _) =>
      SailME.throw (← do
          (pure (Err
              ((PTW_Implicit_Error
                ((← (translationException access e)), (zero_extend (m := 34) pte_addr), (Load
                  PageTableEntry))), ext_ptw))))
  match (← (read_pte pte_addr (2 ^i log_pte_size_bytes))) with
  | .Err _ =>
    (let _ : Unit :=
      (ptw_fail_callback G_Stage level (PTW_No_Access ()) (bits_of_physaddr pte_addr))
    (pure (Err ((PTW_No_Access ()), ext_ptw))))
  | .Ok pte =>
    (do
      let _ : Unit :=
        (ptw_step_callback G_Stage level (bits_of_physaddr pte_addr) (zero_extend (m := 64) pte))
      let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
      let pte_ext := (ext_bits_of_PTE pte)
      if ((← (pte_is_invalid pte_flags pte_ext G_Stage)) : Bool)
      then
        (let _ : Unit :=
          (ptw_fail_callback G_Stage level (PTW_Invalid_PTE ()) (bits_of_physaddr pte_addr))
        (pure (Err ((PTW_Invalid_PTE ()), ext_ptw))))
      else
        (do
          let ppn := (PPN_of_PTE pte)
          let global := (false || ((bne G_Stage G_Stage) && ((_get_PTE_Flags_G pte_flags) == 1#1)))
          if ((pte_is_non_leaf pte_flags) : Bool)
          then
            (do
              if ((level >b 0) : Bool)
              then
                (pt_walk_mutrec_vvv_zUservvvvv_zG_Stagev sv_width vpn access mxr do_sum ppn
                  (level -i 1) global ext_ptw)
              else
                (let _ : Unit :=
                  (ptw_fail_callback G_Stage level (PTW_Invalid_PTE ()) (bits_of_physaddr pte_addr))
                (pure (Err ((PTW_Invalid_PTE ()), ext_ptw)))))
          else
            (do
              let low_bits := (vpn_i_size *i level)
              if ((level >b 0) : Bool)
              then
                (do
                  if (((Sail.BitVec.extractLsb ppn (low_bits -i 1) 0) != (zeros
                         (n := ((((vpn_i_size *i level) -i 1) -i 0) +i 1)))) : Bool)
                  then
                    SailME.throw (let _ : Unit :=
                        (ptw_fail_callback G_Stage level (PTW_Misaligned ())
                          (bits_of_physaddr pte_addr))
                      (Err ((PTW_Misaligned ()), ext_ptw)) : (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)))
                  else (pure ()))
              else (pure ())
              match (← (check_PTE_permission access User G_Stage mxr do_sum pte_flags pte_ext
                  ext_ptw)) with
              | .PTE_Check_Failure (ext_ptw, pte_failure) =>
                (let _ : Unit :=
                  (ptw_fail_callback G_Stage level (ext_get_ptw_error pte_failure)
                    (bits_of_physaddr pte_addr))
                (pure (Err ((ext_get_ptw_error pte_failure), ext_ptw))))
              | .PTE_Check_Success ext_ptw =>
                (do
                  let ppn ← do
                    if ((level >b 0) : Bool)
                    then
                      (do
                        if ((((_get_PTE_Ext_N pte_ext) == 1#1) && pte_reserved_bits_must_be_zero) : Bool)
                        then
                          SailME.throw ((Err ((PTW_Invalid_PTE ()), ext_ptw)) : (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)))
                        else
                          (pure ((Sail.BitVec.extractLsb ppn ((Sail.BitVec.length ppn) -i 1)
                                low_bits) +++ (Sail.BitVec.extractLsb vpn (low_bits -i 1) 0))))
                    else
                      (do
                        if (((← (currentlyEnabled Ext_Svnapot)) && ((_get_PTE_Ext_N pte_ext) == 1#1)) : Bool)
                        then
                          (do
                            if (((Sail.BitVec.extractLsb ppn 3 0) != 0b1000#4) : Bool)
                            then
                              SailME.throw ((Err ((PTW_Invalid_PTE ()), ext_ptw)) : (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)))
                            else
                              (pure (Sail.BitVec.updateSubrange ppn 3 0
                                  (Sail.BitVec.extractLsb vpn 3 0))))
                        else (pure ppn))
                  let pbmt ← do
                    if ((((_get_MEnvcfg_PBMTE (← readReg menvcfg)) == 0#1) || false) : Bool)
                    then (pure PBMT_PMA)
                    else (page_based_mem_type_forwards (_get_PTE_Ext_PBMT pte_ext))
                  let _ : Unit := (ptw_success_callback G_Stage level (zero_extend (m := 64) ppn))
                  (pure (Ok
                      ({ ppn := ppn
                         pte := pte
                         pteAddr := pte_addr_original
                         level := level
                         pbmt := pbmt
                         global := global }, ext_ptw)))))))
termination_by (let (_, _, _, _, _, _, level, _) :=
  (sv_width, vpn, access, mxr, do_sum, pt_base, level, ext_ptw)
level).toNat

/-- Type quantifiers: k_ex821746_ : Bool, k_ex821747_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width) -/
def translate_TLB_miss_mutrec_vvvvvv_zUservv_zG_Stagev (sv_width : Nat) (asid : (BitVec (if ( 32 =
  32  : Bool) then 9 else 16))) (vmid : (BitVec (if ( 32 = 32  : Bool) then 7 else 14))) (base_ppn : (BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  let initial_level := (get_root_level sv_width)
  let pte_size :=
    if (((sv_width == 32) || (sv_width == 34)) : Bool)
    then 4
    else 8
  let ptw_result ← do
    (pt_walk_mutrec_vvv_zUservvvvF_zG_Stagev sv_width vpn access mxr do_sum base_ppn initial_level
      ext_ptw)
  match ptw_result with
  | .Err (f, ext_ptw) => (pure (Err (f, ext_ptw)))
  | .Ok ({ ppn := ppn, pte := pte, pteAddr := pteAddr, level := level, pbmt := pbmt, global := global }, ext_ptw) =>
    (do
      let ext_pte := (ext_bits_of_PTE pte)
      match (← (update_and_write_pte_mutrec_vvvv_zG_Stagev pteAddr pte_size pte access ext_ptw)) with
      | .Ok (.some new_pte) =>
        (do
          (add_to_TLB sv_width asid vmid vpn ppn new_pte pteAddr level global G_Stage)
          (pure (Ok (ppn, pbmt, ext_ptw))))
      | .Ok none =>
        (do
          (add_to_TLB sv_width asid vmid vpn ppn pte pteAddr level global G_Stage)
          (pure (Ok (ppn, pbmt, ext_ptw))))
      | .Err e => (pure (Err (e, ext_ptw))))

/-- Type quantifiers: k_ex821757_ : Bool, k_ex821758_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width) -/
def translate_mutrec_vvvvvv_zUservv_zG_Stagev (sv_width : Nat) (asid : (BitVec (if ( 32 = 32  : Bool) then 9 else 16))) (vmid : (BitVec (if ( 32
  = 32  : Bool) then 7 else 14))) (base_ppn : (BitVec (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  match (← (lookup_TLB sv_width asid vmid vpn G_Stage)) with
  | .some (index, ent) =>
    (translate_TLB_hit_mutrec_vvvvv_zUservvvv_zG_Stagev sv_width asid vmid vpn access mxr do_sum
      index ent ext_ptw)
  | none =>
    (do
      (generate_event EV_TLB_MISS)
      (translate_TLB_miss_mutrec_vvvvvv_zUservv_zG_Stagev sv_width asid vmid base_ppn vpn access mxr
        do_sum ext_ptw))

/-- Type quantifiers: k_n : Nat, sv_width : Nat, k_n ≥ 0, (is_sv_or_svx4_mode sv_width) ∧
  k_n ≥ sv_width -/
def translate_stage_mutrec_vvv_zUser_zG_Stage (sv_width : Nat) (addr : (BitVec k_n)) (access : (MemoryAccessType mem_payload)) : SailM (Result ((BitVec (if ( 32
  = 32  : Bool) then 34 else 64)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  match (translate_validate_address addr sv_width G_Stage) with
  | .Err e => (pure (Err (e, init_ext_ptw)))
  | .Ok valid_addr =>
    (do
      «assert» ((true && ((sv_width == 32) || (sv_width == 34))) || false) "sys/vmem.sail:545.60-545.61"
      let vmid ← do (get_vmid G_Stage)
      let mxr ← do (get_mxr G_Stage)
      let do_sum ← do (get_sum G_Stage)
      let vpn := (Sail.BitVec.extractLsb valid_addr (sv_width -i 1) pagesize_bits)
      let base_ppn ← do (xatp_to_ppn G_Stage)
      let res ← do
        (translate_mutrec_vvvvvv_zUservv_zG_Stagev sv_width 0b000000000#9 vmid base_ppn vpn access
          mxr do_sum init_ext_ptw)
      match res with
      | .Ok (ppn, pbmt, ext_ptw) =>
        (pure (Ok
            ((zero_extend (m := 34) (ppn +++ (Sail.BitVec.extractLsb valid_addr 11 0))), pbmt, ext_ptw)))
      | .Err (f, ext_ptw) => (pure (Err (f, ext_ptw))))

def translate_g_stage (gpa : (BitVec (if ( 32 = 32  : Bool) then 34 else 64))) (access : (MemoryAccessType mem_payload)) : SailM (Result ((BitVec (if ( 32
  = 32  : Bool) then 34 else 64)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  let mode ← do (hgatp_mode ())
  if ((mode == HBare) : Bool)
  then (pure (Ok (gpa, PBMT_PMA, init_ext_ptw)))
  else
    (do
      let sv_width ← do (hgatp_mode_width_forwards mode)
      «assert» (sv_width ≤b gpalen) "sys/vmem.sail:591.27-591.28"
      (translate_stage_mutrec_vvv_zUser_zG_Stage sv_width gpa access))

def translate_PTE_addr (pte_addr : (BitVec (if ( 32 = 32  : Bool) then 34 else 64))) (access : (MemoryAccessType mem_payload)) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result (physaddr × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  if ((stage == VS_Stage) : Bool)
  then
    (do
      match (← (translate_g_stage pte_addr access)) with
      | .Ok (pa, pbmt, ext_ptw) => (pure (Ok ((Physaddr pa), pbmt, ext_ptw)))
      | .Err (f, ext_ptw) => (pure (Err (f, ext_ptw))))
  else (pure (Ok ((Physaddr pte_addr), PBMT_PMA, ext_ptw)))

/-- Type quantifiers: k_ex1822184_ : Bool, level : Nat, k_ex1822182_ : Bool, k_ex1822181_ : Bool, sv_width
  : Nat, (is_sv_or_svx4_mode sv_width), 0 ≤ level ∧
  level ≤
  (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 1 else (if ( sv_width = 39 ∨ sv_width = 41  : Bool) then 2 else (if ( sv_width
  = 48 ∨ sv_width = 50  : Bool) then 3 else 4))) -/
def pt_walk (sv_width : Nat) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (pt_base : (BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (level : Nat) (global : Bool) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)) := SailME.run do
  let _ : Unit := (ptw_start_callback stage level (zero_extend (m := 64) vpn) access priv)
  let log_pte_size_bytes :=
    if (((sv_width == 32) || (sv_width == 34)) : Bool)
    then 2
    else 3
  let vpn_i_size := (pagesize_bits -i log_pte_size_bytes)
  let is_svx4_root :=
    (((sv_width == 34) || ((sv_width == 41) || ((sv_width == 50) || (sv_width == 59)))) && (level == (get_root_level
          sv_width)))
  let vpn_lo := (level *i vpn_i_size)
  let vpn_hi :=
    if (is_svx4_root : Bool)
    then (((level +i 1) *i vpn_i_size) +i 1)
    else (((level +i 1) *i vpn_i_size) -i 1)
  let pte_addr :=
    ((pt_base +++ (zeros (n := pagesize_bits))) + (zero_extend
        (m := ((if (((sv_width == 32) || (sv_width == 34)) : Bool)
          then 22
          else 44) +i 12))
        ((Sail.BitVec.extractLsb vpn vpn_hi vpn_lo) +++ (zeros (n := log_pte_size_bytes)))))
  «assert» ((sv_width == 32) || ((sv_width == 34) || (xlen == 64))) "sys/vmem.sail:176.41-176.42"
  let pte_addr_original := (Physaddr (zero_extend (m := 34) pte_addr))
  let pte_addr ← (( do
    match (← (translate_PTE_addr (zero_extend (m := 34) pte_addr) (Load PageTableEntry) stage
        ext_ptw)) with
    | .Ok (pa, _, _) => (pure pa)
    | .Err (e, _) =>
      SailME.throw (← do
          (pure (Err
              ((PTW_Implicit_Error
                ((← (translationException access e)), (zero_extend (m := 34) pte_addr), (Load
                  PageTableEntry))), ext_ptw)))) ) : SailME
    (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)) physaddr )
  match (← (read_pte pte_addr (2 ^i log_pte_size_bytes))) with
  | .Err _ =>
    (let _ : Unit := (ptw_fail_callback stage level (PTW_No_Access ()) (bits_of_physaddr pte_addr))
    (pure (Err ((PTW_No_Access ()), ext_ptw))))
  | .Ok pte =>
    (do
      let _ : Unit :=
        (ptw_step_callback stage level (bits_of_physaddr pte_addr) (zero_extend (m := 64) pte))
      let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
      let pte_ext := (ext_bits_of_PTE pte)
      if ((← (pte_is_invalid pte_flags pte_ext stage)) : Bool)
      then
        (let _ : Unit :=
          (ptw_fail_callback stage level (PTW_Invalid_PTE ()) (bits_of_physaddr pte_addr))
        (pure (Err ((PTW_Invalid_PTE ()), ext_ptw))))
      else
        (do
          let ppn := (PPN_of_PTE pte)
          let global := (global || ((bne stage G_Stage) && ((_get_PTE_Flags_G pte_flags) == 1#1)))
          if ((pte_is_non_leaf pte_flags) : Bool)
          then
            (do
              if ((level >b 0) : Bool)
              then
                (pt_walk sv_width vpn access priv mxr do_sum ppn (level -i 1) global stage ext_ptw)
              else
                (let _ : Unit :=
                  (ptw_fail_callback stage level (PTW_Invalid_PTE ()) (bits_of_physaddr pte_addr))
                (pure (Err ((PTW_Invalid_PTE ()), ext_ptw)))))
          else
            (do
              let low_bits := (vpn_i_size *i level)
              if ((level >b 0) : Bool)
              then
                (do
                  if (((Sail.BitVec.extractLsb ppn (low_bits -i 1) 0) != (zeros
                         (n := ((((vpn_i_size *i level) -i 1) -i 0) +i 1)))) : Bool)
                  then
                    SailME.throw (let _ : Unit :=
                        (ptw_fail_callback stage level (PTW_Misaligned ())
                          (bits_of_physaddr pte_addr))
                      (Err ((PTW_Misaligned ()), ext_ptw)) : (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)))
                  else (pure ()))
              else (pure ())
              match (← (check_PTE_permission access priv stage mxr do_sum pte_flags pte_ext
                  ext_ptw)) with
              | .PTE_Check_Failure (ext_ptw, pte_failure) =>
                (let _ : Unit :=
                  (ptw_fail_callback stage level (ext_get_ptw_error pte_failure)
                    (bits_of_physaddr pte_addr))
                (pure (Err ((ext_get_ptw_error pte_failure), ext_ptw))))
              | .PTE_Check_Success ext_ptw =>
                (do
                  let ppn ← do
                    if ((level >b 0) : Bool)
                    then
                      (do
                        if ((((_get_PTE_Ext_N pte_ext) == 1#1) && pte_reserved_bits_must_be_zero) : Bool)
                        then
                          SailME.throw ((Err ((PTW_Invalid_PTE ()), ext_ptw)) : (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)))
                        else
                          (pure ((Sail.BitVec.extractLsb ppn ((Sail.BitVec.length ppn) -i 1)
                                low_bits) +++ (Sail.BitVec.extractLsb vpn (low_bits -i 1) 0))))
                    else
                      (do
                        if (((← (currentlyEnabled Ext_Svnapot)) && ((_get_PTE_Ext_N pte_ext) == 1#1)) : Bool)
                        then
                          (do
                            let pte_napot_bits := 4
                            if (((Sail.BitVec.extractLsb ppn (pte_napot_bits -i 1) 0) != 0b1000#4) : Bool)
                            then
                              SailME.throw ((Err ((PTW_Invalid_PTE ()), ext_ptw)) : (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)))
                            else
                              (pure (Sail.BitVec.updateSubrange ppn (pte_napot_bits -i 1) 0
                                  (Sail.BitVec.extractLsb vpn (pte_napot_bits -i 1) 0))))
                        else (pure ppn))
                  let pbmt ← do
                    if ((((_get_MEnvcfg_PBMTE (← readReg menvcfg)) == 0#1) || ((stage == VS_Stage) && ((_get_HEnvcfg_PBMTE
                               (← (read_henvcfg ()))) == 0#1))) : Bool)
                    then (pure PBMT_PMA)
                    else (page_based_mem_type_forwards (_get_PTE_Ext_PBMT pte_ext))
                  let _ : Unit := (ptw_success_callback stage level (zero_extend (m := 64) ppn))
                  (pure (Ok
                      ({ ppn := ppn
                         pte := pte
                         pteAddr := pte_addr_original
                         level := level
                         pbmt := pbmt
                         global := global }, ext_ptw)))))))
termination_by (let (_, _, _, _, _, _, _, level, _, _, _) :=
  (sv_width, vpn, access, priv, mxr, do_sum, pt_base, level, global, stage, ext_ptw)
level).toNat

/-- Type quantifiers: pteWidth : Nat, pteWidth ≥ 0, List.elem pteWidth [4, 8] -/
def update_and_write_pte (pteAddr : physaddr) (pteWidth : Nat) (pte : (BitVec (pteWidth * 8))) (access : (MemoryAccessType mem_payload)) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result (Option (BitVec (pteWidth * 8))) PTW_Error) := SailME.run do
  match (update_PTE_Bits pte access) with
  | none => (pure (Ok none))
  | .some pte =>
    (do
      if ((((← (currentlyEnabled Ext_Svadu)) && (← do
               match stage with
               | .VS_Stage => (pure ((_get_HEnvcfg_ADUE (← (read_henvcfg ()))) == 1#1))
               | _ => (pure ((_get_MEnvcfg_ADUE (← readReg menvcfg)) == 1#1)))) || ((not
               (← (currentlyEnabled Ext_Svadu))) && (not (← (currentlyEnabled Ext_Svade))))) : Bool)
      then
        (do
          let write_paddr ← (( do
            match (← (translate_PTE_addr (bits_of_physaddr pteAddr) (Store PageTableEntry) stage
                ext_ptw)) with
            | .Ok (pa, _, _) => (pure pa)
            | .Err (e, _) =>
              SailME.throw (← do
                  (pure (Err
                      (PTW_Implicit_Error
                        ((← (translationException access e)), (bits_of_physaddr pteAddr), (Store
                          PageTableEntry)))))) ) : SailME
            (Result (Option (BitVec (pteWidth * 8))) PTW_Error) physaddr )
          match (← (write_pte write_paddr pteWidth pte)) with
          | .Ok _ => (pure (Ok (some pte)))
          | .Err _ => (pure (Err (PTW_No_Access ()))))
      else (pure (Err (PTW_PTE_Needs_Update ()))))

/-- Type quantifiers: tlb_index : Nat, k_ex1822192_ : Bool, k_ex1822191_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width), 0 ≤ tlb_index ∧ tlb_index ≤ (2 ^ 6 - 1) -/
def translate_TLB_hit (sv_width : Nat) (_asid : (BitVec (if ( 32 = 32  : Bool) then 9 else 16))) (_vmid : (BitVec (if ( 32
  = 32  : Bool) then 7 else 14))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (tlb_index : Nat) (ent : TLB_Entry) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  let pte_size :=
    if (((sv_width == 32) || (sv_width == 34)) : Bool)
    then 4
    else 8
  let pte := (tlb_get_pte pte_size ent)
  let ext_pte := (ext_bits_of_PTE pte)
  let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
  let pte_check ← do (check_PTE_permission access priv stage mxr do_sum pte_flags ext_pte ext_ptw)
  match pte_check with
  | .PTE_Check_Failure (ext_ptw, pte_failure) =>
    (pure (Err ((ext_get_ptw_error pte_failure), ext_ptw)))
  | .PTE_Check_Success ext_ptw =>
    (do
      match (← (update_and_write_pte ent.pteAddr pte_size pte access stage ext_ptw)) with
      | .Ok (.some pte) =>
        (do
          (write_TLB tlb_index (tlb_set_pte ent pte))
          (pure (Ok ((tlb_get_ppn sv_width ent vpn), (← (tlb_get_pbmt ent)), ext_ptw))))
      | .Ok none => (pure (Ok ((tlb_get_ppn sv_width ent vpn), (← (tlb_get_pbmt ent)), ext_ptw)))
      | .Err (.PTW_PTE_Needs_Update ()) => (pure (Err ((PTW_PTE_Needs_Update ()), ext_ptw)))
      | .Err e => (pure (Err (e, ext_ptw))))

/-- Type quantifiers: k_ex1822200_ : Bool, k_ex1822199_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width) -/
def translate_TLB_miss (sv_width : Nat) (asid : (BitVec (if ( 32 = 32  : Bool) then 9 else 16))) (vmid : (BitVec (if ( 32
  = 32  : Bool) then 7 else 14))) (base_ppn : (BitVec (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  let initial_level := (get_root_level sv_width)
  let pte_size :=
    if (((sv_width == 32) || (sv_width == 34)) : Bool)
    then 4
    else 8
  let ptw_result ← do
    (pt_walk sv_width vpn access priv mxr do_sum base_ppn initial_level false stage ext_ptw)
  match ptw_result with
  | .Err (f, ext_ptw) => (pure (Err (f, ext_ptw)))
  | .Ok ({ ppn := ppn, pte := pte, pteAddr := pteAddr, level := level, pbmt := pbmt, global := global }, ext_ptw) =>
    (do
      let ext_pte := (ext_bits_of_PTE pte)
      match (← (update_and_write_pte pteAddr pte_size pte access stage ext_ptw)) with
      | .Ok (.some new_pte) =>
        (do
          (add_to_TLB sv_width asid vmid vpn ppn new_pte pteAddr level global stage)
          (pure (Ok (ppn, pbmt, ext_ptw))))
      | .Ok none =>
        (do
          (add_to_TLB sv_width asid vmid vpn ppn pte pteAddr level global stage)
          (pure (Ok (ppn, pbmt, ext_ptw))))
      | .Err e => (pure (Err (e, ext_ptw))))

/-- Type quantifiers: k_ex1822207_ : Bool, k_ex1822206_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width) -/
def translate (sv_width : Nat) (asid : (BitVec (if ( 32 = 32  : Bool) then 9 else 16))) (vmid : (BitVec (if ( 32
  = 32  : Bool) then 7 else 14))) (base_ppn : (BitVec (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  match (← (lookup_TLB sv_width asid vmid vpn stage)) with
  | .some (index, ent) =>
    (translate_TLB_hit sv_width asid vmid vpn access priv mxr do_sum index ent stage ext_ptw)
  | none =>
    (do
      (generate_event EV_TLB_MISS)
      (translate_TLB_miss sv_width asid vmid base_ppn vpn access priv mxr do_sum stage ext_ptw))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, sv_width : Nat, (is_sv_or_svx4_mode sv_width) ∧
  k_n ≥ sv_width -/
def translate_stage (sv_width : Nat) (addr : (BitVec k_n)) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (stage : TranslationStage) : SailM (Result ((BitVec (if ( 32
  = 32  : Bool) then 34 else 64)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  match (translate_validate_address addr sv_width stage) with
  | .Err e => (pure (Err (e, init_ext_ptw)))
  | .Ok valid_addr =>
    (do
      «assert» (((xlen == 32) && ((sv_width == 32) || (sv_width == 34))) || ((xlen == 64) && ((sv_width != 32) && (sv_width != 34)))) "sys/vmem.sail:545.60-545.61"
      let asid ← do (get_asid stage)
      let vmid ← do (get_vmid stage)
      let mxr ← do (get_mxr stage)
      let do_sum ← do (get_sum stage)
      let vpn := (Sail.BitVec.extractLsb valid_addr (sv_width -i 1) pagesize_bits)
      let base_ppn ← do (xatp_to_ppn stage)
      let eff_priv :=
        if ((stage == G_Stage) : Bool)
        then User
        else priv
      let res ← do
        (translate sv_width asid vmid base_ppn vpn access eff_priv mxr do_sum stage init_ext_ptw)
      match res with
      | .Ok (ppn, pbmt, ext_ptw) =>
        (pure (Ok
            ((zero_extend (m := 34)
              (ppn +++ (Sail.BitVec.extractLsb valid_addr (pagesize_bits -i 1) 0))), pbmt, ext_ptw)))
      | .Err (f, ext_ptw) => (pure (Err (f, ext_ptw))))

def satp_mode (priv : Privilege) : SailM SATPMode := do
  if (((priv == Machine) || (not (← (currentlyEnabled Ext_S)))) : Bool)
  then (pure Bare)
  else
    (do
      let arch ← do (architecture Supervisor)
      let mbits ← (( do
        match arch with
        | .RV64 =>
          (do
            «assert» (xlen ≥b 64) "sys/vmem.sail:342.33-342.34"
            throw Error.Exit)
        | .RV32 =>
          (pure (0b000#3 +++ (_get_Satp32_Mode
                (Mk_Satp32 (Sail.BitVec.extractLsb (← readReg satp) 31 0)))))
        | .RV128 => (internal_error "sys/vmem.sail" 344 "RV128 not supported") ) : SailM
        SailRV32.satp_mode )
      match (← (satpMode_of_bits arch mbits)) with
      | .some m => (pure m)
      | none => (internal_error "sys/vmem.sail" 349 "invalid translation mode in satp"))

def vsatp_mode (_ : Unit) : SailM SATPMode := do
  let arch ← do (architecture VirtualSupervisor)
  let mbits ← (( do
    match arch with
    | .RV64 =>
      (do
        «assert» (xlen ≥b 64) "sys/vmem.sail:360.31-360.32"
        throw Error.Exit)
    | .RV32 =>
      (pure (0b000#3 +++ (_get_Satp32_Mode
            (Mk_Satp32 (Sail.BitVec.extractLsb (← readReg vsatp) 31 0)))))
    | .RV128 => (internal_error "sys/vmem.sail" 362 "RV128 not supported") ) : SailM
    SailRV32.satp_mode )
  match (← (satpMode_of_bits arch mbits)) with
  | .some m => (pure m)
  | none => (internal_error "sys/vmem.sail" 367 "invalid translation mode in vsatp")

def satp_mode_width_forwards (arg_ : SATPMode) : SailM Int := do
  match arg_ with
  | .Sv32 => (pure 32)
  | .Sv39 => (pure 39)
  | .Sv48 => (pure 48)
  | .Sv57 => (pure 57)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [32, 39, 48, 57] -/
def satp_mode_width_backwards (arg_ : Nat) : SATPMode :=
  match arg_ with
  | 32 => Sv32
  | 39 => Sv39
  | 48 => Sv48
  | _ => Sv57

def satp_mode_width_forwards_matches (arg_ : SATPMode) : Bool :=
  match arg_ with
  | .Sv32 => true
  | .Sv39 => true
  | .Sv48 => true
  | .Sv57 => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [32, 39, 48, 57] -/
def satp_mode_width_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 32 => true
  | 39 => true
  | 48 => true
  | 57 => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [34, 41, 50, 59] -/
def hgatp_mode_width_backwards (arg_ : Nat) : HGATPMode :=
  match arg_ with
  | 34 => Sv32x4
  | 41 => Sv39x4
  | 50 => Sv48x4
  | _ => Sv57x4

def hgatp_mode_width_forwards_matches (arg_ : HGATPMode) : Bool :=
  match arg_ with
  | .Sv32x4 => true
  | .Sv39x4 => true
  | .Sv48x4 => true
  | .Sv57x4 => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [34, 41, 50, 59] -/
def hgatp_mode_width_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 34 => true
  | 41 => true
  | 50 => true
  | 59 => true
  | _ => false

def translate_vs_stage (vaddr : virtaddr) (access : (MemoryAccessType mem_payload)) (p : Privilege) : SailM (Result ((BitVec (if ( 32
  = 32  : Bool) then 34 else 64)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  let (stage, mode) ← do
    if (((p == VirtualSupervisor) || (p == VirtualUser)) : Bool)
    then (pure (VS_Stage, (← (vsatp_mode ()))))
    else (pure (S_Stage, (← (satp_mode p))))
  if ((mode == Bare) : Bool)
  then (pure (Ok ((zero_extend (m := 34) (bits_of_virtaddr vaddr)), PBMT_PMA, init_ext_ptw)))
  else
    (do
      let sv_width ← do (satp_mode_width_forwards mode)
      «assert» (sv_width ≤b xlen) "sys/vmem.sail:578.25-578.26"
      (translate_stage sv_width (bits_of_virtaddr vaddr) access p stage))

def build_exception_context (gva : virtaddr) (gpa : (BitVec (if ( 32 = 32  : Bool) then 34 else 64))) (access : (MemoryAccessType mem_payload)) (ptw_error : PTW_Error) (stage : TranslationStage) : SailM ExceptionContext := do
  match stage with
  | .S_Stage =>
    (pure { trap := ← (translationException access ptw_error)
            excinfo_is_gva := false
            excinfo := (zero_extend (m := 32) (bits_of_virtaddr gva))
            excinfo2 := none
            excinst := none
            excinst_offset := (zeros (n := 5))
            ext := none })
  | .VS_Stage =>
    (do
      match ptw_error with
      | .PTW_Implicit_Error (e, pte_addr, access) =>
        (do
          let is_write ← (( do
            match access with
            | .Store _ => (pure true)
            | .Load _ => (pure false)
            | _ => (internal_error "sys/vmem.sail" 639 "invalid memory access type") ) : SailM Bool
            )
          let trap := (convertToGuestException e)
          let tval2 := (g_stage_tval2_exception_value trap pte_addr)
          (pure { trap := trap
                  excinfo_is_gva := true
                  excinfo := (zero_extend (m := 32) (bits_of_virtaddr gva))
                  excinfo2 := (some tval2)
                  excinst := if ((tval2 != (zeros (n := 32))) : Bool)
                    then
                      (some
                        (if (is_write : Bool)
                        then (zero_extend (m := 32) 0x00002020#32)
                        else (zero_extend (m := 32) 0x00002000#32)))
                    else none
                  excinst_offset := (zeros (n := 5))
                  ext := none }))
      | _ =>
        (pure { trap := ← (translationException access ptw_error)
                excinfo_is_gva := true
                excinfo := (zero_extend (m := 32) (bits_of_virtaddr gva))
                excinfo2 := (some (zeros (n := 32)))
                excinst := none
                excinst_offset := (zeros (n := 5))
                ext := none }))
  | .G_Stage =>
    (do
      let trap ← do (pure (convertToGuestException (← (translationException access ptw_error))))
      (pure { trap := trap
              excinfo_is_gva := true
              excinfo := (zero_extend (m := 32) (bits_of_virtaddr gva))
              excinfo2 := (some (g_stage_tval2_exception_value trap gpa))
              excinst := none
              excinst_offset := (zeros (n := 5))
              ext := none }))

def is_svukte_qualified (access : (MemoryAccessType mem_payload)) (eff_priv : Privilege) (mode : SATPMode) : SailM Bool := do
  let qualified_access_type :=
    ((access == (InstructionFetch ())) || (not (is_implicit_access access)))
  let ukte_enable ← do
    if (((eff_priv == VirtualUser) && ((← readReg cur_privilege) == User)) : Bool)
    then (pure (_get_Hstatus_HUKTE (← readReg hstatus)))
    else (pure (_get_SEnvcfg_UKTE (← (read_senvcfg ()))))
  (pure ((bne mode Bare) && (((eff_priv == User) || (eff_priv == VirtualUser)) && (qualified_access_type && (ukte_enable == 1#1)))))

def translateAddr (gva : virtaddr) (access : (MemoryAccessType mem_payload)) (p : Privilege) : SailM (Result (physaddr × page_based_mem_type × Unit) (ExceptionContext × Unit)) := SailME.run do
  let is_virtual_access := ((p == VirtualSupervisor) || (p == VirtualUser))
  let mode ← do
    if (is_virtual_access : Bool)
    then (vsatp_mode ())
    else (satp_mode p)
  if ((← (is_shadow_stack_access access)) : Bool)
  then
    (do
      if ((((mode == Bare) && (bne p Machine)) || (p == Machine)) : Bool)
      then
        SailME.throw ((Err
            ({ trap := (E_SAMO_Access_Fault ())
               excinfo_is_gva := is_virtual_access
               excinfo := (zero_extend (m := 32) (bits_of_virtaddr gva))
               excinfo2 := none
               excinst := none
               excinst_offset := (zeros (n := 5))
               ext := none }, init_ext_ptw)) : (Result (physaddr × page_based_mem_type × Unit) (ExceptionContext × Unit)))
      else (pure ()))
  else (pure ())
  if (((← (is_svukte_qualified access p mode)) && ((BitVec.access (bits_of_virtaddr gva)
           (xlen -i 1)) == 1#1)) : Bool)
  then
    (pure (Err
        ((make_exception_context (← (translationException access (PTW_Invalid_Addr ())))
          (zero_extend (m := 32) (bits_of_virtaddr gva)) is_virtual_access none), init_ext_ptw)))
  else
    (do
      match (← (translate_vs_stage gva access p)) with
      | .Ok (gpa, vs_pbmt, ext_ptw) =>
        (do
          if ((not is_virtual_access) : Bool)
          then (pure (Ok ((Physaddr gpa), vs_pbmt, ext_ptw)))
          else
            (do
              match (← (translate_g_stage gpa access)) with
              | .Ok (spa, g_pbmt, ext_ptw) =>
                (let pbmt :=
                  if ((bne vs_pbmt PBMT_PMA) : Bool)
                  then vs_pbmt
                  else g_pbmt
                (pure (Ok ((Physaddr spa), pbmt, ext_ptw))))
              | .Err (ptw_error, ext_ptw) =>
                (pure (Err
                    ((← (build_exception_context gva gpa access ptw_error G_Stage)), ext_ptw)))))
      | .Err (ptw_error, ext_ptw) =>
        (pure (Err
            ((← (build_exception_context gva (zeros (n := 34)) access ptw_error
                (if (is_virtual_access : Bool)
                then VS_Stage
                else S_Stage))), ext_ptw))))

def reset_vmem (_ : Unit) : SailM Unit := do
  writeReg vsatp (zeros (n := 32))
  writeReg hgatp (zeros (n := 32))
  (reset_TLB ())

