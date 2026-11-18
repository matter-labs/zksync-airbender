import SailRV32.SailRV32
import SailRV32.Prelude
import SailRV32.Errors
import SailRV32.Xlen
import SailRV32.PlatformConfig
import SailRV32.VmemTypes
import SailRV32.MemTypeUtils
import SailRV32.SysRegs
import SailRV32.PmpRegs

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

def pmpCheckRWX (ent : (BitVec 8)) (access : (MemoryAccessType mem_payload)) : SailM Bool := do
  match access with
  | .Load .Data => (pure ((_get_Pmpcfg_ent_R ent) == 1#1))
  | .Load .Vector => (pure ((_get_Pmpcfg_ent_R ent) == 1#1))
  | .Load .PageTableEntry => (pure ((_get_Pmpcfg_ent_R ent) == 1#1))
  | .LoadReserved (_, _, .Data) => (pure ((_get_Pmpcfg_ent_R ent) == 1#1))
  | .Store .Data => (pure ((_get_Pmpcfg_ent_W ent) == 1#1))
  | .Store .Vector => (pure ((_get_Pmpcfg_ent_W ent) == 1#1))
  | .Store .PageTableEntry => (pure ((_get_Pmpcfg_ent_W ent) == 1#1))
  | .StoreConditional (_, _, .Data) => (pure ((_get_Pmpcfg_ent_W ent) == 1#1))
  | .Atomic (_, _, _, .Data, .Data) =>
    (pure (((_get_Pmpcfg_ent_R ent) == 1#1) && ((_get_Pmpcfg_ent_W ent) == 1#1)))
  | .LoadExecute .Data =>
    (pure (((_get_Pmpcfg_ent_R ent) == 1#1) && ((_get_Pmpcfg_ent_X ent) == 1#1)))
  | .InstructionFetch () => (pure ((_get_Pmpcfg_ent_X ent) == 1#1))
  | .Load .ShadowStack =>
    (pure (((_get_Pmpcfg_ent_R ent) == 1#1) && ((_get_Pmpcfg_ent_W ent) == 1#1)))
  | .Store .ShadowStack =>
    (pure (((_get_Pmpcfg_ent_R ent) == 1#1) && ((_get_Pmpcfg_ent_W ent) == 1#1)))
  | .Atomic (_, _, _, .ShadowStack, .ShadowStack) =>
    (pure (((_get_Pmpcfg_ent_R ent) == 1#1) && ((_get_Pmpcfg_ent_W ent) == 1#1)))
  | .LoadExecute p =>
    (internal_error "pmp/pmp_control.sail" 36
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadExecute.")))
  | .LoadReserved (_, _, p) =>
    (internal_error "pmp/pmp_control.sail" 37
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadReserved.")))
  | .StoreConditional (_, _, p) =>
    (internal_error "pmp/pmp_control.sail" 38
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for StoreConditional.")))
  | .Atomic (_, _, _, rp, wp) =>
    (internal_error "pmp/pmp_control.sail" 39
      (HAppend.hAppend "Invalid payloads ("
        (HAppend.hAppend (mem_payload_name_forwards rp)
          (HAppend.hAppend ", " (HAppend.hAppend (mem_payload_str_forwards wp) ") for Atomic.")))))
  | .CacheAccess (.CB_manage _) =>
    (pure (((_get_Pmpcfg_ent_R ent) == 1#1) || ((_get_Pmpcfg_ent_W ent) == 1#1)))
  | .CacheAccess (.CB_zero ()) => (pure ((_get_Pmpcfg_ent_W ent) == 1#1))
  | .CacheAccess (.CB_prefetch p) =>
    (match p with
    | .PREFETCH_I => (pure ((_get_Pmpcfg_ent_X ent) == 1#1))
    | .PREFETCH_R => (pure ((_get_Pmpcfg_ent_R ent) == 1#1))
    | .PREFETCH_W => (pure ((_get_Pmpcfg_ent_W ent) == 1#1)))

def undefined_pmpAddrMatch (_ : Unit) : SailM pmpAddrMatch := do
  (internal_pick [PMP_NoMatch, PMP_PartialMatch, PMP_Match])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def pmpAddrMatch_of_num (arg_ : Nat) : pmpAddrMatch :=
  match arg_ with
  | 0 => PMP_NoMatch
  | 1 => PMP_PartialMatch
  | _ => PMP_Match

def num_of_pmpAddrMatch (arg_ : pmpAddrMatch) : Int :=
  match arg_ with
  | .PMP_NoMatch => 0
  | .PMP_PartialMatch => 1
  | .PMP_Match => 2

/-- Type quantifiers: width : Nat, addr : Nat, end_ : Nat, begin : Nat, 0 ≤ begin, 0 ≤ end_, 0
  ≤ addr, 0 ≤ width -/
def pmpRangeMatch (begin : Nat) (end_ : Nat) (addr : Nat) (width : Nat) : pmpAddrMatch :=
  if ((((addr +i width) ≤b begin) || (end_ ≤b addr)) : Bool)
  then PMP_NoMatch
  else
    (if (((begin ≤b addr) && ((addr +i width) ≤b end_)) : Bool)
    then PMP_Match
    else PMP_PartialMatch)

/-- Type quantifiers: grain : Nat, 0 ≤ grain ∧ grain ≤ 63 -/
def pmpTORBound (addr : (BitVec 32)) (grain : Nat) : (BitVec 32) :=
  let mask : xlenbits := (zero_extend (m := 32) (ones (n := (Min.min grain xlen))))
  (addr &&& (Complement.complement mask))

def test_pmpTORBound (_ : Unit) : SailM Unit := do
  «assert» ((pmpTORBound (zero_extend (m := 32) 0x5#4) 0) == (zero_extend (m := 32) 0x5#4)) "pmp/pmp_control.sail:85.61-85.62"
  «assert» ((pmpTORBound (zero_extend (m := 32) 0x5#4) 1) == (zero_extend (m := 32) 0x4#4)) "pmp/pmp_control.sail:86.61-86.62"
  «assert» ((pmpTORBound (zero_extend (m := 32) 0x7#4) 2) == (zero_extend (m := 32) 0x4#4)) "pmp/pmp_control.sail:87.61-87.62"

def pmpMatchAddr (typ_0 : physaddr) (width : (BitVec 32)) (ent : (BitVec 8)) (pmpaddr : (BitVec 32)) (prev_pmpaddr : (BitVec 32)) : SailM pmpAddrMatch := do
  let .Physaddr addr : physaddr := typ_0
  let addr := (BitVec.toNatInt addr)
  let width := (BitVec.toNatInt width)
  match (pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent)) with
  | .OFF => (pure PMP_NoMatch)
  | .TOR =>
    (let pmpaddr := (pmpTORBound pmpaddr sys_pmp_grain)
    let prev_pmpaddr := (pmpTORBound prev_pmpaddr sys_pmp_grain)
    if ((zopz0zKzJ_u prev_pmpaddr pmpaddr) : Bool)
    then (pure PMP_NoMatch)
    else
      (pure (pmpRangeMatch ((BitVec.toNatInt prev_pmpaddr) *i 4) ((BitVec.toNatInt pmpaddr) *i 4)
          addr width)))
  | .NA4 =>
    (do
      «assert» (sys_pmp_grain <b 1) "NA4 cannot be selected when PMP grain G >= 1."
      let begin := ((BitVec.toNatInt pmpaddr) *i 4)
      (pure (pmpRangeMatch begin (begin +i 4) addr width)))
  | .NAPOT =>
    (let mask := (pmpaddr ^^^ (BitVec.addInt pmpaddr 1))
    let begin_words := (BitVec.toNatInt (pmpaddr &&& (Complement.complement mask)))
    let end_words := ((begin_words +i (BitVec.toNatInt mask)) +i 1)
    (pure (pmpRangeMatch (begin_words *i 4) (end_words *i 4) addr width)))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def pmpCheck (addr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (priv : Privilege) : SailM (Option ExceptionType) := SailME.run do
  if ((sys_pmp_count == 0) : Bool)
  then (pure none)
  else
    (do
      let width : xlenbits := (to_bits (l := 32) width)
      let loop_i_lower := 0
      let loop_i_upper := (sys_pmp_count -i 1)
      let mut loop_vars := ()
      for i in [loop_i_lower:loop_i_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          let prev_pmpaddr ← do
            if ((i >b 0) : Bool)
            then (pmpReadAddrReg (i -i 1))
            else (pure (zeros (n := 32)))
          let cfg ← do (pure (GetElem?.getElem! (← readReg pmpcfg_n) i))
          match (← (pmpMatchAddr addr width cfg (← (pmpReadAddrReg i)) prev_pmpaddr)) with
          | .PMP_NoMatch => (pure ())
          | .PMP_PartialMatch =>
            SailME.throw (← do
                let _ : Unit :=
                  if ((get_config_print_pmp ()) : Bool)
                  then
                    (print_endline
                      (HAppend.hAppend "PMP check failed with a partial match at entry #"
                        (HAppend.hAppend (Int.repr i) ".")))
                  else ()
                (pure (some (← (accessFaultFromAccessType access)))))
          | .PMP_Match =>
            SailME.throw (← do
                if (((← (pmpCheckRWX cfg access)) || ((priv == Machine) && (not (pmpLocked cfg)))) : Bool)
                then (pure none)
                else
                  (do
                    let _ : Unit :=
                      if ((get_config_print_pmp ()) : Bool)
                      then
                        (print_endline
                          (HAppend.hAppend "PMP check failed at matching entry #"
                            (HAppend.hAppend (Int.repr i) ".")))
                      else ()
                    (pure (some (← (accessFaultFromAccessType access))))))
      (pure loop_vars)
      if ((priv == Machine) : Bool)
      then (pure none)
      else
        (do
          let _ : Unit :=
            if ((get_config_print_pmp ()) : Bool)
            then (print_endline "PMP check failed with no matching entry.")
            else ()
          (pure (some (← (accessFaultFromAccessType access))))))

def reset_pmp (_ : Unit) : SailM Unit := do
  let loop_i_lower := 0
  let loop_i_upper := 63
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      writeReg pmpcfg_n (vectorUpdate (← readReg pmpcfg_n) i
        (_update_Pmpcfg_ent_L
          (_update_Pmpcfg_ent_A (GetElem?.getElem! (← readReg pmpcfg_n) i)
            (pmpAddrMatchType_encdec_forwards OFF)) 0#1))
  (pure loop_vars)

