import SailRV32.SailRV32
import SailRV32.Flow
import SailRV32.Arith
import SailRV32.Prelude
import SailRV32.Xlen
import SailRV32.Vlen
import SailRV32.Arithmetic
import SailRV32.PlatformConfig
import SailRV32.Regs
import SailRV32.VextRegs
import SailRV32.VextControl

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

def maybe_vmask_forwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | "" => (pure 1#1)
  | _ => throw Error.Exit

def maybe_vmask_forwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | "" => (pure true)
  | _ => throw Error.Exit

def maybe_vmask_backwards_matches (arg_ : (BitVec 1)) : Bool :=
  match arg_ with
  | 1 => true
  | 0 => true
  | _ => false

def vstart_arith_zero_required : Bool := true

def vstart_scalar_move_zero_required : Bool := true

/-- Type quantifiers: EMUL_pow : Int, num_elem : Nat, 0 ≤ num_elem -/
def illegal_vstart (cls : vstart_class) (num_elem : Nat) (EMUL_pow : Int) : SailM Bool := do
  let vs ← do (pure (BitVec.toNatInt (← readReg vstart)))
  let VLMAX :=
    if ((EMUL_pow ≥b 0) : Bool)
    then num_elem
    else (Int.tdiv num_elem (2 ^i (0 -i EMUL_pow)))
  let out_of_bounds : Bool :=
    match vstart_reserved_behavior with
    | .Vstart_Illegal => (vs ≥b VLMAX)
    | .Vstart_Ignore => false
  match cls with
  | .VSTART_ARITH => (pure (out_of_bounds || (vstart_arith_zero_required && (vs != 0))))
  | .VSTART_LOAD_STORE => (pure out_of_bounds)
  | .VSTART_SCALAR_MOVE => (pure (out_of_bounds || (vstart_scalar_move_zero_required && (vs != 0))))
  | .VSTART_MANDATORY => (pure (vs != 0))

/-- Type quantifiers: EMUL_pow : Int, EEW : Nat, 0 ≤ EEW -/
def valid_eew_emul (EEW : Nat) (EMUL_pow : Int) : Bool :=
  ((EEW ≥b 8) && ((EEW ≤b elen) && ((EMUL_pow ≥b (Neg.neg 3)) && (EMUL_pow ≤b 3))))

def valid_vtype (_ : Unit) : SailM Bool := do
  (pure ((_get_Vtype_vill (← readReg vtype)) == 0#1))

def valid_rd_mask (rd : vregidx) (vm : (BitVec 1)) : Bool :=
  ((vm != 0#1) || (bne rd zvreg))

/-- Type quantifiers: EMUL_pow : Int -/
def valid_reg_group (r : vregidx) (EMUL_pow : Int) : Bool :=
  ((Int.tmod (BitVec.toNatInt (vregidx_bits r)) (2 ^i (Max.max EMUL_pow 0))) == 0)

/-- Type quantifiers: nf : Nat, List.elem nf [1, 2, 4, 8] -/
def valid_whole_register (r : vregidx) (nf : Nat) : Bool :=
  ((Int.tmod (BitVec.toNatInt (vregidx_bits r)) nf) == 0)

/-- Type quantifiers: EMUL_pow_rd : Int, EMUL_pow_rs : Int -/
def valid_reg_overlap (rs : vregidx) (rd : vregidx) (EMUL_pow_rs : Int) (EMUL_pow_rd : Int) : Bool :=
  let rs_group := (2 ^i (Max.max EMUL_pow_rs 0))
  let rd_group := (2 ^i (Max.max EMUL_pow_rd 0))
  let rs_int := (BitVec.toNatInt (vregidx_bits rs))
  let rd_int := (BitVec.toNatInt (vregidx_bits rd))
  if ((((Int.tmod rs_int rs_group) != 0) || ((Int.tmod rd_int rd_group) != 0)) : Bool)
  then false
  else
    (if ((EMUL_pow_rs <b EMUL_pow_rd) : Bool)
    then
      (((rs_int +i rs_group) ≤b rd_int) || ((rs_int ≥b (rd_int +i rd_group)) || (((rs_int +i rs_group) == (rd_int +i rd_group)) && (EMUL_pow_rs ≥b 0))))
    else
      (if ((EMUL_pow_rs >b EMUL_pow_rd) : Bool)
      then ((rd_int ≤b rs_int) || (rd_int ≥b (rs_int +i rs_group)))
      else true))

/-- Type quantifiers: EMUL_pow_rd : Int, EMUL_pow_rs : Int -/
def valid_disjoint_reg_groups (rs : vregidx) (rd : vregidx) (EMUL_pow_rs : Int) (EMUL_pow_rd : Int) : Bool :=
  let rs_group := (2 ^i (Max.max EMUL_pow_rs 0))
  let rd_group := (2 ^i (Max.max EMUL_pow_rd 0))
  let rs_int := (BitVec.toNatInt (vregidx_bits rs))
  let rd_int := (BitVec.toNatInt (vregidx_bits rd))
  if ((((Int.tmod rs_int rs_group) != 0) || ((Int.tmod rd_int rd_group) != 0)) : Bool)
  then false
  else (((rs_int +i rs_group) ≤b rd_int) || ((rd_int +i rd_group) ≤b rs_int))

/-- Type quantifiers: data_fields : Nat, EMUL_pow_rd : Int, EMUL_pow_rs : Int, data_fields > 0 ∧
  data_fields ≤ 8 -/
def valid_disjoint_reg_groups_segmented (rs : vregidx) (rd : vregidx) (EMUL_pow_rs : Int) (EMUL_pow_rd : Int) (data_fields : Nat) : Bool :=
  let rs_group := (2 ^i (Max.max EMUL_pow_rs 0))
  let rd_group := (2 ^i (Max.max EMUL_pow_rd 0))
  let rs_int := (BitVec.toNatInt (vregidx_bits rs))
  let rd_int := (BitVec.toNatInt (vregidx_bits rd))
  if ((((Int.tmod rs_int rs_group) != 0) || ((Int.tmod rd_int rd_group) != 0)) : Bool)
  then false
  else (((rs_int +i rs_group) ≤b rd_int) || ((rd_int +i (rd_group *i data_fields)) ≤b rs_int))

/-- Type quantifiers: EMUL_pow_rs2 : Int, EEW_rs2 : Nat, EMUL_pow_rs1 : Int, EEW_rs1 : Nat, 0 ≤
  EEW_rs1, 0 ≤ EEW_rs2 -/
def valid_src_overlap (rs1 : vregidx) (EEW_rs1 : Nat) (EMUL_pow_rs1 : Int) (rs2 : vregidx) (EEW_rs2 : Nat) (EMUL_pow_rs2 : Int) : Bool :=
  let rs1_group := (2 ^i (Max.max EMUL_pow_rs1 0))
  let rs2_group := (2 ^i (Max.max EMUL_pow_rs2 0))
  let rs1_int := (BitVec.toNatInt (vregidx_bits rs1))
  let rs2_int := (BitVec.toNatInt (vregidx_bits rs2))
  if ((((Int.tmod rs1_int rs1_group) != 0) || ((Int.tmod rs2_int rs2_group) != 0)) : Bool)
  then false
  else
    (if ((EEW_rs1 == EEW_rs2) : Bool)
    then true
    else (((rs1_int +i rs1_group) ≤b rs2_int) || ((rs2_int +i rs2_group) ≤b rs1_int)))

/-- Type quantifiers: data_fields : Nat, EMUL_pow_rs2 : Int, EEW_rs2 : Nat, EMUL_pow_rs1 : Int, EEW_rs1
  : Nat, 0 ≤ EEW_rs1, 0 ≤ EEW_rs2, data_fields > 0 ∧ data_fields ≤ 8 -/
def valid_src_overlap_segmented (rs1 : vregidx) (EEW_rs1 : Nat) (EMUL_pow_rs1 : Int) (rs2 : vregidx) (EEW_rs2 : Nat) (EMUL_pow_rs2 : Int) (data_fields : Nat) : Bool :=
  if ((EEW_rs1 == EEW_rs2) : Bool)
  then ((valid_reg_group rs1 EMUL_pow_rs1) && (valid_reg_group rs2 EMUL_pow_rs2))
  else (valid_disjoint_reg_groups_segmented rs1 rs2 EMUL_pow_rs1 EMUL_pow_rs2 data_fields)

/-- Type quantifiers: EEW_rs : Nat, 0 ≤ EEW_rs -/
def valid_vm_src_overlap (vm : (BitVec 1)) (rs : vregidx) (EEW_rs : Nat) : SailM Bool := do
  «assert» (EEW_rs != 1) "extensions/V/vext_utils_insts.sail:193.20-193.21"
  (pure ((vm != 0#1) || (bne rs zvreg)))

/-- Type quantifiers: EMUL_pow : Int, nf : Nat, nf > 0 ∧ nf ≤ 8 -/
def valid_segment_group_size (nf : Nat) (EMUL_pow : Int) : Bool :=
  if ((EMUL_pow <b 0) : Bool)
  then ((Int.tdiv nf (2 ^i (0 -i EMUL_pow))) ≤b 8)
  else ((nf *i (2 ^i EMUL_pow)) ≤b 8)

/-- Type quantifiers: EMUL_pow : Int, nf : Nat, nf > 0 ∧ nf ≤ 8 -/
def valid_segment_group_without_overflow (reg : vregidx) (nf : Nat) (EMUL_pow : Int) : Bool :=
  let EMUL_reg := (2 ^i (Max.max EMUL_pow 0))
  (((BitVec.toNatInt (vregidx_bits reg)) +i (nf *i EMUL_reg)) ≤b 32)

def illegal_normal (vd : vregidx) (vm : (BitVec 1)) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || (not (valid_rd_mask vd vm))))

def illegal_vd_masked (vd : vregidx) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || (vd == zvreg)))

def illegal_vd_unmasked (_ : Unit) : SailM Bool := do
  (pure (not (← (valid_vtype ()))))

/-- Type quantifiers: LMUL_pow_new : Int, SEW_new : Nat, 0 ≤ SEW_new -/
def illegal_variable_width (vd : vregidx) (vm : (BitVec 1)) (SEW_new : Nat) (LMUL_pow_new : Int) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (valid_rd_mask vd vm)) || (not
          (valid_eew_emul SEW_new LMUL_pow_new)))))

def illegal_reduction (_ : Unit) : SailM Bool := do
  (pure (not (← (valid_vtype ()))))

/-- Type quantifiers: EEW : Nat, 0 ≤ EEW -/
def illegal_widening_reduction (EEW : Nat) : SailM Bool := do
  (pure ((← (illegal_reduction ())) || (not ((EEW ≥b 8) && (EEW ≤b elen)))))

/-- Type quantifiers: EMUL_pow : Int, EEW : Nat, nf : Nat, nf > 0 ∧ nf ≤ 8, 0 ≤ EEW -/
def illegal_load (vd : vregidx) (vm : (BitVec 1)) (nf : Nat) (EEW : Nat) (EMUL_pow : Int) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (valid_rd_mask vd vm)) || ((not
            (valid_eew_emul EEW EMUL_pow)) || ((not (valid_segment_group_size nf EMUL_pow)) || (not
              (valid_segment_group_without_overflow vd nf EMUL_pow)))))))

/-- Type quantifiers: EMUL_pow : Int, EEW : Nat, nf : Nat, nf > 0 ∧ nf ≤ 8, 0 ≤ EEW -/
def illegal_store (vs3 : vregidx) (nf : Nat) (EEW : Nat) (EMUL_pow : Int) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (valid_eew_emul EEW EMUL_pow)) || ((not
            (valid_segment_group_size nf EMUL_pow)) || (not
            (valid_segment_group_without_overflow vs3 nf EMUL_pow))))))

/-- Type quantifiers: EMUL_pow_data : Int, EMUL_pow_index : Int, EEW_index : Nat, nf : Nat, nf > 0
  ∧ nf ≤ 8, 0 ≤ EEW_index -/
def illegal_indexed_load (vd : vregidx) (vm : (BitVec 1)) (nf : Nat) (EEW_index : Nat) (EMUL_pow_index : Int) (EMUL_pow_data : Int) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (valid_rd_mask vd vm)) || ((not
            (valid_eew_emul EEW_index EMUL_pow_index)) || ((not
              (valid_segment_group_size nf EMUL_pow_data)) || (not
              (valid_segment_group_without_overflow vd nf EMUL_pow_data)))))))

/-- Type quantifiers: EMUL_pow_data : Int, EMUL_pow_index : Int, EEW_index : Nat, nf : Nat, nf > 0
  ∧ nf ≤ 8, 0 ≤ EEW_index -/
def illegal_indexed_store (vs3 : vregidx) (nf : Nat) (EEW_index : Nat) (EMUL_pow_index : Int) (EMUL_pow_data : Int) : SailM Bool := do
  (pure ((not (← (valid_vtype ()))) || ((not (valid_eew_emul EEW_index EMUL_pow_index)) || ((not
            (valid_segment_group_size nf EMUL_pow_data)) || (not
            (valid_segment_group_without_overflow vs3 nf EMUL_pow_data))))))

/-- Type quantifiers: SEW : Nat, SEW ≥ 0, SEW ≥ 8 -/
def get_scalar (rs1 : regidx) (SEW : Nat) : SailM (BitVec SEW) := do
  if ((SEW ≤b xlen) : Bool)
  then (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) (SEW -i 1) 0))
  else (pure (sign_extend (m := SEW) (← (rX_bits rs1))))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_m : Nat, k_m ≥ 0, i : Nat, k_n > 0 ∧
  k_m > 0 ∧ i ≥ 0 ∧ (4 * i + 3) < k_n -/
def get_velem_quad (v : (Vector (BitVec k_m) k_n)) (i : Nat) : (BitVec (4 * k_m)) :=
  ((GetElem?.getElem! v ((4 *i i) +i 3)) +++ ((GetElem?.getElem! v ((4 *i i) +i 2)) +++ ((GetElem?.getElem!
          v ((4 *i i) +i 1)) +++ (GetElem?.getElem! v (4 *i i)))))

/-- Type quantifiers: i : Nat, SEW : Nat, k_n : Nat, k_n ≥ 0, k_n > 0, List.elem SEW
  [8, 16, 32, 64], 0 ≤ i -/
def write_velem_quad (vd : vregidx) (SEW : Nat) (input : (BitVec k_n)) (i : Nat) : SailM Unit := do
  let loop_j_lower := 0
  let loop_j_upper := 3
  let mut loop_vars := ()
  for j in [loop_j_lower:loop_j_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      «assert» (((j +i 1) *i SEW) ≤b (Sail.BitVec.length input)) "extensions/V/vext_utils_insts.sail:363.30-363.31"
      (write_single_element SEW ((4 *i i) +i j) vd
        (Sail.BitVec.extractLsb input (((j +i 1) *i SEW) -i 1) (j *i SEW)))
  (pure loop_vars)

/-- Type quantifiers: _n : Nat, _n ≥ 0, k_m : Nat, k_m ≥ 0, i : Nat, _n > 0 ∧
  8 ≤ k_m ∧ k_m ≤ 64 ∧ i ≥ 0 ∧ (8 * i + 7) < _n -/
def get_velem_oct_vec {_n : _} (v : (Vector (BitVec k_m) _n)) (i : Nat) : (Vector (BitVec k_m) 8) :=
  #v[(GetElem?.getElem! v (8 *i i)), (GetElem?.getElem! v ((8 *i i) +i 1)), (GetElem?.getElem! v
      ((8 *i i) +i 2)), (GetElem?.getElem! v ((8 *i i) +i 3)), (GetElem?.getElem! v ((8 *i i) +i 4)), (GetElem?.getElem!
      v ((8 *i i) +i 5)), (GetElem?.getElem! v ((8 *i i) +i 6)), (GetElem?.getElem! v
      ((8 *i i) +i 7))]

/-- Type quantifiers: i : Nat, SEW : Nat, SEW ≥ 0, (is_sew_bitsize SEW), 0 ≤ i -/
def write_velem_oct_vec (vd : vregidx) (SEW : Nat) (input : (Vector (BitVec SEW) 8)) (i : Nat) : SailM Unit := do
  let loop_j_lower := 0
  let loop_j_upper := 7
  let mut loop_vars := ()
  for j in [loop_j_lower:loop_j_upper:1]i do
    let () := loop_vars
    loop_vars ← do (write_single_element SEW ((8 *i i) +i j) vd (GetElem?.getElem! input j))
  (pure loop_vars)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_m : Nat, k_m ≥ 0, i : Nat, k_n > 0 ∧
  8 ≤ k_m ∧ k_m ≤ 64 ∧ i ≥ 0 ∧ (4 * i + 3) < k_n -/
def get_velem_quad_vec (v : (Vector (BitVec k_m) k_n)) (i : Nat) : (Vector (BitVec k_m) 4) :=
  #v[(GetElem?.getElem! v (4 *i i)), (GetElem?.getElem! v ((4 *i i) +i 1)), (GetElem?.getElem! v
      ((4 *i i) +i 2)), (GetElem?.getElem! v ((4 *i i) +i 3))]

/-- Type quantifiers: i : Nat, SEW : Nat, SEW ≥ 0, (is_sew_bitsize SEW) ∧ i ≥ 0 -/
def write_velem_quad_vec (vd : vregidx) (SEW : Nat) (input : (Vector (BitVec SEW) 4)) (i : Nat) : SailM Unit := do
  let loop_j_lower := 0
  let loop_j_upper := 3
  let mut loop_vars := ()
  for j in [loop_j_lower:loop_j_upper:1]i do
    let () := loop_vars
    loop_vars ← do (write_single_element SEW ((4 *i i) +i j) vd (GetElem?.getElem! input j))
  (pure loop_vars)

def get_start_element (_ : Unit) : SailM Nat := do
  (pure (BitVec.toNatInt (← readReg vstart)))

def get_end_element (_ : Unit) : SailM Int := do
  (pure ((BitVec.toNatInt (← readReg vl)) -i 1))

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, _EEW : Nat, _EEW ≥ 0, LMUL_pow : Int, num_elem
  ≥ 0 -/
def init_masked_result (num_elem : Nat) (_EEW : Nat) (LMUL_pow : Int) (vd_val : (Vector (BitVec _EEW) num_elem)) (vm_val : (BitVec num_elem)) : SailM ((Vector (BitVec _EEW) num_elem) × (BitVec num_elem)) := do
  let start_element ← do (get_start_element ())
  let end_element ← do (get_end_element ())
  let tail_ag ← (( do (get_vtype_vta ()) ) : SailM agtype )
  let mask_ag ← (( do (get_vtype_vma ()) ) : SailM agtype )
  let mask ← (( do (undefined_bitvector (Sail.BitVec.length vm_val)) ) : SailM (BitVec num_elem) )
  let result ← (( do
    (undefined_vector (Sail.BitVec.length vm_val) (← (undefined_bitvector _EEW))) ) : SailM
    (Vector (BitVec _EEW) num_elem) )
  let real_num_elem :=
    if ((LMUL_pow ≥b 0) : Bool)
    then num_elem
    else (Int.tdiv num_elem (2 ^i (0 -i LMUL_pow)))
  «assert» (num_elem ≥b real_num_elem) "extensions/V/vext_utils_insts.sail:418.34-418.35"
  let (mask, result) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (num_elem -i 1)
    let mut loop_vars := (mask, result)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (mask, result) := loop_vars
      loop_vars :=
        let (mask, result) : ((BitVec num_elem) × (Vector (BitVec _EEW) num_elem)) :=
          if ((i <b start_element) : Bool)
          then
            (let result : (Vector (BitVec _EEW) num_elem) :=
              (vectorUpdate result i (GetElem?.getElem! vd_val i))
            let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
            (mask, result))
          else
            (let (mask, result) : ((BitVec num_elem) × (Vector (BitVec _EEW) num_elem)) :=
              if ((i >b end_element) : Bool)
              then
                (let result : (Vector (BitVec _EEW) num_elem) :=
                  (vectorUpdate result i
                    (match tail_ag with
                    | .UNDISTURBED => (GetElem?.getElem! vd_val i)
                    | .AGNOSTIC => (GetElem?.getElem! vd_val i)))
                let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                (mask, result))
              else
                (let (mask, result) : ((BitVec num_elem) × (Vector (BitVec _EEW) num_elem)) :=
                  if ((i ≥b real_num_elem) : Bool)
                  then
                    (let result : (Vector (BitVec _EEW) num_elem) :=
                      (vectorUpdate result i
                        (match tail_ag with
                        | .UNDISTURBED => (GetElem?.getElem! vd_val i)
                        | .AGNOSTIC => (GetElem?.getElem! vd_val i)))
                    let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                    (mask, result))
                  else
                    (let (mask, result) : ((BitVec num_elem) × (Vector (BitVec _EEW) num_elem)) :=
                      if (((BitVec.access vm_val i) == 0#1) : Bool)
                      then
                        (let result : (Vector (BitVec _EEW) num_elem) :=
                          (vectorUpdate result i
                            (match mask_ag with
                            | .UNDISTURBED => (GetElem?.getElem! vd_val i)
                            | .AGNOSTIC => (GetElem?.getElem! vd_val i)))
                        let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                        (mask, result))
                      else
                        (let mask : (BitVec num_elem) := (BitVec.update mask i 1#1)
                        (mask, result))
                    (mask, result))
                (mask, result))
            (mask, result))
        (mask, result)
    (pure loop_vars) ) : SailM ((BitVec num_elem) × (Vector (BitVec _EEW) num_elem)) )
  (pure (result, mask))

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, LMUL_pow : Int, num_elem > 0 -/
def init_masked_source (num_elem : Nat) (LMUL_pow : Int) (vm_val : (BitVec num_elem)) : SailM (BitVec num_elem) := do
  let start_element ← do (get_start_element ())
  let end_element ← do (get_end_element ())
  let mask ← (( do (undefined_bitvector (Sail.BitVec.length vm_val)) ) : SailM (BitVec num_elem) )
  let real_num_elem :=
    if ((LMUL_pow ≥b 0) : Bool)
    then num_elem
    else (Int.tdiv num_elem (2 ^i (0 -i LMUL_pow)))
  «assert» (num_elem ≥b real_num_elem) "extensions/V/vext_utils_insts.sail:467.34-467.35"
  let loop_i_lower := 0
  let loop_i_upper := (num_elem -i 1)
  let mut loop_vars := mask
  for i in [loop_i_lower:loop_i_upper:1]i do
    let mask := loop_vars
    loop_vars :=
      if ((i <b start_element) : Bool)
      then (BitVec.update mask i 0#1)
      else
        (if ((i >b end_element) : Bool)
        then (BitVec.update mask i 0#1)
        else
          (if ((i ≥b real_num_elem) : Bool)
          then (BitVec.update mask i 0#1)
          else
            (if (((BitVec.access vm_val i) == 0#1) : Bool)
            then (BitVec.update mask i 0#1)
            else (BitVec.update mask i 1#1))))
  (pure loop_vars)

/-- Type quantifiers: LMUL_pow : Int, _EEW : Nat, num_elem : Nat, num_elem ≥ 0, num_elem ≥ 0, List.elem
  _EEW [8, 16, 32, 64] -/
def init_masked_result_carry (num_elem : Nat) (_EEW : Nat) (LMUL_pow : Int) (vd_val : (BitVec num_elem)) : SailM ((BitVec num_elem) × (BitVec num_elem)) := do
  let start_element ← do (get_start_element ())
  let end_element ← do (get_end_element ())
  let mask ← (( do (undefined_bitvector (Sail.BitVec.length vd_val)) ) : SailM (BitVec num_elem) )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length vd_val)) ) : SailM (BitVec num_elem)
    )
  let real_num_elem :=
    if ((LMUL_pow ≥b 0) : Bool)
    then num_elem
    else (Int.tdiv num_elem (2 ^i (0 -i LMUL_pow)))
  «assert» (num_elem ≥b real_num_elem) "extensions/V/vext_utils_insts.sail:502.34-502.35"
  let (mask, result) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (num_elem -i 1)
    let mut loop_vars := (mask, result)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (mask, result) := loop_vars
      loop_vars :=
        let (mask, result) : ((BitVec num_elem) × (BitVec num_elem)) :=
          if ((i <b start_element) : Bool)
          then
            (let result : (BitVec num_elem) := (BitVec.update result i (BitVec.access vd_val i))
            let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
            (mask, result))
          else
            (let (mask, result) : ((BitVec num_elem) × (BitVec num_elem)) :=
              if ((i >b end_element) : Bool)
              then
                (let result : (BitVec num_elem) := (BitVec.update result i (BitVec.access vd_val i))
                let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                (mask, result))
              else
                (let (mask, result) : ((BitVec num_elem) × (BitVec num_elem)) :=
                  if ((i ≥b real_num_elem) : Bool)
                  then
                    (let result : (BitVec num_elem) :=
                      (BitVec.update result i (BitVec.access vd_val i))
                    let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                    (mask, result))
                  else
                    (let mask : (BitVec num_elem) := (BitVec.update mask i 1#1)
                    (mask, result))
                (mask, result))
            (mask, result))
        (mask, result)
    (pure loop_vars) ) : SailM ((BitVec num_elem) × (BitVec num_elem)) )
  (pure (result, mask))

/-- Type quantifiers: LMUL_pow : Int, _EEW : Nat, num_elem : Nat, num_elem ≥ 0, num_elem ≥ 0, List.elem
  _EEW [8, 16, 32, 64] -/
def init_masked_result_cmp (num_elem : Nat) (_EEW : Nat) (LMUL_pow : Int) (vd_val : (BitVec num_elem)) (vm_val : (BitVec num_elem)) : SailM ((BitVec num_elem) × (BitVec num_elem)) := do
  let start_element ← do (get_start_element ())
  let end_element ← do (get_end_element ())
  let mask_ag ← (( do (get_vtype_vma ()) ) : SailM agtype )
  let mask ← (( do (undefined_bitvector (Sail.BitVec.length vm_val)) ) : SailM (BitVec num_elem) )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length vm_val)) ) : SailM (BitVec num_elem)
    )
  let real_num_elem :=
    if ((LMUL_pow ≥b 0) : Bool)
    then num_elem
    else (Int.tdiv num_elem (2 ^i (0 -i LMUL_pow)))
  «assert» (num_elem ≥b real_num_elem) "extensions/V/vext_utils_insts.sail:539.34-539.35"
  let (mask, result) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (num_elem -i 1)
    let mut loop_vars := (mask, result)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (mask, result) := loop_vars
      loop_vars :=
        let (mask, result) : ((BitVec num_elem) × (BitVec num_elem)) :=
          if ((i <b start_element) : Bool)
          then
            (let result : (BitVec num_elem) := (BitVec.update result i (BitVec.access vd_val i))
            let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
            (mask, result))
          else
            (let (mask, result) : ((BitVec num_elem) × (BitVec num_elem)) :=
              if ((i >b end_element) : Bool)
              then
                (let result : (BitVec num_elem) := (BitVec.update result i (BitVec.access vd_val i))
                let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                (mask, result))
              else
                (let (mask, result) : ((BitVec num_elem) × (BitVec num_elem)) :=
                  if ((i ≥b real_num_elem) : Bool)
                  then
                    (let result : (BitVec num_elem) :=
                      (BitVec.update result i (BitVec.access vd_val i))
                    let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                    (mask, result))
                  else
                    (let (mask, result) : ((BitVec num_elem) × (BitVec num_elem)) :=
                      if (((BitVec.access vm_val i) == 0#1) : Bool)
                      then
                        (let result : (BitVec num_elem) :=
                          (BitVec.update result i
                            (match mask_ag with
                            | .UNDISTURBED => (BitVec.access vd_val i)
                            | .AGNOSTIC => (BitVec.access vd_val i)))
                        let mask : (BitVec num_elem) := (BitVec.update mask i 0#1)
                        (mask, result))
                      else
                        (let mask : (BitVec num_elem) := (BitVec.update mask i 1#1)
                        (mask, result))
                    (mask, result))
                (mask, result))
            (mask, result))
        (mask, result)
    (pure loop_vars) ) : SailM ((BitVec num_elem) × (BitVec num_elem)) )
  (pure (result, mask))

/-- Type quantifiers: num_elem : Nat, num_elem ≥ 0, SEW : Nat, LMUL_pow : Int, nf : Nat, num_elem
  ≥ 0 ∧ (is_sew_bitsize SEW) ∧ (nfields_range nf) -/
def read_vreg_seg (num_elem : Nat) (SEW : Nat) (LMUL_pow : Int) (nf : Nat) (vrid : vregidx) : SailM (Vector (BitVec (nf * SEW)) num_elem) := do
  let LMUL_reg : Int :=
    if ((LMUL_pow ≤b 0) : Bool)
    then 1
    else (2 ^i LMUL_pow)
  let vreg_list : (Vector (Vector (BitVec SEW) num_elem) nf) :=
    (vectorInit (vectorInit (zeros (n := SEW))))
  let result : (Vector (BitVec (nf * SEW)) num_elem) :=
    (vectorInit (zeros (n := ((Vector.length vreg_list) *i SEW))))
  let vreg_list ← (( do
    let loop_j_lower := 0
    let loop_j_upper := (nf -i 1)
    let mut loop_vars := vreg_list
    for j in [loop_j_lower:loop_j_upper:1]i do
      let vreg_list := loop_vars
      loop_vars ← do
        (pure (vectorUpdate vreg_list j
            (← (read_vreg num_elem SEW LMUL_pow
                (vregidx_offset vrid (to_bits_unsafe (l := 5) (j *i LMUL_reg)))))))
    (pure loop_vars) ) : SailM (Vector (Vector (BitVec SEW) num_elem) nf) )
  let loop_i_lower := 0
  let loop_i_upper := (num_elem -i 1)
  let mut loop_vars_1 := result
  for i in [loop_i_lower:loop_i_upper:1]i do
    let result := loop_vars_1
    loop_vars_1 ← do
      let result : (Vector (BitVec (nf * SEW)) num_elem) :=
        (vectorUpdate result i (zeros (n := ((Vector.length vreg_list) *i SEW))))
      let loop_j_lower := 0
      let loop_j_upper := (nf -i 1)
      let mut loop_vars_2 := result
      for j in [loop_j_lower:loop_j_upper:1]i do
        let result := loop_vars_2
        loop_vars_2 :=
          (vectorUpdate result i
            ((GetElem?.getElem! result i) ||| ((zero_extend
                  (m := ((Vector.length vreg_list) *i SEW))
                  (GetElem?.getElem! (GetElem?.getElem! vreg_list j) i)) <<< (j *i SEW))))
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: SEW : Nat, k_n : Nat, k_n ≥ 0, 0 ≤ k_n, List.elem SEW [8, 16, 32, 64] -/
def get_shift_amount (bit_val : (BitVec k_n)) (SEW : Nat) : SailM Nat := do
  let lowlog2bits : Nat :=
    match SEW with
    | 8 => 3
    | 16 => 4
    | 32 => 5
    | _ => 6
  «assert» ((0 <b lowlog2bits) && (lowlog2bits <b (Sail.BitVec.length bit_val))) "extensions/V/vext_utils_insts.sail:601.43-601.44"
  (pure (BitVec.toNatInt (Sail.BitVec.extractLsb bit_val (lowlog2bits -i 1) 0)))

/-- Type quantifiers: k_m : Nat, shift_amount : Nat, k_m > 0 ∧ shift_amount ≥ 0 -/
def get_fixed_rounding_incr (vec_elem : (BitVec k_m)) (shift_amount : Nat) : SailM (BitVec 1) := do
  if ((shift_amount == 0) : Bool)
  then (pure 0#1)
  else
    (do
      let rounding_mode ← do (pure (_get_Vcsr_vxrm (← readReg vcsr)))
      «assert» (shift_amount <b (Sail.BitVec.length vec_elem)) "extensions/V/vext_utils_insts.sail:612.28-612.29"
      match rounding_mode with
      | 0b00 => (pure (BitVec.access vec_elem (shift_amount -i 1)))
      | 0b01 =>
        (pure (bool_to_bit
            (((BitVec.access vec_elem (shift_amount -i 1)) == 1#1) && ((if ((shift_amount == 1) : Bool)
                then false
                else
                  ((Sail.BitVec.extractLsb vec_elem (shift_amount -i 2) 0) != (zeros
                      (n := (((shift_amount -i 2) -i 0) +i 1))))) || ((BitVec.access vec_elem
                    shift_amount) == 1#1)))))
      | 0b10 => (pure 0#1)
      | _ =>
        (pure (bool_to_bit
            (((BitVec.access vec_elem shift_amount) != 1#1) && ((Sail.BitVec.extractLsb vec_elem
                  (shift_amount -i 1) 0) != (zeros (n := (((shift_amount -i 1) -i 0) +i 1))))))))

/-- Type quantifiers: len : Nat, k_n : Nat, k_n ≥ len ∧ len > 1 -/
def unsigned_saturation (len : Nat) (elem : (BitVec k_n)) : SailM (BitVec len) := do
  if (((BitVec.toNatInt elem) >b (BitVec.toNatInt (ones (n := len)))) : Bool)
  then
    (do
      (write_vxsat 1#1)
      (pure (ones (n := len))))
  else
    (do
      (write_vxsat (_get_Vcsr_vxsat (← readReg vcsr)))
      (pure (Sail.BitVec.extractLsb elem (len -i 1) 0)))

/-- Type quantifiers: len : Nat, k_n : Nat, k_n ≥ len ∧ len > 1 -/
def signed_saturation (len : Nat) (elem : (BitVec k_n)) : SailM (BitVec len) := do
  if (((BitVec.toInt elem) >b (BitVec.toInt (0#1 +++ (ones (n := (len -i 1)))))) : Bool)
  then
    (do
      (write_vxsat 1#1)
      (pure (0#1 +++ (ones (n := (len -i 1))))))
  else
    (do
      if (((BitVec.toInt elem) <b (BitVec.toInt (1#1 +++ (zeros (n := (len -i 1)))))) : Bool)
      then
        (do
          (write_vxsat 1#1)
          (pure (1#1 +++ (zeros (n := (len -i 1))))))
      else
        (do
          (write_vxsat (_get_Vcsr_vxsat (← readReg vcsr)))
          (pure (Sail.BitVec.extractLsb elem (len -i 1) 0))))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, _m : Nat, _m ≥ 0, k_n ≥ 0 ∧ _m ≥ 0 -/
def vrev8 {_m : _} (input : (Vector (BitVec (_m * 8)) k_n)) : (Vector (BitVec (_m * 8)) k_n) := Id.run do
  let output : (Vector (BitVec (_m * 8)) k_n) := input
  let loop_i_lower := 0
  let loop_i_upper := ((Vector.length output) -i 1)
  let mut loop_vars := output
  for i in [loop_i_lower:loop_i_upper:1]i do
    let output := loop_vars
    loop_vars := (vectorUpdate output i (rev8 (GetElem?.getElem! input i)))
  (pure loop_vars)

