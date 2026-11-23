import SailRV32.Flow
import SailRV32.Common
import SailRV32.Nan
import SailRV32.Zero
import SailRV32.Rounding

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

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, (is_fp_bits k_n) -/
def float_is_lt_internal (op_0 : (BitVec k_n)) (op_1 : (BitVec k_n)) : Bool :=
  let fp_0 := (float_decompose op_0)
  let fp_1 := (float_decompose op_1)
  let is_zero := ((float_is_zero op_0) && (float_is_zero op_1))
  let diff_sign_lt := ((is_lowest_one fp_0.sign) && (! is_zero))
  let is_neg := (is_lowest_one fp_0.sign)
  let unsigned_lt := ((BitVec.toNatInt op_0) <b (BitVec.toNatInt op_1))
  let is_xor := ((is_neg && (! unsigned_lt)) || ((! is_neg) && unsigned_lt))
  let same_sign_lt := ((op_0 != op_1) && is_xor)
  if ((fp_0.sign != fp_1.sign) : Bool)
  then diff_sign_lt
  else same_sign_lt

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, (is_fp_bits k_n) -/
def float_is_eq_internal (op_0 : (BitVec k_n)) (op_1 : (BitVec k_n)) : Bool :=
  let is_zero := ((float_is_zero op_0) && (float_is_zero op_1))
  ((op_0 == op_1) || is_zero)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, (is_fp_bits k_n) -/
def float_is_ne_internal (op_0 : (BitVec k_n)) (op_1 : (BitVec k_n)) : Bool :=
  (! (float_is_eq_internal op_0 op_1))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, (is_fp_bits k_n) -/
def float_is_le_internal (op_0 : (BitVec k_n)) (op_1 : (BitVec k_n)) : Bool :=
  ((float_is_eq_internal op_0 op_1) || (float_is_lt_internal op_0 op_1))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, (is_fp_bits k_n) -/
def float_is_gt_internal (op_0 : (BitVec k_n)) (op_1 : (BitVec k_n)) : Bool :=
  (! (float_is_le_internal op_0 op_1))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, (is_fp_bits k_n) -/
def float_is_ge_internal (op_0 : (BitVec k_n)) (op_1 : (BitVec k_n)) : Bool :=
  (! (float_is_lt_internal op_0 op_1))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, List.elem k_n [16, 32, 64, 128] -/
def float_propagate_nan (op_0 : (BitVec k_n)) (op_1 : (BitVec k_n)) : ((BitVec k_n) × (BitVec 5)) :=
  let is_snan := ((float_is_snan op_0) || (float_is_snan op_1))
  let flags :=
    if (is_snan : Bool)
    then fp_eflag_invalid
    else fp_eflag_none
  let one := (Sail.BitVec.zeroExtend (1#1 : (BitVec 1)) (Sail.BitVec.length op_0))
  let fp_0 := (float_decompose op_0)
  let mask := (one <<< ((Sail.BitVec.length fp_0.mantissa) -i 1))
  let op :=
    if ((float_is_nan op_0) : Bool)
    then op_0
    else op_1
  ((op ||| mask), flags)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, List.elem k_n [16, 32, 64, 128] -/
def float_rounding_increment (sign : (BitVec 1)) (op : (BitVec k_n)) (rounding_mode : (BitVec 5)) : (BitVec k_n) :=
  let bitsize := (Sail.BitVec.length op)
  let fp := (float_decompose op)
  let is_rne := (rounding_mode == fp_rounding_rne)
  let is_rna := (rounding_mode == fp_rounding_rna)
  let not_rne_and_rna := ((! is_rne) && (! is_rna))
  let rounding_inf :=
    if ((sign == (1#1 : (BitVec 1))) : Bool)
    then fp_rounding_rdn
    else fp_rounding_rup
  let one := (Sail.BitVec.zeroExtend (1#1 : (BitVec 1)) bitsize)
  if ((not_rne_and_rna && (rounding_mode == rounding_inf)) : Bool)
  then ((one <<< ((Sail.BitVec.length fp.exp) -i 1)) - one)
  else
    (if ((not_rne_and_rna && (rounding_mode != rounding_inf)) : Bool)
    then (BitVec.zero (Sail.BitVec.length op))
    else (one <<< ((Sail.BitVec.length fp.exp) -i 2)))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, List.elem k_n [16, 32, 64, 128] -/
def float_compose_after_round (sign : (BitVec 1)) (exp : (BitVec k_n)) (mantissa : (BitVec k_n)) (increment : (BitVec k_n)) (rounding_mode : (BitVec 5)) : ((BitVec k_n) × (BitVec 5)) :=
  let bitsize := (Sail.BitVec.length mantissa)
  let fp := (float_decompose mantissa)
  let one := (Sail.BitVec.zeroExtend (1#1 : (BitVec 1)) bitsize)
  let zero := (Sail.BitVec.zeroExtend (0#1 : (BitVec 1)) bitsize)
  let round_mask := ((one <<< ((Sail.BitVec.length fp.exp) -i 1)) - one)
  let round_bits := (mantissa &&& round_mask)
  let eflag :=
    if ((is_all_zeros round_bits) : Bool)
    then fp_eflag_none
    else fp_eflag_inexact
  let rne_mask :=
    if ((rounding_mode == fp_rounding_rne) : Bool)
    then one
    else zero
  let cst_mask := (one <<< ((Sail.BitVec.length fp.exp) -i 2))
  let xor_mask := (round_bits ^^^ cst_mask)
  let not_mask :=
    if ((is_all_zeros xor_mask) : Bool)
    then one
    else zero
  let and_mask := (not_mask &&& rne_mask)
  let mantissa_mask := (Complement.complement and_mask)
  let offset := ((Sail.BitVec.length fp.exp) -i 1)
  let mantissa_round := ((mantissa + increment) >>> offset)
  let mantissa_new := (mantissa_round &&& mantissa_mask)
  let exp_new :=
    if ((is_all_zeros mantissa_new) : Bool)
    then (BitVec.zero (Sail.BitVec.length zero))
    else exp
  let exp_shift := (exp_new <<< (Sail.BitVec.length fp.mantissa))
  let exp_and_mantissa := (Sail.BitVec.truncate (exp_shift + mantissa_new) (bitsize -i 1))
  ((sign +++ exp_and_mantissa), eflag)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, List.elem k_n [16, 32, 64, 128] -/
def float_get_sign_with_all_ones_exp (sign : (BitVec 1)) (op : (BitVec k_n)) : (BitVec k_n) :=
  let bitsize := (Sail.BitVec.length op)
  let fp := (float_decompose op)
  let one := (Sail.BitVec.zeroExtend (1#1 : (BitVec 1)) bitsize)
  let all_ones := ((one <<< (Sail.BitVec.length fp.exp)) - one)
  let all_ones_exp := (all_ones <<< (Sail.BitVec.length fp.mantissa))
  (sign +++ (Sail.BitVec.truncate all_ones_exp (bitsize -i 1)))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, List.elem k_n [16, 32, 64, 128] -/
def float_round_and_compose (sign : (BitVec 1)) (exp : (BitVec k_n)) (mantissa : (BitVec k_n)) (rounding_mode : (BitVec 5)) : ((BitVec k_n) × (BitVec 5)) :=
  let op := mantissa
  let fp := (float_decompose op)
  let bitsize := (Sail.BitVec.length op)
  let one := (Sail.BitVec.zeroExtend (1#1 : (BitVec 1)) bitsize)
  let zero := (Sail.BitVec.zeroExtend (0#1 : (BitVec 1)) bitsize)
  let three := (Sail.BitVec.zeroExtend (0b11#2 : (BitVec 2)) bitsize)
  let increment := (float_rounding_increment sign mantissa rounding_mode)
  let exp_limit := ((one <<< (Sail.BitVec.length fp.exp)) - three)
  let exp_reach_limit := (! ((BitVec.toNatInt exp) <b (BitVec.toNatInt exp_limit)))
  let exp_overflow := ((BitVec.toNatInt exp) >b (BitVec.toNatInt exp_limit))
  let mantissa_limit := (one <<< (bitsize -i 1))
  let mantissa_overflow :=
    (! ((BitVec.toNatInt mantissa_limit) >b ((BitVec.toNatInt mantissa) +i (BitVec.toNatInt
            increment))))
  if ((exp_reach_limit && (exp_overflow || mantissa_overflow)) : Bool)
  then
    (let result := (float_get_sign_with_all_ones_exp sign op)
    let tail :=
      if ((is_all_zeros increment) : Bool)
      then one
      else zero
    ((result - tail), fp_eflag_overflow_and_inexact))
  else (float_compose_after_round sign exp mantissa increment rounding_mode)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, List.elem k_n [16, 32, 64, 128] -/
def float_add_same_exp_internal (op_0 : (BitVec k_n)) (op_1 : (BitVec k_n)) : SailM ((BitVec k_n) × (BitVec 5)) := do
  let fp_0 := (float_decompose op_0)
  let fp_1 := (float_decompose op_1)
  let bitsize := (Sail.BitVec.length op_0)
  let mantissa_0 := (Sail.BitVec.zeroExtend fp_0.mantissa bitsize)
  let mantissa_1 := (Sail.BitVec.zeroExtend fp_1.mantissa bitsize)
  let mantissa_sum := (mantissa_0 + mantissa_1)
  let sign := fp_0.sign
  let no_round := ((is_lowest_zero mantissa_sum) && (! (float_has_max_exp op_0)))
  if (no_round : Bool)
  then
    (let mantissa_shift := (mantissa_sum >>> 1)
    let mantissa_bitsize := (Sail.BitVec.length fp_0.mantissa)
    let exp :=
      (fp_0.exp + (Sail.BitVec.zeroExtend (1#1 : (BitVec 1)) (Sail.BitVec.length fp_0.exp)))
    let mantissa := (Sail.BitVec.truncate mantissa_shift mantissa_bitsize)
    (pure ((sign +++ (exp +++ mantissa)), fp_eflag_none)))
  else
    (do
      let exp := (Sail.BitVec.zeroExtend fp_0.exp bitsize)
      let shift_bitsize := ((Sail.BitVec.length fp_0.mantissa) +i 1)
      let one := (Sail.BitVec.zeroExtend (1#1 : (BitVec 1)) bitsize)
      let mantissa_offset := (mantissa_sum + (one <<< shift_bitsize))
      let mantissa := (mantissa_offset <<< ((Sail.BitVec.length fp_0.exp) -i 2))
      let rm ← do (float_get_rounding ())
      (pure (float_round_and_compose sign exp mantissa rm)))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, List.elem k_n [16, 32, 64, 128] -/
def float_add_same_exp (op_0 : (BitVec k_n)) (op_1 : (BitVec k_n)) : SailM ((BitVec k_n) × (BitVec 5)) := do
  let bitsize := (Sail.BitVec.length op_0)
  let fp_0 := (float_decompose op_0)
  let fp_1 := (float_decompose op_1)
  «assert» (fp_0.exp == fp_1.exp) "The exp of floating point must be same."
  let is_exp_0_all_ones := (is_all_ones fp_0.exp)
  let is_mantissa_all_zeros := (is_all_zeros (fp_0.mantissa ||| fp_1.mantissa))
  if ((is_all_zeros fp_0.exp) : Bool)
  then (pure ((op_0 + (Sail.BitVec.zeroExtend fp_1.mantissa bitsize)), fp_eflag_none))
  else
    (do
      if ((is_exp_0_all_ones && is_mantissa_all_zeros) : Bool)
      then (pure (op_0, fp_eflag_none))
      else
        (do
          if ((is_exp_0_all_ones && (! is_mantissa_all_zeros)) : Bool)
          then (pure (float_propagate_nan op_0 op_1))
          else (float_add_same_exp_internal op_0 op_1)))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, List.elem k_n [16, 32, 64, 128] -/
def float_add_less_than_exp (op_0 : (BitVec k_n)) (op_1 : (BitVec k_n)) : SailM ((BitVec k_n) × (BitVec 5)) := do
  let bitsize := (Sail.BitVec.length op_0)
  let fp_0 := (float_decompose op_0)
  let fp_1 := (float_decompose op_1)
  «assert» ((BitVec.toNatInt fp_0.exp) <b (BitVec.toNatInt fp_1.exp)) "The exp of floating point op_0 must be less than op_1."
  let is_exp_all_ones := (is_all_ones fp_1.exp)
  let mantissa_shift := (fp_1.mantissa <<< ((Sail.BitVec.length fp_1.exp) -i 2))
  let is_nan := (! (is_all_zeros mantissa_shift))
  if ((is_exp_all_ones && is_nan) : Bool)
  then (pure (float_propagate_nan op_0 op_1))
  else
    (do
      if (is_exp_all_ones : Bool)
      then (pure ((float_get_sign_with_all_ones_exp fp_0.sign op_0), fp_eflag_none))
      else
        (do
          «assert» false "Not implemented yet."
          throw Error.Exit))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, List.elem k_n [16, 32, 64, 128] -/
def float_add_diff_exp (op_0 : (BitVec k_n)) (op_1 : (BitVec k_n)) : SailM ((BitVec k_n) × (BitVec 5)) := do
  let bitsize := (Sail.BitVec.length op_0)
  let fp_0 := (float_decompose op_0)
  let fp_1 := (float_decompose op_1)
  «assert» (fp_0.exp != fp_1.exp) "The exp of floating point cannot be same."
  if (((BitVec.toNatInt fp_0.exp) <b (BitVec.toNatInt fp_1.exp)) : Bool)
  then (float_add_less_than_exp op_0 op_1)
  else
    (do
      «assert» false "Not implemented yet."
      throw Error.Exit)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, List.elem k_n [16, 32, 64, 128] -/
def float_add_internal (op_0 : (BitVec k_n)) (op_1 : (BitVec k_n)) : SailM ((BitVec k_n) × (BitVec 5)) := do
  let fp_0 := (float_decompose op_0)
  let fp_1 := (float_decompose op_1)
  «assert» ((fp_0.sign ^^^ fp_1.sign) == (0#1 : (BitVec 1))) "The sign of float add operand 0 and operand 1 must be the same."
  if ((fp_0.exp == fp_1.exp) : Bool)
  then (float_add_same_exp op_0 op_1)
  else (float_add_diff_exp op_0 op_1)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, List.elem k_n [16, 32, 64, 128] -/
def float_sub_internal (_op_0 : (BitVec k_n)) (_op_1 : (BitVec k_n)) : SailM ((BitVec k_n) × (BitVec 5)) := do
  «assert» false "Not implemented yet."
  throw Error.Exit

