import SailRV32.Flow
import SailRV32.Prelude
import SailRV32.FextInsts

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

def fsplit_D (x64 : (BitVec 64)) : ((BitVec 1) × (BitVec 11) × (BitVec 52)) :=
  ((Sail.BitVec.extractLsb x64 63 63), (Sail.BitVec.extractLsb x64 62 52), (Sail.BitVec.extractLsb
    x64 51 0))

def fmake_D (sign : (BitVec 1)) (exp : (BitVec 11)) (mant : (BitVec 52)) : (BitVec 64) :=
  (sign +++ (exp +++ mant))

def f_is_neg_inf_D (x64 : (BitVec 64)) : Bool :=
  let (sign, exp, mant) := (fsplit_D x64)
  ((sign == 1#1) && ((exp == (ones (n := 11))) && (mant == (zeros (n := 52)))))

def f_is_neg_norm_D (x64 : (BitVec 64)) : Bool :=
  let (sign, exp, mant) := (fsplit_D x64)
  ((sign == 1#1) && ((exp != (zeros (n := 11))) && (exp != (ones (n := 11)))))

def f_is_neg_subnorm_D (x64 : (BitVec 64)) : Bool :=
  let (sign, exp, mant) := (fsplit_D x64)
  ((sign == 1#1) && ((exp == (zeros (n := 11))) && (mant != (zeros (n := 52)))))

def f_is_neg_zero_D (x64 : (BitVec 64)) : Bool :=
  let (sign, exp, mant) := (fsplit_D x64)
  ((sign == (ones (n := 1))) && ((exp == (zeros (n := 11))) && (mant == (zeros (n := 52)))))

def f_is_pos_zero_D (x64 : (BitVec 64)) : Bool :=
  let (sign, exp, mant) := (fsplit_D x64)
  ((sign == (zeros (n := 1))) && ((exp == (zeros (n := 11))) && (mant == (zeros (n := 52)))))

def f_is_pos_subnorm_D (x64 : (BitVec 64)) : Bool :=
  let (sign, exp, mant) := (fsplit_D x64)
  ((sign == (zeros (n := 1))) && ((exp == (zeros (n := 11))) && (mant != (zeros (n := 52)))))

def f_is_pos_norm_D (x64 : (BitVec 64)) : Bool :=
  let (sign, exp, mant) := (fsplit_D x64)
  ((sign == (zeros (n := 1))) && ((exp != (zeros (n := 11))) && (exp != (ones (n := 11)))))

def f_is_pos_inf_D (x64 : (BitVec 64)) : Bool :=
  let (sign, exp, mant) := (fsplit_D x64)
  ((sign == (zeros (n := 1))) && ((exp == (ones (n := 11))) && (mant == (zeros (n := 52)))))

def f_is_SNaN_D (x64 : (BitVec 64)) : Bool :=
  let (sign, exp, mant) := (fsplit_D x64)
  ((exp == (ones (n := 11))) && (((BitVec.access mant 51) == 0#1) && (mant != (zeros (n := 52)))))

def f_is_QNaN_D (x64 : (BitVec 64)) : Bool :=
  let (sign, exp, mant) := (fsplit_D x64)
  ((exp == (ones (n := 11))) && ((BitVec.access mant 51) == 1#1))

def f_is_NaN_D (x64 : (BitVec 64)) : Bool :=
  let (sign, exp, mant) := (fsplit_D x64)
  ((exp == (ones (n := 11))) && (mant != (zeros (n := 52))))

def negate_D (x64 : (BitVec 64)) : (BitVec 64) :=
  let (sign, exp, mant) := (fsplit_D x64)
  let new_sign :=
    if ((sign == 0#1) : Bool)
    then 1#1
    else 0#1
  (fmake_D new_sign exp mant)

def feq_quiet_D (v1 : (BitVec 64)) (v2 : (BitVec 64)) : (Bool × (BitVec 5)) :=
  let (s1, e1, m1) := (fsplit_D v1)
  let (s2, e2, m2) := (fsplit_D v2)
  let v1Is0 := ((f_is_neg_zero_D v1) || (f_is_pos_zero_D v1))
  let v2Is0 := ((f_is_neg_zero_D v2) || (f_is_pos_zero_D v2))
  let result := ((v1 == v2) || (v1Is0 && v2Is0))
  let fflags :=
    if (((f_is_SNaN_D v1) || (f_is_SNaN_D v2)) : Bool)
    then (nvFlag ())
    else (zeros (n := 5))
  (result, fflags)

/-- Type quantifiers: k_ex1822280_ : Bool -/
def flt_D (v1 : (BitVec 64)) (v2 : (BitVec 64)) (is_quiet : Bool) : (Bool × (BitVec 5)) :=
  let (s1, e1, m1) := (fsplit_D v1)
  let (s2, e2, m2) := (fsplit_D v2)
  let result : Bool :=
    if (((s1 == 0#1) && (s2 == 0#1)) : Bool)
    then
      (if ((e1 == e2) : Bool)
      then ((BitVec.toNatInt m1) <b (BitVec.toNatInt m2))
      else ((BitVec.toNatInt e1) <b (BitVec.toNatInt e2)))
    else
      (if (((s1 == 0#1) && (s2 == 1#1)) : Bool)
      then false
      else
        (if (((s1 == 1#1) && (s2 == 0#1)) : Bool)
        then true
        else
          (if ((e1 == e2) : Bool)
          then ((BitVec.toNatInt m1) >b (BitVec.toNatInt m2))
          else ((BitVec.toNatInt e1) >b (BitVec.toNatInt e2)))))
  let fflags :=
    if (is_quiet : Bool)
    then
      (if (((f_is_SNaN_D v1) || (f_is_SNaN_D v2)) : Bool)
      then (nvFlag ())
      else (zeros (n := 5)))
    else
      (if (((f_is_NaN_D v1) || (f_is_NaN_D v2)) : Bool)
      then (nvFlag ())
      else (zeros (n := 5)))
  (result, fflags)

/-- Type quantifiers: k_ex1822281_ : Bool -/
def fle_D (v1 : (BitVec 64)) (v2 : (BitVec 64)) (is_quiet : Bool) : (Bool × (BitVec 5)) :=
  let (s1, e1, m1) := (fsplit_D v1)
  let (s2, e2, m2) := (fsplit_D v2)
  let v1Is0 := ((f_is_neg_zero_D v1) || (f_is_pos_zero_D v1))
  let v2Is0 := ((f_is_neg_zero_D v2) || (f_is_pos_zero_D v2))
  let result : Bool :=
    if (((s1 == 0#1) && (s2 == 0#1)) : Bool)
    then
      (if ((e1 == e2) : Bool)
      then ((BitVec.toNatInt m1) ≤b (BitVec.toNatInt m2))
      else ((BitVec.toNatInt e1) <b (BitVec.toNatInt e2)))
    else
      (if (((s1 == 0#1) && (s2 == 1#1)) : Bool)
      then (v1Is0 && v2Is0)
      else
        (if (((s1 == 1#1) && (s2 == 0#1)) : Bool)
        then true
        else
          (if ((e1 == e2) : Bool)
          then ((BitVec.toNatInt m1) ≥b (BitVec.toNatInt m2))
          else ((BitVec.toNatInt e1) >b (BitVec.toNatInt e2)))))
  let fflags :=
    if (is_quiet : Bool)
    then
      (if (((f_is_SNaN_D v1) || (f_is_SNaN_D v2)) : Bool)
      then (nvFlag ())
      else (zeros (n := 5)))
    else
      (if (((f_is_NaN_D v1) || (f_is_NaN_D v2)) : Bool)
      then (nvFlag ())
      else (zeros (n := 5)))
  (result, fflags)

def f_madd_type_mnemonic_D_backwards (arg_ : String) : SailM f_madd_op_D := do
  match arg_ with
  | "fmadd.d" => (pure FMADD_D)
  | "fmsub.d" => (pure FMSUB_D)
  | "fnmsub.d" => (pure FNMSUB_D)
  | "fnmadd.d" => (pure FNMADD_D)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_madd_type_mnemonic_D_forwards_matches (arg_ : f_madd_op_D) : Bool :=
  match arg_ with
  | .FMADD_D => true
  | .FMSUB_D => true
  | .FNMSUB_D => true
  | .FNMADD_D => true

def f_madd_type_mnemonic_D_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fmadd.d" => true
  | "fmsub.d" => true
  | "fnmsub.d" => true
  | "fnmadd.d" => true
  | _ => false

def f_bin_rm_type_mnemonic_D_backwards (arg_ : String) : SailM f_bin_rm_op_D := do
  match arg_ with
  | "fadd.d" => (pure FADD_D)
  | "fsub.d" => (pure FSUB_D)
  | "fmul.d" => (pure FMUL_D)
  | "fdiv.d" => (pure FDIV_D)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_bin_rm_type_mnemonic_D_forwards_matches (arg_ : f_bin_rm_op_D) : Bool :=
  match arg_ with
  | .FADD_D => true
  | .FSUB_D => true
  | .FMUL_D => true
  | .FDIV_D => true

def f_bin_rm_type_mnemonic_D_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fadd.d" => true
  | "fsub.d" => true
  | "fmul.d" => true
  | "fdiv.d" => true
  | _ => false

def f_un_rm_ff_type_mnemonic_D_backwards (arg_ : String) : SailM f_un_rm_ff_op_D := do
  match arg_ with
  | "fsqrt.d" => (pure FSQRT_D)
  | "fcvt.s.d" => (pure FCVT_S_D)
  | "fcvt.d.s" => (pure FCVT_D_S)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_un_rm_ff_type_mnemonic_D_forwards_matches (arg_ : f_un_rm_ff_op_D) : Bool :=
  match arg_ with
  | .FSQRT_D => true
  | .FCVT_S_D => true
  | .FCVT_D_S => true

def f_un_rm_ff_type_mnemonic_D_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fsqrt.d" => true
  | "fcvt.s.d" => true
  | "fcvt.d.s" => true
  | _ => false

def f_un_rm_fx_type_mnemonic_D_backwards (arg_ : String) : SailM f_un_rm_fx_op_D := do
  match arg_ with
  | "fcvt.w.d" => (pure FCVT_W_D)
  | "fcvt.wu.d" => (pure FCVT_WU_D)
  | "fcvt.l.d" => (pure FCVT_L_D)
  | "fcvt.lu.d" => (pure FCVT_LU_D)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_un_rm_fx_type_mnemonic_D_forwards_matches (arg_ : f_un_rm_fx_op_D) : Bool :=
  match arg_ with
  | .FCVT_W_D => true
  | .FCVT_WU_D => true
  | .FCVT_L_D => true
  | .FCVT_LU_D => true

def f_un_rm_fx_type_mnemonic_D_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fcvt.w.d" => true
  | "fcvt.wu.d" => true
  | "fcvt.l.d" => true
  | "fcvt.lu.d" => true
  | _ => false

def f_un_rm_xf_type_mnemonic_D_backwards (arg_ : String) : SailM f_un_rm_xf_op_D := do
  match arg_ with
  | "fcvt.d.w" => (pure FCVT_D_W)
  | "fcvt.d.wu" => (pure FCVT_D_WU)
  | "fcvt.d.l" => (pure FCVT_D_L)
  | "fcvt.d.lu" => (pure FCVT_D_LU)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_un_rm_xf_type_mnemonic_D_forwards_matches (arg_ : f_un_rm_xf_op_D) : Bool :=
  match arg_ with
  | .FCVT_D_W => true
  | .FCVT_D_WU => true
  | .FCVT_D_L => true
  | .FCVT_D_LU => true

def f_un_rm_xf_type_mnemonic_D_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fcvt.d.w" => true
  | "fcvt.d.wu" => true
  | "fcvt.d.l" => true
  | "fcvt.d.lu" => true
  | _ => false

def f_bin_f_type_mnemonic_D_backwards (arg_ : String) : SailM f_bin_f_op_D := do
  match arg_ with
  | "fsgnj.d" => (pure FSGNJ_D)
  | "fsgnjn.d" => (pure FSGNJN_D)
  | "fsgnjx.d" => (pure FSGNJX_D)
  | "fmin.d" => (pure FMIN_D)
  | "fmax.d" => (pure FMAX_D)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_bin_f_type_mnemonic_D_forwards_matches (arg_ : f_bin_f_op_D) : Bool :=
  match arg_ with
  | .FSGNJ_D => true
  | .FSGNJN_D => true
  | .FSGNJX_D => true
  | .FMIN_D => true
  | .FMAX_D => true

def f_bin_f_type_mnemonic_D_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fsgnj.d" => true
  | "fsgnjn.d" => true
  | "fsgnjx.d" => true
  | "fmin.d" => true
  | "fmax.d" => true
  | _ => false

def f_bin_x_type_mnemonic_D_backwards (arg_ : String) : SailM f_bin_x_op_D := do
  match arg_ with
  | "feq.d" => (pure FEQ_D)
  | "flt.d" => (pure FLT_D)
  | "fle.d" => (pure FLE_D)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_bin_x_type_mnemonic_D_forwards_matches (arg_ : f_bin_x_op_D) : Bool :=
  match arg_ with
  | .FEQ_D => true
  | .FLT_D => true
  | .FLE_D => true

def f_bin_x_type_mnemonic_D_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "feq.d" => true
  | "flt.d" => true
  | "fle.d" => true
  | _ => false

def f_un_x_type_mnemonic_D_backwards (arg_ : String) : SailM f_un_x_op_D := do
  match arg_ with
  | "fmv.x.d" => (pure FMV_X_D)
  | "fclass.d" => (pure FCLASS_D)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_un_x_type_mnemonic_D_forwards_matches (arg_ : f_un_x_op_D) : Bool :=
  match arg_ with
  | .FMV_X_D => true
  | .FCLASS_D => true

def f_un_x_type_mnemonic_D_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fmv.x.d" => true
  | "fclass.d" => true
  | _ => false

def f_un_f_type_mnemonic_D_backwards (arg_ : String) : SailM f_un_f_op_D := do
  match arg_ with
  | "fmv.d.x" => (pure FMV_D_X)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_un_f_type_mnemonic_D_forwards_matches (arg_ : f_un_f_op_D) : Bool :=
  match arg_ with
  | .FMV_D_X => true

def f_un_f_type_mnemonic_D_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fmv.d.x" => true
  | _ => false

