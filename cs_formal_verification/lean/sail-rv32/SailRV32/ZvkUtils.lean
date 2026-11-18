import SailRV32.Prelude
import SailRV32.TypesKext

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

def undefined_zvk_vsha2_funct6 (_ : Unit) : SailM zvk_vsha2_funct6 := do
  (internal_pick [ZVK_VSHA2CH_VV, ZVK_VSHA2CL_VV])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def zvk_vsha2_funct6_of_num (arg_ : Nat) : zvk_vsha2_funct6 :=
  match arg_ with
  | 0 => ZVK_VSHA2CH_VV
  | _ => ZVK_VSHA2CL_VV

def num_of_zvk_vsha2_funct6 (arg_ : zvk_vsha2_funct6) : Int :=
  match arg_ with
  | .ZVK_VSHA2CH_VV => 0
  | .ZVK_VSHA2CL_VV => 1

/-- Type quantifiers: SEW : Nat, SEW ≥ 0, List.elem SEW [32, 64] -/
def zvk_sig0 (x : (BitVec k_n)) (SEW : Nat) : (BitVec SEW) :=
  match SEW with
  | 32 => ((rotater x 7) ^^^ ((rotater x 18) ^^^ (x >>> 3)))
  | _ => ((rotater x 1) ^^^ ((rotater x 8) ^^^ (x >>> 7)))

/-- Type quantifiers: SEW : Nat, SEW ≥ 0, List.elem SEW [32, 64] -/
def zvk_sig1 (x : (BitVec k_n)) (SEW : Nat) : (BitVec SEW) :=
  match SEW with
  | 32 => ((rotater x 17) ^^^ ((rotater x 19) ^^^ (x >>> 10)))
  | _ => ((rotater x 19) ^^^ ((rotater x 61) ^^^ (x >>> 6)))

/-- Type quantifiers: SEW : Nat, SEW ≥ 0, List.elem SEW [32, 64] -/
def zvk_sum0 (x : (BitVec k_n)) (SEW : Nat) : (BitVec SEW) :=
  match SEW with
  | 32 => ((rotater x 2) ^^^ ((rotater x 13) ^^^ (rotater x 22)))
  | _ => ((rotater x 28) ^^^ ((rotater x 34) ^^^ (rotater x 39)))

/-- Type quantifiers: SEW : Nat, SEW ≥ 0, List.elem SEW [32, 64] -/
def zvk_sum1 (x : (BitVec k_n)) (SEW : Nat) : (BitVec SEW) :=
  match SEW with
  | 32 => ((rotater x 6) ^^^ ((rotater x 11) ^^^ (rotater x 25)))
  | _ => ((rotater x 14) ^^^ ((rotater x 18) ^^^ (rotater x 41)))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ≥ 0 -/
def zvk_ch (x : (BitVec k_n)) (y : (BitVec k_n)) (z : (BitVec k_n)) : (BitVec k_n) :=
  ((x &&& y) ^^^ ((Complement.complement x) &&& z))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ≥ 0 -/
def zvk_maj (x : (BitVec k_n)) (y : (BitVec k_n)) (z : (BitVec k_n)) : (BitVec k_n) :=
  ((x &&& y) ^^^ ((x &&& z) ^^^ (y &&& z)))

def undefined_zvk_vsm4r_funct6 (_ : Unit) : SailM zvk_vsm4r_funct6 := do
  (internal_pick [ZVK_VSM4R_VV, ZVK_VSM4R_VS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def zvk_vsm4r_funct6_of_num (arg_ : Nat) : zvk_vsm4r_funct6 :=
  match arg_ with
  | 0 => ZVK_VSM4R_VV
  | _ => ZVK_VSM4R_VS

def num_of_zvk_vsm4r_funct6 (arg_ : zvk_vsm4r_funct6) : Int :=
  match arg_ with
  | .ZVK_VSM4R_VV => 0
  | .ZVK_VSM4R_VS => 1

def zvk_round_key (X : (BitVec 32)) (S : (BitVec 32)) : (BitVec 32) :=
  (X ^^^ (S ^^^ ((rotatel S 13) ^^^ (rotatel S 23))))

def zvk_sm4_round (X : (BitVec 32)) (S : (BitVec 32)) : (BitVec 32) :=
  (X ^^^ (S ^^^ ((rotatel S 2) ^^^ ((rotatel S 10) ^^^ ((rotatel S 18) ^^^ (rotatel S 24))))))

def zvksed_ck : (Vector (BitVec 32) 32) :=
  #v[0x646B7279#32, 0x484F565D#32, 0x2C333A41#32, 0x10171E25#32, 0xF4FB0209#32, 0xD8DFE6ED#32, 0xBCC3CAD1#32, 0xA0A7AEB5#32, 0x848B9299#32, 0x686F767D#32, 0x4C535A61#32, 0x30373E45#32, 0x141B2229#32, 0xF8FF060D#32, 0xDCE3EAF1#32, 0xC0C7CED5#32, 0xA4ABB2B9#32, 0x888F969D#32, 0x6C737A81#32, 0x50575E65#32, 0x343B4249#32, 0x181F262D#32, 0xFC030A11#32, 0xE0E7EEF5#32, 0xC4CBD2D9#32, 0xA8AFB6BD#32, 0x8C939AA1#32, 0x70777E85#32, 0x545B6269#32, 0x383F464D#32, 0x1C232A31#32, 0x00070E15#32]

def zvksed_box_lookup (x : (BitVec 5)) (table : (Vector (BitVec 32) 32)) : (BitVec 32) :=
  (GetElem?.getElem! table (31 -i (BitVec.toNatInt x)))

def zvk_sm4_sbox (x : (BitVec 5)) : (BitVec 32) :=
  (zvksed_box_lookup x zvksed_ck)

def zvk_sm4_subword (x : (BitVec 32)) : (BitVec 32) :=
  ((sm4_sbox (Sail.BitVec.extractLsb x 31 24)) +++ ((sm4_sbox (Sail.BitVec.extractLsb x 23 16)) +++ ((sm4_sbox
          (Sail.BitVec.extractLsb x 15 8)) +++ (sm4_sbox (Sail.BitVec.extractLsb x 7 0)))))

def zvk_p0 (X : (BitVec 32)) : (BitVec 32) :=
  (X ^^^ ((rotatel X 9) ^^^ (rotatel X 17)))

def zvk_p1 (X : (BitVec 32)) : (BitVec 32) :=
  (X ^^^ ((rotatel X 15) ^^^ (rotatel X 23)))

def zvk_sh_w (A : (BitVec 32)) (B : (BitVec 32)) (C : (BitVec 32)) (D : (BitVec 32)) (E : (BitVec 32)) : (BitVec 32) :=
  ((zvk_p1 (A ^^^ (B ^^^ (rotatel C 15)))) ^^^ ((rotatel D 7) ^^^ E))

def zvk_ff1 (X : (BitVec 32)) (Y : (BitVec 32)) (Z : (BitVec 32)) : (BitVec 32) :=
  (X ^^^ (Y ^^^ Z))

def zvk_ff2 (X : (BitVec 32)) (Y : (BitVec 32)) (Z : (BitVec 32)) : (BitVec 32) :=
  ((X &&& Y) ||| ((X &&& Z) ||| (Y &&& Z)))

/-- Type quantifiers: J : Nat, 0 ≤ J -/
def zvk_ff_j (X : (BitVec 32)) (Y : (BitVec 32)) (Z : (BitVec 32)) (J : Nat) : (BitVec 32) :=
  if ((J ≤b 15) : Bool)
  then (zvk_ff1 X Y Z)
  else (zvk_ff2 X Y Z)

def zvk_gg1 (X : (BitVec 32)) (Y : (BitVec 32)) (Z : (BitVec 32)) : (BitVec 32) :=
  (X ^^^ (Y ^^^ Z))

def zvk_gg2 (X : (BitVec 32)) (Y : (BitVec 32)) (Z : (BitVec 32)) : (BitVec 32) :=
  ((X &&& Y) ||| ((Complement.complement X) &&& Z))

/-- Type quantifiers: J : Nat, 0 ≤ J -/
def zvk_gg_j (X : (BitVec 32)) (Y : (BitVec 32)) (Z : (BitVec 32)) (J : Nat) : (BitVec 32) :=
  if ((J ≤b 15) : Bool)
  then (zvk_gg1 X Y Z)
  else (zvk_gg2 X Y Z)

/-- Type quantifiers: J : Nat, 0 ≤ J -/
def zvk_t_j (J : Nat) : (BitVec 32) :=
  if ((J ≤b 15) : Bool)
  then 0x79CC4519#32
  else 0x7A879D8A#32

/-- Type quantifiers: j : Nat, 0 ≤ j -/
def zvk_sm3_round (A_H : (Vector (BitVec 32) 8)) (w : (BitVec 32)) (x : (BitVec 32)) (j : Nat) : (Vector (BitVec 32) 8) :=
  let t_j := (rotatel (zvk_t_j j) (Int.tmod j 32))
  let ss1 :=
    (rotatel (((rotatel (GetElem?.getElem! A_H 0) 12) + (GetElem?.getElem! A_H 4)) + t_j) 7)
  let ss2 := (ss1 ^^^ (rotatel (GetElem?.getElem! A_H 0) 12))
  let tt1 :=
    ((((zvk_ff_j (GetElem?.getElem! A_H 0) (GetElem?.getElem! A_H 1) (GetElem?.getElem! A_H 2) j) + (GetElem?.getElem!
            A_H 3)) + ss2) + x)
  let tt2 :=
    ((((zvk_gg_j (GetElem?.getElem! A_H 4) (GetElem?.getElem! A_H 5) (GetElem?.getElem! A_H 6) j) + (GetElem?.getElem!
            A_H 7)) + ss1) + w)
  let A1 := tt1
  let C1 := (rotatel (GetElem?.getElem! A_H 1) 9)
  let E1 := (zvk_p0 tt2)
  let G1 := (rotatel (GetElem?.getElem! A_H 5) 19)
  #v[A1, (GetElem?.getElem! A_H 0), C1, (GetElem?.getElem! A_H 2), E1, (GetElem?.getElem! A_H 4), G1, (GetElem?.getElem!
      A_H 6)]

def undefined_zvk_vaesdf_funct6 (_ : Unit) : SailM zvk_vaesdf_funct6 := do
  (internal_pick [ZVK_VAESDF_VV, ZVK_VAESDF_VS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def zvk_vaesdf_funct6_of_num (arg_ : Nat) : zvk_vaesdf_funct6 :=
  match arg_ with
  | 0 => ZVK_VAESDF_VV
  | _ => ZVK_VAESDF_VS

def num_of_zvk_vaesdf_funct6 (arg_ : zvk_vaesdf_funct6) : Int :=
  match arg_ with
  | .ZVK_VAESDF_VV => 0
  | .ZVK_VAESDF_VS => 1

def undefined_zvk_vaesdm_funct6 (_ : Unit) : SailM zvk_vaesdm_funct6 := do
  (internal_pick [ZVK_VAESDM_VV, ZVK_VAESDM_VS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def zvk_vaesdm_funct6_of_num (arg_ : Nat) : zvk_vaesdm_funct6 :=
  match arg_ with
  | 0 => ZVK_VAESDM_VV
  | _ => ZVK_VAESDM_VS

def num_of_zvk_vaesdm_funct6 (arg_ : zvk_vaesdm_funct6) : Int :=
  match arg_ with
  | .ZVK_VAESDM_VV => 0
  | .ZVK_VAESDM_VS => 1

def undefined_zvk_vaesef_funct6 (_ : Unit) : SailM zvk_vaesef_funct6 := do
  (internal_pick [ZVK_VAESEF_VV, ZVK_VAESEF_VS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def zvk_vaesef_funct6_of_num (arg_ : Nat) : zvk_vaesef_funct6 :=
  match arg_ with
  | 0 => ZVK_VAESEF_VV
  | _ => ZVK_VAESEF_VS

def num_of_zvk_vaesef_funct6 (arg_ : zvk_vaesef_funct6) : Int :=
  match arg_ with
  | .ZVK_VAESEF_VV => 0
  | .ZVK_VAESEF_VS => 1

def undefined_zvk_vaesem_funct6 (_ : Unit) : SailM zvk_vaesem_funct6 := do
  (internal_pick [ZVK_VAESEM_VV, ZVK_VAESEM_VS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def zvk_vaesem_funct6_of_num (arg_ : Nat) : zvk_vaesem_funct6 :=
  match arg_ with
  | 0 => ZVK_VAESEM_VV
  | _ => ZVK_VAESEM_VS

def num_of_zvk_vaesem_funct6 (arg_ : zvk_vaesem_funct6) : Int :=
  match arg_ with
  | .ZVK_VAESEM_VV => 0
  | .ZVK_VAESEM_VS => 1

