import SailRV32.SailRV32
import SailRV32.Vector

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

def not_bit (b : (BitVec 1)) : (BitVec 1) :=
  if ((b == 1#1) : Bool)
  then 0#1
  else 1#1

def print_log_instr (message : String) (_pc : (BitVec 64)) : Unit :=
  (print_endline message)

def print_step (_ : Unit) : Unit :=
  ()

def get_config_print_instr (_ : Unit) : Bool :=
  false

def get_config_print_clint (_ : Unit) : Bool :=
  false

def get_config_print_exception (_ : Unit) : Bool :=
  false

def get_config_print_interrupt (_ : Unit) : Bool :=
  false

def get_config_print_trigger (_ : Unit) : Bool :=
  false

def get_config_print_htif (_ : Unit) : Bool :=
  false

def get_config_print_pma (_ : Unit) : Bool :=
  false

def get_config_print_pmp (_ : Unit) : Bool :=
  false

def get_config_rvfi (_ : Unit) : Bool :=
  false

def get_config_use_abi_names (_ : Unit) : Bool :=
  false

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, m : Nat, m ≥ 0, m ≥ k_n -/
def sign_extend {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.signExtend v m)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, m : Nat, m ≥ 0, m ≥ k_n -/
def zero_extend {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.zeroExtend v m)

/-- Type quantifiers: n : Nat, n ≥ 0, n ≥ 0 -/
def zeros {n : _} : (BitVec n) :=
  (BitVec.zero n)

/-- Type quantifiers: n : Nat, n ≥ 0, n ≥ 0 -/
def ones {n : _} : (BitVec n) :=
  (sail_ones n)

/-- Type quantifiers: m : Nat, m ≥ 0, k_n : Nat, k_n ≥ 0, m ≥ 0 ∧ m ≤ k_n -/
def trunc {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.truncate v m)

/-- Type quantifiers: k_ex1818739_ : Bool -/
def bool_bit_forwards (arg_ : Bool) : (BitVec 1) :=
  match arg_ with
  | true => 1#1
  | false => 0#1

def bool_bit_backwards (arg_ : (BitVec 1)) : Bool :=
  match arg_ with
  | 1 => true
  | _ => false

/-- Type quantifiers: k_ex1818740_ : Bool -/
def bool_bit_forwards_matches (arg_ : Bool) : Bool :=
  match arg_ with
  | true => true
  | false => true

def bool_bit_backwards_matches (arg_ : (BitVec 1)) : Bool :=
  match arg_ with
  | 1 => true
  | 0 => true
  | _ => false

/-- Type quantifiers: k_ex1818741_ : Bool -/
def bool_int_forwards (arg_ : Bool) : Int :=
  match arg_ with
  | false => 0
  | true => 1

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [0, 1] -/
def bool_int_backwards (arg_ : Nat) : Bool :=
  match arg_ with
  | 0 => false
  | _ => true

/-- Type quantifiers: k_ex1818743_ : Bool -/
def bool_int_forwards_matches (arg_ : Bool) : Bool :=
  match arg_ with
  | false => true
  | true => true

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [0, 1] -/
def bool_int_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 0 => true
  | 1 => true
  | _ => false

/-- Type quantifiers: k_ex1818745_ : Bool -/
def bool_to_bit (x : Bool) : (BitVec 1) :=
  (bool_bit_forwards x)

def bit_to_bool (x : (BitVec 1)) : Bool :=
  (bool_bit_backwards x)

/-- Type quantifiers: l : Nat, l ≥ 0, n : Nat, l ≥ 0 ∧ 0 ≤ n ∧ n < (2 ^ l) -/
def to_bits {l : _} (n : Nat) : (BitVec l) :=
  (get_slice_int l n 0)

/-- Type quantifiers: n : Int, l : Nat, l ≥ 0, l ≥ 0 -/
def to_bits_checked {l : _} (n : Int) : SailM (BitVec l) := do
  let bv := (get_slice_int l n 0)
  «assert» ((BitVec.toNatInt bv) == n) (HAppend.hAppend "Couldn't convert integer "
    (HAppend.hAppend (Int.repr n)
      (HAppend.hAppend " to " (HAppend.hAppend (Int.repr l) " bits without overflow."))))
  (pure bv)

/-- Type quantifiers: n : Int, l : Nat, l ≥ 0, l ≥ 0 -/
def to_bits_truncate {l : _} (n : Int) : (BitVec l) :=
  (get_slice_int l n 0)

/-- Type quantifiers: n : Int, l : Nat, l ≥ 0, l ≥ 0 -/
def to_bits_unsafe {l : _} (n : Int) : (BitVec l) :=
  (get_slice_int l n 0)

def undefined_Signedness (_ : Unit) : SailM Signedness := do
  (internal_pick [Signed, Unsigned])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def Signedness_of_num (arg_ : Nat) : Signedness :=
  match arg_ with
  | 0 => Signed
  | _ => Unsigned

def num_of_Signedness (arg_ : Signedness) : Int :=
  match arg_ with
  | .Signed => 0
  | .Unsigned => 1

def undefined_VectorHalf (_ : Unit) : SailM VectorHalf := do
  (internal_pick [High, Low])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def VectorHalf_of_num (arg_ : Nat) : VectorHalf :=
  match arg_ with
  | 0 => High
  | _ => Low

def num_of_VectorHalf (arg_ : VectorHalf) : Int :=
  match arg_ with
  | .High => 0
  | .Low => 1

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def zopz0zI_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toInt x) <b (BitVec.toInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def zopz0zK_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toInt x) >b (BitVec.toInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def zopz0zIzJ_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toInt x) ≤b (BitVec.toInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def zopz0zKzJ_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toInt x) ≥b (BitVec.toInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zopz0zI_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNatInt x) <b (BitVec.toNatInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zopz0zK_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNatInt x) >b (BitVec.toNatInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zopz0zIzJ_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNatInt x) ≤b (BitVec.toNatInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zopz0zKzJ_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNatInt x) ≥b (BitVec.toNatInt y))

/-- Type quantifiers: k_ex1818750_ : Bool, k_ex1818749_ : Bool -/
def zopz0zJzJzK (x : Bool) (y : Bool) : Bool :=
  ((not x) || y)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_n : Nat, k_n ≥ 0, k_n ≥ 1 -/
def shift_bits_right_arith (value : (BitVec k_n)) (shift : (BitVec k_m)) : (BitVec k_n) :=
  (BitVec.sshiftRight value (BitVec.toNatInt shift))

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, shift : Nat, k_m ≥ shift ∧ shift ≥ 0 -/
def rotater (value : (BitVec k_m)) (shift : Nat) : (BitVec k_m) :=
  ((value >>> shift) ||| (value <<< ((Sail.BitVec.length value) -i shift)))

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, shift : Nat, k_m ≥ shift ∧ shift ≥ 0 -/
def rotatel (value : (BitVec k_m)) (shift : Nat) : (BitVec k_m) :=
  ((value <<< shift) ||| (value >>> ((Sail.BitVec.length value) -i shift)))

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_n : Nat, k_n ≥ 0, k_n ≥ 0 ∧ k_m ≥ (2 ^ k_n) -/
def rotate_bits_right (value : (BitVec k_m)) (shift : (BitVec k_n)) : (BitVec k_m) :=
  (rotater value (BitVec.toNatInt shift))

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_n : Nat, k_n ≥ 0, k_n ≥ 0 ∧ k_m ≥ (2 ^ k_n) -/
def rotate_bits_left (value : (BitVec k_m)) (shift : (BitVec k_n)) : (BitVec k_m) :=
  (rotatel value (BitVec.toNatInt shift))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def reverse_bits (xs : (BitVec k_n)) : (BitVec k_n) := Id.run do
  let ys : (BitVec k_n) := (zeros (n := (Sail.BitVec.length xs)))
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length ys) -i 1)
  let mut loop_vars := ys
  for i in [loop_i_lower:loop_i_upper:1]i do
    let ys := loop_vars
    loop_vars := (BitVec.update ys i (BitVec.access xs (((Sail.BitVec.length ys) -i 1) -i i)))
  (pure loop_vars)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ≥ 0 -/
def hex_bits_str (x : (BitVec k_n)) : String :=
  (BitVec.toFormatted
    (zero_extend
      (m := ((3 -i (Int.tmod ((Sail.BitVec.length x) +i 3) 4)) +i (Sail.BitVec.length x))) x))

/-- Type quantifiers: k_b : Bool, k_b -/
def static_assert (x_0 : Bool) : Unit :=
  ()

