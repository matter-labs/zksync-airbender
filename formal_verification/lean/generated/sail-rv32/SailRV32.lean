import Sail
import SailRV32.Defs
import SailRV32.SpecializationArchSem
import SailRV32.FakeReal
import SailRV32.SailPlatform

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ArchSem

namespace SailRV32

open ArchSem

namespace Functions

open vector_support
open uop
open stateen_bit
open sopw
open sop
open ropw
open rop
open regno
open regidx
open option
open iop
open instruction
open extop_zbb
open extension
open bropw_zbb
open brop_zbb
open breakpoint_cause
open bop
open WaitReason
open VectorHalf
open Signedness
open Register
open Privilege
open ExecutionResult
open ExceptionType

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

def num_of_vector_support (arg_ : vector_support) : Int :=
  match arg_ with
  | .Disabled => 0
  | .Integer => 1
  | .Float_single => 2
  | .Float_double => 3
  | .Full => 4

def vector_support_ge (x : vector_support) (y : vector_support) : Bool :=
  ((num_of_vector_support x) ≥b (num_of_vector_support y))

/-- Type quantifiers: n : Nat, n ≥ 0, n ≥ 0 -/
def sail_ones (n : Nat) : (BitVec n) :=
  (Complement.complement (BitVec.zero n))

/-- Type quantifiers: k_p : Bool -/
def not (b : Bool) : Bool :=
  (! b)

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

/-- Type quantifiers: k_ex433363_ : Bool -/
def bool_bit_forwards (arg_ : Bool) : (BitVec 1) :=
  match arg_ with
  | true => 1#1
  | false => 0#1

def bool_bit_backwards (arg_ : (BitVec 1)) : Bool :=
  match arg_ with
  | 1 => true
  | _ => false

/-- Type quantifiers: k_ex433369_ : Bool -/
def bool_to_bit (x : Bool) : (BitVec 1) :=
  (bool_bit_forwards x)

def bit_to_bool (x : (BitVec 1)) : Bool :=
  (bool_bit_backwards x)

/-- Type quantifiers: l : Nat, l ≥ 0, n : Nat, l ≥ 0 ∧ 0 ≤ n ∧ n < (2 ^ l) -/
def to_bits {l : _} (n : Nat) : (BitVec l) :=
  (get_slice_int l n 0)

/-- Type quantifiers: n : Int, l : Nat, l ≥ 0, l ≥ 0 -/
def to_bits_truncate {l : _} (n : Int) : (BitVec l) :=
  (get_slice_int l n 0)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def zopz0zI_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toInt x) <b (BitVec.toInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def zopz0zKzJ_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toInt x) ≥b (BitVec.toInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zopz0zI_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNatInt x) <b (BitVec.toNatInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zopz0zKzJ_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNatInt x) ≥b (BitVec.toNatInt y))

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_n : Nat, k_n ≥ 0, k_n ≥ 1 -/
def shift_bits_right_arith (value : (BitVec k_n)) (shift : (BitVec k_m)) : (BitVec k_n) :=
  (BitVec.sshiftRight value (BitVec.toNatInt shift))

def log2_xlen := 5

def xlen := 32

def flen := (8 *i 8)

def vector_support_level : vector_support := Float_single

/-- Type quantifiers: l : Nat, l ≥ 0, l > 0 -/
def mult_to_bits_half {l : _} (sign1 : Signedness) (sign2 : Signedness) (rs1_bits : (BitVec l)) (rs2_bits : (BitVec l)) (result_part : VectorHalf) : (BitVec l) :=
  let rs1_int : Int :=
    match sign1 with
    | .Signed => (BitVec.toInt rs1_bits)
    | .Unsigned => (BitVec.toNatInt rs1_bits)
  let rs2_int : Int :=
    match sign2 with
    | .Signed => (BitVec.toInt rs2_bits)
    | .Unsigned => (BitVec.toNatInt rs2_bits)
  let result_wide := (to_bits_truncate (l := (2 *i l)) (rs1_int *i rs2_int))
  match result_part with
  | .High => (Sail.BitVec.extractLsb result_wide ((2 *i l) -i 1) l)
  | .Low => (Sail.BitVec.extractLsb result_wide (l -i 1) 0)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ≥ 0 ∧ (k_m % 8) = 0 -/
def rev8 (input : (BitVec k_m)) : (BitVec k_m) := Id.run do
  let output : (BitVec k_m) := (zeros (n := (Sail.BitVec.length input)))
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length output) -i 8)
  let mut loop_vars := output
  for i in [loop_i_lower:loop_i_upper:8]i do
    let output := loop_vars
    loop_vars :=
      (Sail.BitVec.updateSubrange output (i +i 7) i
        (Sail.BitVec.extractLsb input (((Sail.BitVec.length output) -i i) -i 1)
          (((Sail.BitVec.length output) -i i) -i 8)))
  (pure loop_vars)

def plat_reservation_set_size_exp : Nat := 3

def undefined_Privilege (_ : Unit) : SailM Privilege := do
  (internal_pick [User, VirtualUser, Supervisor, VirtualSupervisor, Machine])

def _get_MEnvcfg_ADUE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _get_MEnvcfg_DTE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _get_MEnvcfg_LPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_MEnvcfg_PBMTE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _get_MEnvcfg_SSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_MEnvcfg_STCE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def hartSupports_measure (ext : extension) : Int :=
  match ext with
  | .Ext_D => 1
  | .Ext_Ssu64xl => 1
  | .Ext_Zvkn => 1
  | .Ext_Zvks => 1
  | .Ext_Sspm => 1
  | .Ext_Supm => 1
  | .Ext_C => 2
  | .Ext_Zvknc => 2
  | .Ext_Zvkng => 2
  | .Ext_Zvksc => 2
  | .Ext_Zvksg => 2
  | _ => 0

def hartSupports (merge_var : extension) : Bool :=
  match merge_var with
  | .Ext_M => true
  | .Ext_A => true
  | .Ext_F => true
  | .Ext_D => (true && (hartSupports Ext_F))
  | .Ext_B => true
  | .Ext_V => ((8 ≥b 7) && (vector_support_ge vector_support_level Full))
  | .Ext_S => true
  | .Ext_U => true
  | .Ext_H => true
  | .Ext_Sha => true
  | .Ext_Shcounterenw => true
  | .Ext_Shgatpa => true
  | .Ext_Shtvala => true
  | .Ext_Shvsatpa => true
  | .Ext_Shvstvala => true
  | .Ext_Shvstvecd => true
  | .Ext_Zibi => ((sys_enable_experimental_extensions ()) && (true : Bool))
  | .Ext_Zic64b => true
  | .Ext_Zicbom => true
  | .Ext_Zicbop => true
  | .Ext_Zicboz => true
  | .Ext_Zicfilp => true
  | .Ext_Zicfiss => true
  | .Ext_Zicntr => true
  | .Ext_Zicond => true
  | .Ext_Zicsr => true
  | .Ext_Zifencei => true
  | .Ext_Zihintntl => true
  | .Ext_Zihintpause => true
  | .Ext_Zihpm => true
  | .Ext_Zilx => ((sys_enable_experimental_extensions ()) && (true : Bool))
  | .Ext_Zimop => true
  | .Ext_Zmmul => false
  | .Ext_Zaamo => false
  | .Ext_Zabha => true
  | .Ext_Zacas => true
  | .Ext_Zalrsc => false
  | .Ext_Zama16b => true
  | .Ext_Zawrs => true
  | .Ext_Za64rs => ((plat_reservation_set_size_exp ≤b 6) && ((false : Bool) || (true : Bool)))
  | .Ext_Za128rs => ((plat_reservation_set_size_exp ≤b 7) && ((false : Bool) || (true : Bool)))
  | .Ext_Zfa => true
  | .Ext_Zfbfmin => true
  | .Ext_Zfh => true
  | .Ext_Zfhmin => true
  | .Ext_Zfinx => false
  | .Ext_Zdinx => false
  | .Ext_Zca => true
  | .Ext_Zcb => true
  | .Ext_Zcd => true
  | .Ext_Zcf => ((true : Bool) && (xlen == 32))
  | .Ext_Zcmop => true
  | .Ext_C =>
    ((hartSupports Ext_Zca) && (((hartSupports Ext_Zcf) || ((not (hartSupports Ext_F)) || (xlen != 32))) && ((hartSupports
            Ext_Zcd) || (not (hartSupports Ext_D)))))
  | .Ext_Zba => false
  | .Ext_Zbb => false
  | .Ext_Zbc => true
  | .Ext_Zbkb => true
  | .Ext_Zbkc => true
  | .Ext_Zbkx => true
  | .Ext_Zbs => false
  | .Ext_Ziccamoa => true
  | .Ext_Ziccamoc => true
  | .Ext_Ziccif => true
  | .Ext_Zicclsm => true
  | .Ext_Ziccrse => true
  | .Ext_Zknd => true
  | .Ext_Zkne => true
  | .Ext_Zknh => true
  | .Ext_Zkr => true
  | .Ext_Zksed => true
  | .Ext_Zksh => true
  | .Ext_Zkt => true
  | .Ext_Zhinx => false
  | .Ext_Zhinxmin => false
  | .Ext_Zvl32b => (8 ≥b 5)
  | .Ext_Zvl64b => (8 ≥b 6)
  | .Ext_Zvl128b => (8 ≥b 7)
  | .Ext_Zvl256b => (8 ≥b 8)
  | .Ext_Zvl512b => (8 ≥b 9)
  | .Ext_Zvl1024b => (8 ≥b 10)
  | .Ext_Zve32f => ((5 ≥b 5) && (vector_support_ge vector_support_level Float_single))
  | .Ext_Zve32x => ((5 ≥b 5) && (vector_support_ge vector_support_level Integer))
  | .Ext_Zve64d => ((5 ≥b 6) && (vector_support_ge vector_support_level Float_double))
  | .Ext_Zve64f => ((5 ≥b 6) && (vector_support_ge vector_support_level Float_single))
  | .Ext_Zve64x => ((5 ≥b 6) && (vector_support_ge vector_support_level Integer))
  | .Ext_Zvabd => ((sys_enable_experimental_extensions ()) && (true : Bool))
  | .Ext_Zvfbfmin => true
  | .Ext_Zvfbfwma => true
  | .Ext_Zvfh => true
  | .Ext_Zvfhmin => true
  | .Ext_Zvbb => true
  | .Ext_Zvbc => false
  | .Ext_Zvkb => false
  | .Ext_Zvkg => true
  | .Ext_Zvkned => true
  | .Ext_Zvknha => true
  | .Ext_Zvknhb => false
  | .Ext_Zvksed => true
  | .Ext_Zvksh => true
  | .Ext_Zvkt => true
  | .Ext_Zvkn =>
    ((hartSupports Ext_Zvkned) && ((hartSupports Ext_Zvknhb) && ((hartSupports Ext_Zvkb) && (hartSupports
            Ext_Zvkt))))
  | .Ext_Zvknc => ((hartSupports Ext_Zvkn) && (hartSupports Ext_Zvbc))
  | .Ext_Zvkng => ((hartSupports Ext_Zvkn) && (hartSupports Ext_Zvkg))
  | .Ext_Zvks =>
    ((hartSupports Ext_Zvksed) && ((hartSupports Ext_Zvksh) && ((hartSupports Ext_Zvkb) && (hartSupports
            Ext_Zvkt))))
  | .Ext_Zvksc => ((hartSupports Ext_Zvks) && (hartSupports Ext_Zvbc))
  | .Ext_Zvksg => ((hartSupports Ext_Zvks) && (hartSupports Ext_Zvkg))
  | .Ext_Ssccptr => true
  | .Ext_Sscofpmf => true
  | .Ext_Sscounterenw => true
  | .Ext_Ssdbltrp => false
  | .Ext_Ssnpm => ((false : Bool) && (xlen == 64))
  | .Ext_Ssstateen => true
  | .Ext_Ssstrict => true
  | .Ext_Sstc => true
  | .Ext_Sstvala => true
  | .Ext_Sstvecd => true
  | .Ext_Ssu64xl => ((hartSupports Ext_S) && (xlen == 64))
  | .Ext_Svbare => true
  | .Ext_Sv32 => ((true : Bool) && (xlen == 32))
  | .Ext_Sv39 => ((false : Bool) && (xlen == 64))
  | .Ext_Sv48 => ((false : Bool) && (xlen == 64))
  | .Ext_Sv57 => ((false : Bool) && (xlen == 64))
  | .Ext_Svade => true
  | .Ext_Svadu => true
  | .Ext_Svinval => true
  | .Ext_Svnapot => ((false : Bool) && (xlen == 64))
  | .Ext_Svpbmt => ((false : Bool) && (xlen == 64))
  | .Ext_Svrsw60t59b => false
  | .Ext_Svukte => ((sys_enable_experimental_extensions ()) && ((false : Bool) && (xlen == 64)))
  | .Ext_Svvptc => true
  | .Ext_Smcntrpmf => true
  | .Ext_Smdbltrp => false
  | .Ext_Smmpm => ((false : Bool) && (xlen == 64))
  | .Ext_Smnpm => ((false : Bool) && (xlen == 64))
  | .Ext_Smstateen => true
  | .Ext_Ssqosid => true
  | .Ext_Sspm => ((hartSupports Ext_Smnpm) && (hartSupports Ext_S))
  | .Ext_Supm =>
    ((hartSupports Ext_U) && (if ((hartSupports Ext_S) : Bool)
      then (hartSupports Ext_Ssnpm)
      else (hartSupports Ext_Smnpm)))
termination_by (let ext := merge_var
(hartSupports_measure ext)).toNat

def _get_Misa_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_Misa_D (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_Misa_F (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_Misa_H (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_Misa_I (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_Misa_M (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_Misa_S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_Misa_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_Misa_V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_Mstatus_FS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 14 13)

def _get_Mstatus_VS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 10 9)

def currentlyEnabled_measure (ext : extension) : Int :=
  match ext with
  | .Ext_A => 0
  | .Ext_B => 0
  | .Ext_C => 0
  | .Ext_M => 0
  | .Ext_Zicsr => 0
  | .Ext_Zvl128b => 0
  | .Ext_Zvl32b => 0
  | .Ext_Zvl64b => 0
  | .Ext_Zimop => 0
  | .Ext_F => 1
  | .Ext_S => 1
  | .Ext_Zaamo => 1
  | .Ext_Zalrsc => 1
  | .Ext_Zca => 1
  | .Ext_Zicntr => 1
  | .Ext_Zihpm => 1
  | .Ext_Zve32x => 1
  | .Ext_Smstateen => 1
  | .Ext_Ssstateen => 1
  | .Ext_D => 2
  | .Ext_Sscounterenw => 2
  | .Ext_Ssdbltrp => 2
  | .Ext_Ssstrict => 2
  | .Ext_Sv39 => 2
  | .Ext_Zfh => 2
  | .Ext_Zvbb => 2
  | .Ext_Zve32f => 2
  | .Ext_Zve64x => 2
  | .Ext_Zcmop => 2
  | .Ext_Zicfiss => 2
  | .Ext_Ssccptr => 3
  | .Ext_Supm => 3
  | .Ext_Svnapot => 3
  | .Ext_Svpbmt => 3
  | .Ext_Svukte => 3
  | .Ext_Svvptc => 3
  | .Ext_Svrsw60t59b => 3
  | .Ext_Zcd => 3
  | .Ext_Zfhmin => 3
  | .Ext_Zicfilp => 3
  | .Ext_Zvbc => 3
  | .Ext_Zve64f => 3
  | .Ext_Zvfbfmin => 3
  | .Ext_Zvkb => 3
  | .Ext_Zvknhb => 3
  | .Ext_H => 4
  | .Ext_Zve64d => 4
  | .Ext_Zvfbfwma => 4
  | .Ext_Zvfh => 4
  | .Ext_Shcounterenw => 5
  | .Ext_Shgatpa => 5
  | .Ext_Shtvala => 5
  | .Ext_Shvsatpa => 5
  | .Ext_Shvstvala => 5
  | .Ext_Shvstvecd => 5
  | .Ext_V => 5
  | .Ext_Zvfhmin => 5
  | .Ext_Sha => 6
  | .Ext_Zfinx => 9
  | .Ext_Zdinx => 10
  | .Ext_Zhinx => 10
  | .Ext_Zhinxmin => 11
  | _ => 2

def _get_Seccfg_MLPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_HEnvcfg_LPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_SEnvcfg_LPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_HEnvcfg_ADUE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _get_HEnvcfg_DTE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _get_HEnvcfg_PBMTE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _get_HEnvcfg_SSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_HEnvcfg_STCE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_HEnvcfg_ADUE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_HEnvcfg_DTE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_HEnvcfg_PBMTE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_HEnvcfg_SSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_HEnvcfg_STCE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _get_SEnvcfg_SSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_SEnvcfg_SSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def privLevel_is_virtual (p : Privilege) : Bool :=
  ((p == VirtualSupervisor) || (p == VirtualUser))

def inVirtualPrivilege (_ : Unit) : SailM Bool := do
  (pure (privLevel_is_virtual (← readReg cur_privilege)))

def is_mstateen_accessible (_ : Unit) : Bool :=
  (hartSupports Ext_Smstateen)

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 3 -/
def get_mstateen (idx : Nat) : SailM (BitVec 64) := do
  if ((not (is_mstateen_accessible ())) : Bool)
  then (pure (ones (n := 64)))
  else
    (do
      match idx with
      | 0 => readReg mstateen0
      | 1 => readReg mstateen1
      | 2 => readReg mstateen2
      | _ => readReg mstateen3)

def stateen_bit_index_forwards (arg_ : stateen_bit) : Nat :=
  match arg_ with
  | .STATEEN_SE => 63
  | .STATEEN_ENVCFG => 62
  | .STATEEN_P1P13 => 56
  | .STATEEN_SRMCFG => 55
  | .STATEEN_FCSR => 1

def read_henvcfg (_ : Unit) : SailM (BitVec 64) := do
  (pure (_update_HEnvcfg_SSE
      (_update_HEnvcfg_DTE
        (_update_HEnvcfg_ADUE
          (_update_HEnvcfg_PBMTE
            (_update_HEnvcfg_STCE (← readReg henvcfg)
              ((_get_MEnvcfg_STCE (← readReg menvcfg)) &&& (_get_HEnvcfg_STCE
                  (← readReg henvcfg))))
            ((_get_MEnvcfg_PBMTE (← readReg menvcfg)) &&& (_get_HEnvcfg_PBMTE
                (← readReg henvcfg))))
          ((_get_MEnvcfg_ADUE (← readReg menvcfg)) &&& (_get_HEnvcfg_ADUE (← readReg henvcfg))))
        ((_get_MEnvcfg_DTE (← readReg menvcfg)) &&& (_get_HEnvcfg_DTE (← readReg henvcfg))))
      ((_get_MEnvcfg_SSE (← readReg menvcfg)) &&& (_get_HEnvcfg_SSE (← readReg henvcfg)))))

def read_senvcfg (_ : Unit) : SailM (BitVec 64) := do
  (pure (_update_SEnvcfg_SSE (← readReg senvcfg)
      ((_get_MEnvcfg_SSE (← readReg menvcfg)) &&& ((_get_SEnvcfg_SSE (← readReg senvcfg)) &&& (← do
            if ((← (inVirtualPrivilege ())) : Bool)
            then (pure (_get_HEnvcfg_SSE (← readReg henvcfg)))
            else (pure 1#1))))))


mutual
/-- Type quantifiers: stateen_reg : Nat, 0 ≤ stateen_reg ∧ stateen_reg ≤ 3 -/
def check_stateen_bit (priv : Privilege) (bit_idx : stateen_bit) (stateen_reg : Nat) : SailM Bool := do
  let mask ← (( do
    match priv with
    | .Machine => (pure (ones (n := 64)))
    | .Supervisor => (get_mstateen stateen_reg)
    | .User => (pure ((← (get_mstateen stateen_reg)) &&& (← (get_sstateen stateen_reg))))
    | .VirtualSupervisor =>
      (pure ((← (get_mstateen stateen_reg)) &&& (← (get_hstateen stateen_reg))))
    | .VirtualUser =>
      (pure ((← (get_mstateen stateen_reg)) &&& ((← (get_hstateen stateen_reg)) &&& (← (get_sstateen
                stateen_reg))))) ) : SailM (BitVec 64) )
  (pure ((BitVec.access mask (stateen_bit_index_forwards bit_idx)) == 1#1))
termination_by (let (_, _, _) := (priv, bit_idx, stateen_reg)
7).toNat
def currentlyEnabled (merge_var : extension) : SailM Bool := do
  match merge_var with
  | .Ext_Shcounterenw => (pure ((hartSupports Ext_Shcounterenw) && (← (currentlyEnabled Ext_H))))
  | .Ext_Shgatpa => (pure ((hartSupports Ext_Shgatpa) && (← (currentlyEnabled Ext_H))))
  | .Ext_Shtvala => (pure ((hartSupports Ext_Shtvala) && (← (currentlyEnabled Ext_H))))
  | .Ext_Shvsatpa => (pure ((hartSupports Ext_Shvsatpa) && (← (currentlyEnabled Ext_H))))
  | .Ext_Shvstvala => (pure ((hartSupports Ext_Shvstvala) && (← (currentlyEnabled Ext_H))))
  | .Ext_Shvstvecd => (pure ((hartSupports Ext_Shvstvecd) && (← (currentlyEnabled Ext_H))))
  | .Ext_Zic64b => (pure (hartSupports Ext_Zic64b))
  | .Ext_Zama16b => (pure (hartSupports Ext_Zama16b))
  | .Ext_Ziccif => (pure (hartSupports Ext_Ziccif))
  | .Ext_Zicclsm => (pure (hartSupports Ext_Zicclsm))
  | .Ext_Zkt => (pure (hartSupports Ext_Zkt))
  | .Ext_Zvkt => (pure (hartSupports Ext_Zvkt))
  | .Ext_Zvkn => (pure (hartSupports Ext_Zvkn))
  | .Ext_Zvknc => (pure (hartSupports Ext_Zvknc))
  | .Ext_Zvkng => (pure (hartSupports Ext_Zvkng))
  | .Ext_Zvks => (pure (hartSupports Ext_Zvks))
  | .Ext_Zvksc => (pure (hartSupports Ext_Zvksc))
  | .Ext_Zvksg => (pure (hartSupports Ext_Zvksg))
  | .Ext_Ssnpm => (pure ((hartSupports Ext_Ssnpm) && (← (currentlyEnabled Ext_S))))
  | .Ext_Ssstrict => (pure ((hartSupports Ext_Ssstrict) && (← (currentlyEnabled Ext_S))))
  | .Ext_Sha =>
    (pure ((hartSupports Ext_Sha) && ((← (currentlyEnabled Ext_H)) && ((← (currentlyEnabled
                Ext_Ssstateen)) && ((← (currentlyEnabled Ext_Shcounterenw)) && ((← (currentlyEnabled
                    Ext_Shgatpa)) && ((← (currentlyEnabled Ext_Shtvala)) && ((← (currentlyEnabled
                        Ext_Shvsatpa)) && ((← (currentlyEnabled Ext_Shvstvala)) && (← (currentlyEnabled
                          Ext_Shvstvecd)))))))))))
  | .Ext_Sstvala => (pure ((hartSupports Ext_Sstvala) && (← (currentlyEnabled Ext_S))))
  | .Ext_Sstvecd => (pure ((hartSupports Ext_Sstvecd) && (← (currentlyEnabled Ext_S))))
  | .Ext_Smdbltrp => (pure (hartSupports Ext_Smdbltrp))
  | .Ext_Smmpm => (pure (hartSupports Ext_Smmpm))
  | .Ext_Smnpm => (pure (hartSupports Ext_Smnpm))
  | .Ext_Sspm => (pure ((hartSupports Ext_Sspm) && (← (currentlyEnabled Ext_S))))
  | .Ext_Supm => (pure ((hartSupports Ext_Supm) && (← (currentlyEnabled Ext_U))))
  | .Ext_Sstc => (pure (hartSupports Ext_Sstc))
  | .Ext_U =>
    (pure ((hartSupports Ext_U) && (((_get_Misa_U (← readReg misa)) == 1#1) && (← (currentlyEnabled
              Ext_Zicsr)))))
  | .Ext_S =>
    (pure ((hartSupports Ext_S) && (((_get_Misa_S (← readReg misa)) == 1#1) && (← (currentlyEnabled
              Ext_Zicsr)))))
  | .Ext_H =>
    (pure ((hartSupports Ext_H) && (((_get_Misa_H (← readReg misa)) == 1#1) && (((_get_Misa_I
                (← readReg misa)) == 1#1) && ((← (currentlyEnabled Ext_S)) && ((← (currentlyEnabled
                    Ext_Sv32)) || (← (currentlyEnabled Ext_Sv39))))))))
  | .Ext_Ssu64xl => (pure ((hartSupports Ext_Ssu64xl) && (← (currentlyEnabled Ext_S))))
  | .Ext_Svbare => (pure ((hartSupports Ext_Svbare) && (← (currentlyEnabled Ext_S))))
  | .Ext_Sv32 => (pure ((hartSupports Ext_Sv32) && (← (currentlyEnabled Ext_S))))
  | .Ext_Sv39 => (pure ((hartSupports Ext_Sv39) && (← (currentlyEnabled Ext_S))))
  | .Ext_Sv48 => (pure ((hartSupports Ext_Sv48) && (← (currentlyEnabled Ext_S))))
  | .Ext_Sv57 => (pure ((hartSupports Ext_Sv57) && (← (currentlyEnabled Ext_S))))
  | .Ext_Ssdbltrp =>
    (pure ((hartSupports Ext_Ssdbltrp) && ((← (currentlyEnabled Ext_S)) && ((_get_MEnvcfg_DTE
              (← readReg menvcfg)) == 1#1))))
  | .Ext_Sscounterenw => (pure ((hartSupports Ext_Sscounterenw) && (← (currentlyEnabled Ext_S))))
  | .Ext_Smstateen => (pure ((hartSupports Ext_Smstateen) && (← (currentlyEnabled Ext_Zicsr))))
  | .Ext_Ssstateen => (pure ((hartSupports Ext_Ssstateen) && (← (currentlyEnabled Ext_Zicsr))))
  | .Ext_F =>
    (pure ((hartSupports Ext_F) && (((_get_Misa_F (← readReg misa)) == 1#1) && ((← (currentlyEnabled
                Ext_Zicsr)) && (((_get_Mstatus_FS (← readReg mstatus)) != 0b00#2) && (← do
                if ((← (inVirtualPrivilege ())) : Bool)
                then (pure ((_get_Mstatus_FS (← readReg vsstatus)) != 0b00#2))
                else (pure true)))))))
  | .Ext_D =>
    (pure ((hartSupports Ext_D) && (((_get_Misa_D (← readReg misa)) == 1#1) && ((flen ≥b 64) && (← (currentlyEnabled
                Ext_F))))))
  | .Ext_Zfinx =>
    (pure ((hartSupports Ext_Zfinx) && ((← (currentlyEnabled Ext_Zicsr)) && (← (is_zfinx_enabled_by_stateen
              ())))))
  | .Ext_Zvl32b => (pure (hartSupports Ext_Zvl32b))
  | .Ext_Zvl64b => (pure (hartSupports Ext_Zvl64b))
  | .Ext_Zvl128b => (pure (hartSupports Ext_Zvl128b))
  | .Ext_Zvl256b => (pure (hartSupports Ext_Zvl256b))
  | .Ext_Zvl512b => (pure (hartSupports Ext_Zvl512b))
  | .Ext_Zvl1024b => (pure (hartSupports Ext_Zvl1024b))
  | .Ext_Zve32x =>
    (pure ((hartSupports Ext_Zve32x) && ((← (currentlyEnabled Ext_Zvl32b)) && ((← (currentlyEnabled
                Ext_Zicsr)) && (((_get_Mstatus_VS (← readReg mstatus)) != 0b00#2) && (← do
                if ((← (inVirtualPrivilege ())) : Bool)
                then (pure ((_get_Mstatus_VS (← readReg vsstatus)) != 0b00#2))
                else (pure true)))))))
  | .Ext_Zve32f =>
    (pure ((hartSupports Ext_Zve32f) && ((← (currentlyEnabled Ext_Zve32x)) && (← (currentlyEnabled
              Ext_F)))))
  | .Ext_Zve64x =>
    (pure ((hartSupports Ext_Zve64x) && ((← (currentlyEnabled Ext_Zvl64b)) && (← (currentlyEnabled
              Ext_Zve32x)))))
  | .Ext_Zve64f =>
    (pure ((hartSupports Ext_Zve64f) && ((← (currentlyEnabled Ext_Zve64x)) && (← (currentlyEnabled
              Ext_Zve32f)))))
  | .Ext_Zve64d =>
    (pure ((hartSupports Ext_Zve64d) && ((← (currentlyEnabled Ext_Zve64f)) && (← (currentlyEnabled
              Ext_D)))))
  | .Ext_V =>
    (pure ((hartSupports Ext_V) && (((_get_Misa_V (← readReg misa)) == 1#1) && ((← (currentlyEnabled
                Ext_Zvl128b)) && (← (currentlyEnabled Ext_Zve64d))))))
  | .Ext_Zvfh =>
    (pure ((hartSupports Ext_Zvfh) && ((← (currentlyEnabled Ext_Zve32f)) && (← (currentlyEnabled
              Ext_Zfhmin)))))
  | .Ext_Zvfhmin =>
    (pure (((hartSupports Ext_Zvfhmin) && (← (currentlyEnabled Ext_Zve32f))) || (← (currentlyEnabled
            Ext_Zvfh))))
  | .Ext_Smcntrpmf => (pure ((hartSupports Ext_Smcntrpmf) && (← (currentlyEnabled Ext_Zicntr))))
  | .Ext_Zicfilp =>
    (pure ((← (currentlyEnabled Ext_Zicsr)) && ((hartSupports Ext_Zicfilp) && (← (get_xLPE
              (← readReg cur_privilege))))))
  | .Ext_Svnapot => (pure ((hartSupports Ext_Svnapot) && (← (currentlyEnabled Ext_Sv39))))
  | .Ext_Svpbmt => (pure ((hartSupports Ext_Svpbmt) && (← (currentlyEnabled Ext_Sv39))))
  | .Ext_Svrsw60t59b => (pure ((hartSupports Ext_Svrsw60t59b) && (← (currentlyEnabled Ext_Sv39))))
  | .Ext_Svvptc =>
    (pure ((hartSupports Ext_Svvptc) && ((← (currentlyEnabled Ext_Sv32)) || (← (currentlyEnabled
              Ext_Sv39)))))
  | .Ext_Svukte => (pure ((hartSupports Ext_Svukte) && (← (currentlyEnabled Ext_Sv39))))
  | .Ext_Svade => (pure (hartSupports Ext_Svade))
  | .Ext_Svadu => (pure (hartSupports Ext_Svadu))
  | .Ext_Ssccptr =>
    (pure ((hartSupports Ext_Ssccptr) && ((← (currentlyEnabled Ext_Sv32)) || (← (currentlyEnabled
              Ext_Sv39)))))
  | .Ext_C => (pure ((hartSupports Ext_C) && ((_get_Misa_C (← readReg misa)) == 1#1)))
  | .Ext_Zca =>
    (pure ((hartSupports Ext_Zca) && ((← (currentlyEnabled Ext_C)) || (not (hartSupports Ext_C)))))
  | .Ext_M => (pure ((hartSupports Ext_M) && ((_get_Misa_M (← readReg misa)) == 1#1)))
  | .Ext_Zmmul => (pure ((hartSupports Ext_Zmmul) || (← (currentlyEnabled Ext_M))))
  | .Ext_Zbb => (pure ((hartSupports Ext_Zbb) || (← (currentlyEnabled Ext_B))))
  | .Ext_Zbkb => (pure (hartSupports Ext_Zbkb))
  | _ =>
    (do
      assert false "Pattern match failure at /private/tmp/airbender-sail-integration/model/model/extensions/B/zbb_insts.sail:10.0-10.67"
      throw Error.Exit)
termination_by (let ext := merge_var
(currentlyEnabled_measure ext)).toNat
/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 3 -/
def get_hstateen (idx : Nat) : SailM (BitVec 64) := do
  if ((not (← (is_hstateen_accessible ()))) : Bool)
  then (pure (ones (n := 64)))
  else
    (do
      match idx with
      | 0 => readReg hstateen0
      | 1 => readReg hstateen1
      | 2 => readReg hstateen2
      | _ => readReg hstateen3)
termination_by (let _ := idx
6).toNat
/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 3 -/
def get_sstateen (idx : Nat) : SailM (BitVec 64) := do
  (pure (0xFFFFFFFF#32 +++ (← do
        if ((not (← (is_sstateen_accessible ()))) : Bool)
        then (pure (ones (n := (64 -i 32))))
        else
          (do
            match idx with
            | 0 => readReg sstateen0
            | 1 => readReg sstateen1
            | 2 => readReg sstateen2
            | _ => readReg sstateen3))))
termination_by (let _ := idx
3).toNat
def get_xLPE (p : Privilege) : SailM Bool := do
  match p with
  | .Machine => (pure (bool_bit_backwards (_get_Seccfg_MLPE (← readReg mseccfg))))
  | .Supervisor => (pure (bool_bit_backwards (_get_MEnvcfg_LPE (← readReg menvcfg))))
  | .User =>
    (do
      if ((← (currentlyEnabled Ext_S)) : Bool)
      then (pure (bool_bit_backwards (_get_SEnvcfg_LPE (← (read_senvcfg ())))))
      else (pure (bool_bit_backwards (_get_MEnvcfg_LPE (← readReg menvcfg)))))
  | .VirtualSupervisor => (pure (bool_bit_backwards (_get_HEnvcfg_LPE (← (read_henvcfg ())))))
  | .VirtualUser => (pure (bool_bit_backwards (_get_SEnvcfg_LPE (← (read_senvcfg ())))))
termination_by (let _ := p
2).toNat
def is_hstateen_accessible (_ : Unit) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_H)) && ((← (currentlyEnabled Ext_Smstateen)) || (← (currentlyEnabled
            Ext_Ssstateen)))))
termination_by (let () := ()
5).toNat
def is_sstateen_accessible (_ : Unit) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_S)) && ((← (currentlyEnabled Ext_Smstateen)) || (← (currentlyEnabled
            Ext_Ssstateen)))))
termination_by (let () := ()
2).toNat
def is_zfinx_enabled_by_stateen (_ : Unit) : SailM Bool := do
  (check_stateen_bit (← readReg cur_privilege) STATEEN_FCSR 0)
termination_by (let () := ()
8).toNat
end

/-- Type quantifiers: x_0 : Nat, x_0 ≥ 0, List.elem x_0 [32, 64] -/
def sail_branch_announce (x_0 : Nat) (x_1 : (BitVec x_0)) : Unit :=
  ()

def pc_write_callback (x_0 : (BitVec 32)) : Unit :=
  ()

def xreg_full_write_callback (x_0 : String) (x_1 : regidx) (x_2 : (BitVec 32)) : Unit :=
  ()

def redirect_callback (x_0 : (BitVec 32)) : Unit :=
  ()

def zero_reg : regtype := (zeros (n := 32))

def regval_from_reg (r : (BitVec 32)) : (BitVec 32) :=
  r

def regval_into_reg (v : (BitVec 32)) : (BitVec 32) :=
  v

def encdec_reg_forwards (arg_ : regidx) : (BitVec 5) :=
  match arg_ with
  | .Regidx r => (zero_extend (m := 5) r)

def encdec_reg_forwards_matches (arg_ : regidx) : Bool :=
  match arg_ with
  | .Regidx r => true

def reg_abi_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  match arg_ with
  | 0b00000 => "zero"
  | 0b00001 => "ra"
  | 0b00010 => "sp"
  | 0b00011 => "gp"
  | 0b00100 => "tp"
  | 0b00101 => "t0"
  | 0b00110 => "t1"
  | 0b00111 => "t2"
  | 0b01000 => "s0"
  | 0b01000 => "fp"
  | 0b01001 => "s1"
  | 0b01010 => "a0"
  | 0b01011 => "a1"
  | 0b01100 => "a2"
  | 0b01101 => "a3"
  | 0b01110 => "a4"
  | 0b01111 => "a5"
  | 0b10000 => "a6"
  | 0b10001 => "a7"
  | 0b10010 => "s2"
  | 0b10011 => "s3"
  | 0b10100 => "s4"
  | 0b10101 => "s5"
  | 0b10110 => "s6"
  | 0b10111 => "s7"
  | 0b11000 => "s8"
  | 0b11001 => "s9"
  | 0b11010 => "s10"
  | 0b11011 => "s11"
  | 0b11100 => "t3"
  | 0b11101 => "t4"
  | 0b11110 => "t5"
  | _ => "t6"

def reg_arch_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  match arg_ with
  | 0b00000 => "x0"
  | 0b00001 => "x1"
  | 0b00010 => "x2"
  | 0b00011 => "x3"
  | 0b00100 => "x4"
  | 0b00101 => "x5"
  | 0b00110 => "x6"
  | 0b00111 => "x7"
  | 0b01000 => "x8"
  | 0b01001 => "x9"
  | 0b01010 => "x10"
  | 0b01011 => "x11"
  | 0b01100 => "x12"
  | 0b01101 => "x13"
  | 0b01110 => "x14"
  | 0b01111 => "x15"
  | 0b10000 => "x16"
  | 0b10001 => "x17"
  | 0b10010 => "x18"
  | 0b10011 => "x19"
  | 0b10100 => "x20"
  | 0b10101 => "x21"
  | 0b10110 => "x22"
  | 0b10111 => "x23"
  | 0b11000 => "x24"
  | 0b11001 => "x25"
  | 0b11010 => "x26"
  | 0b11011 => "x27"
  | 0b11100 => "x28"
  | 0b11101 => "x29"
  | 0b11110 => "x30"
  | _ => "x31"

def reg_name_forwards (arg_ : regidx) : SailM String := do
  let head_exp_ := arg_
  match (let mapping0_ := head_exp_
  if ((encdec_reg_forwards_matches mapping0_) : Bool)
  then
    (let i := (encdec_reg_forwards mapping0_)
    if ((get_config_use_abi_names ()) : Bool)
    then (some (reg_abi_name_raw_forwards i))
    else none)
  else none) with
  | .some result => (pure result)
  | none =>
    (do
      match (let mapping1_ := head_exp_
      if ((encdec_reg_forwards_matches mapping1_) : Bool)
      then
        (let i := (encdec_reg_forwards mapping1_)
        if ((not (get_config_use_abi_names ())) : Bool)
        then (some (reg_arch_name_raw_forwards i))
        else none)
      else none) with
      | .some result => (pure result)
      | _ =>
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))

def xreg_write_callback (reg : regidx) (value : (BitVec 32)) : SailM Unit := do
  let name ← do (reg_name_forwards reg)
  (pure (xreg_full_write_callback name reg value))

def rX (app_0 : regno) : SailM (BitVec 32) := do
  let .Regno r := app_0
  let v ← (( do
    match r with
    | 0 => (pure zero_reg)
    | 1 => readReg x1
    | 2 => readReg x2
    | 3 => readReg x3
    | 4 => readReg x4
    | 5 => readReg x5
    | 6 => readReg x6
    | 7 => readReg x7
    | 8 => readReg x8
    | 9 => readReg x9
    | 10 => readReg x10
    | 11 => readReg x11
    | 12 => readReg x12
    | 13 => readReg x13
    | 14 => readReg x14
    | 15 => readReg x15
    | 16 => readReg x16
    | 17 => readReg x17
    | 18 => readReg x18
    | 19 => readReg x19
    | 20 => readReg x20
    | 21 => readReg x21
    | 22 => readReg x22
    | 23 => readReg x23
    | 24 => readReg x24
    | 25 => readReg x25
    | 26 => readReg x26
    | 27 => readReg x27
    | 28 => readReg x28
    | 29 => readReg x29
    | 30 => readReg x30
    | _ => readReg x31 ) : SailM regtype )
  (pure (regval_from_reg v))

def wX (typ_0 : regno) (in_v : (BitVec 32)) : SailM Unit := do
  let .Regno r : regno := typ_0
  let v := (regval_into_reg in_v)
  match r with
  | 0 => (pure ())
  | 1 => writeReg x1 v
  | 2 => writeReg x2 v
  | 3 => writeReg x3 v
  | 4 => writeReg x4 v
  | 5 => writeReg x5 v
  | 6 => writeReg x6 v
  | 7 => writeReg x7 v
  | 8 => writeReg x8 v
  | 9 => writeReg x9 v
  | 10 => writeReg x10 v
  | 11 => writeReg x11 v
  | 12 => writeReg x12 v
  | 13 => writeReg x13 v
  | 14 => writeReg x14 v
  | 15 => writeReg x15 v
  | 16 => writeReg x16 v
  | 17 => writeReg x17 v
  | 18 => writeReg x18 v
  | 19 => writeReg x19 v
  | 20 => writeReg x20 v
  | 21 => writeReg x21 v
  | 22 => writeReg x22 v
  | 23 => writeReg x23 v
  | 24 => writeReg x24 v
  | 25 => writeReg x25 v
  | 26 => writeReg x26 v
  | 27 => writeReg x27 v
  | 28 => writeReg x28 v
  | 29 => writeReg x29 v
  | 30 => writeReg x30 v
  | _ => writeReg x31 v
  if ((r != 0) : Bool)
  then (xreg_write_callback (Regidx (to_bits (l := 5) r)) in_v)
  else (pure ())

def rX_bits (app_0 : regidx) : SailM (BitVec 32) := do
  let .Regidx i := app_0
  (rX (Regno (BitVec.toNatInt i)))

def wX_bits (typ_0 : regidx) (data : (BitVec 32)) : SailM Unit := do
  let .Regidx i : regidx := typ_0
  (wX (Regno (BitVec.toNatInt i)) data)

def get_arch_pc (_ : Unit) : SailM (BitVec 32) := do
  readReg PC

def get_next_pc (_ : Unit) : SailM (BitVec 32) := do
  readReg nextPC

def set_next_pc (pc : (BitVec 32)) : SailM Unit := do
  let _ : Unit := (sail_branch_announce xlen pc)
  writeReg nextPC pc
  (pure (redirect_callback pc))

def tick_pc (_ : Unit) : SailM Unit := do
  writeReg PC (← readReg nextPC)
  (pure (pc_write_callback (← readReg PC)))

def ext_control_check_pc (_pc : (BitVec 32)) : (Option Unit) :=
  none

def exception_context (e : ExceptionType) (excinfo : (BitVec 32)) : SailM ExceptionContext := do
  (pure { trap := e
          excinfo_is_gva := ← (inVirtualPrivilege ())
          excinfo := excinfo
          excinfo2 := none
          excinst := none
          excinst_offset := (zeros (n := 5))
          ext := none })

def update_elp_state (rs1 : regidx) : SailM Unit := do
  if ((← (currentlyEnabled Ext_Zicfilp)) : Bool)
  then
    (do
      let is_software_guarded_branch := (rs1 == (Regidx (zero_extend (m := 5) 0x7#4)))
      let is_return :=
        ((rs1 == (Regidx (zero_extend (m := 5) 0x1#4))) || (rs1 == (Regidx
              (zero_extend (m := 5) 0x5#4))))
      writeReg elp (bool_to_bit ((not is_software_guarded_branch) && (not is_return))))
  else (pure ())

def RETIRE_SUCCESS : ExecutionResult := (Retire_Success ())

def trap (exc : ExceptionContext) : SailM ExecutionResult := do
  (pure (Trap ((← readReg cur_privilege), exc, (← readReg PC))))

def jump_to (target : (BitVec 32)) : SailM ExecutionResult := SailME.run do
  match (ext_control_check_pc target) with
  | .some e => SailME.throw ((Ext_ControlAddr_Check_Failure e) : ExecutionResult)
  | none => (pure ())
  assert ((BitVec.access target 0) == 0#1) "/private/tmp/airbender-sail-integration/model/model/extensions/I/base_insts.sail:59.25-59.26"
  if (((bit_to_bool (BitVec.access target 1)) && (not (← (currentlyEnabled Ext_Zca)))) : Bool)
  then (trap (← (exception_context (E_Fetch_Addr_Align ()) target)))
  else
    (do
      (set_next_pc target)
      (pure RETIRE_SUCCESS))

def execute_UTYPE (imm : (BitVec 20)) (rd : regidx) (op : uop) : SailM ExecutionResult := do
  let off : xlenbits := (sign_extend (m := 32) (imm +++ 0x000#12))
  (wX_bits rd
    (← do
      match op with
      | .LUI => (pure off)
      | .AUIPC => (pure ((← (get_arch_pc ())) + off))))
  (pure RETIRE_SUCCESS)

def execute_SHIFTIOP (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) (op : sop) : SailM ExecutionResult := do
  let shamt := (Sail.BitVec.extractLsb shamt (log2_xlen -i 1) 0)
  (wX_bits rd
    (← do
      match op with
      | .SLLI => (pure (shift_bits_left (← (rX_bits rs1)) shamt))
      | .SRLI => (pure (shift_bits_right (← (rX_bits rs1)) shamt))
      | .SRAI => (pure (shift_bits_right_arith (← (rX_bits rs1)) shamt))))
  (pure RETIRE_SUCCESS)

def execute_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
  (wX_bits rd
    (← do
      match op with
      | .ADD => (pure ((← (rX_bits rs1)) + (← (rX_bits rs2))))
      | .SLT =>
        (pure (zero_extend (m := 32)
            (bool_to_bit (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | .SLTU =>
        (pure (zero_extend (m := 32)
            (bool_to_bit (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | .AND => (pure ((← (rX_bits rs1)) &&& (← (rX_bits rs2))))
      | .OR => (pure ((← (rX_bits rs1)) ||| (← (rX_bits rs2))))
      | .XOR => (pure ((← (rX_bits rs1)) ^^^ (← (rX_bits rs2))))
      | .SLL =>
        (pure (shift_bits_left (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | .SRL =>
        (pure (shift_bits_right (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | .SUB => (pure ((← (rX_bits rs1)) - (← (rX_bits rs2))))
      | .SRA =>
        (pure (shift_bits_right_arith (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))))
  (pure RETIRE_SUCCESS)

def execute_REV8 (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (wX_bits rd (rev8 (← (rX_bits rs1))))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: k_ex436011_ : Bool -/
def execute_REM (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let rs1_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let remainder :=
    if ((rs2_int == 0) : Bool)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (wX_bits rd (to_bits_truncate (l := 32) remainder))
  (pure RETIRE_SUCCESS)

def execute_MUL (rs2 : regidx) (rs1 : regidx) (rd : regidx) (mul_op : mul_op) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd
    (mult_to_bits_half (l := xlen) mul_op.signed_rs1 mul_op.signed_rs2 rs1_bits rs2_bits
      mul_op.result_part))
  (pure RETIRE_SUCCESS)

def execute_JALR (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (update_elp_state rs1)
  let link_address ← do (get_next_pc ())
  let target ← do (pure ((← (rX_bits rs1)) + (sign_extend (m := 32) imm)))
  match (← (jump_to (BitVec.update target 0 0#1))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (Retire_Success ())))
  | failure => (pure failure)

def execute_JAL (imm : (BitVec 21)) (rd : regidx) : SailM ExecutionResult := do
  let link_address ← do (get_next_pc ())
  match (← (jump_to ((← readReg PC) + (sign_extend (m := 32) imm)))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (Retire_Success ())))
  | failure => (pure failure)

def execute_ITYPE (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : iop) : SailM ExecutionResult := do
  let immext : xlenbits := (sign_extend (m := 32) imm)
  (wX_bits rd
    (← do
      match op with
      | .ADDI => (pure ((← (rX_bits rs1)) + immext))
      | .SLTI => (pure (zero_extend (m := 32) (bool_to_bit (zopz0zI_s (← (rX_bits rs1)) immext))))
      | .SLTIU =>
        (pure (zero_extend (m := 32) (bool_to_bit (zopz0zI_u (← (rX_bits rs1)) immext))))
      | .ANDI => (pure ((← (rX_bits rs1)) &&& immext))
      | .ORI => (pure ((← (rX_bits rs1)) ||| immext))
      | .XORI => (pure ((← (rX_bits rs1)) ^^^ immext))))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: k_ex436015_ : Bool -/
def execute_DIV (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let rs1_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let quotient :=
    if ((rs2_int == 0) : Bool)
    then (Neg.neg 1)
    else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    if (((not is_unsigned) && (quotient ≥b (2 ^i (xlen -i 1)))) : Bool)
    then (Neg.neg (2 ^i (xlen -i 1)))
    else quotient
  (wX_bits rd (to_bits_truncate (l := 32) quotient))
  (pure RETIRE_SUCCESS)

def execute_BTYPE (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) (op : bop) : SailM ExecutionResult := do
  let taken ← (( do
    match op with
    | .BEQ => (pure ((← (rX_bits rs1)) == (← (rX_bits rs2))))
    | .BNE => (pure ((← (rX_bits rs1)) != (← (rX_bits rs2))))
    | .BLT => (pure (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BGE => (pure (zopz0zKzJ_s (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BLTU => (pure (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BGEU => (pure (zopz0zKzJ_u (← (rX_bits rs1)) (← (rX_bits rs2)))) ) : SailM Bool )
  if (taken : Bool)
  then (jump_to ((← readReg PC) + (sign_extend (m := 32) imm)))
  else (pure RETIRE_SUCCESS)

def normal_base_next_pc (_ : Unit) : SailM Unit := do
  writeReg nextPC (BitVec.addInt (← readReg PC) 4)

end SailRV32.Functions
