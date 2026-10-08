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

variable [MemoryPlatform exception]

abbrev plat_term_write {m : Type → Type} [MonadLift SailM m] (byte : BitVec 8) : m Unit :=
  liftM (Sail.ArchSem.plat_term_write (ue := exception) byte)

abbrev load_reservation {m : Type → Type} [MonadLift SailM m]
    (address : BitVec Arch.addr_size) (width : Nat) : m Unit :=
  liftM (Sail.ArchSem.load_reservation (ue := exception) address width)

abbrev match_reservation (address : BitVec Arch.addr_size) : Bool :=
  Sail.ArchSem.match_reservation (ue := exception) address

open write_kind
open virtaddr
open vector_support
open uop
open stateen_bit
open sopw
open sop
open ropw
open rop
open regno
open regidx
open read_kind
open pte_check_failure
open pmpAddrMatch
open physaddr
open page_based_mem_type
open option
open misaligned_exception
open mem_payload
open iop
open instruction
open extop_zbb
open extension
open exception
open csrop
open cbop_zicbop
open cbop_zicbom
open cacheop
open bropw_zbb
open brop_zbb
open breakpoint_cause
open bop
open amoop
open access_kind
open XipReadType
open WaitReason
open VectorHalf
open TranslationStage
open Splittability
open Signedness
open SATPMode
open Reservability
open Register
open Privileged_ISA_Version
open Privilege
open PointerMaskingMode
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open MemoryRegionType
open MemoryAccessType
open HGATPMode
open Ext_DataAddr_Check
open ExecutionResult
open ExceptionType
open AtomicSupport
open Architecture

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

def num_of_Privileged_ISA_Version (arg_ : Privileged_ISA_Version) : Int :=
  match arg_ with
  | .Privileged_ISA_1_11 => 0
  | .Privileged_ISA_1_12 => 1
  | .Privileged_ISA_1_13 => 2

def num_of_vector_support (arg_ : vector_support) : Int :=
  match arg_ with
  | .Disabled => 0
  | .Integer => 1
  | .Float_single => 2
  | .Float_double => 3
  | .Full => 4

def privileged_isa_version_ge (x : Privileged_ISA_Version) (y : Privileged_ISA_Version) : Bool :=
  ((num_of_Privileged_ISA_Version x) ≥b (num_of_Privileged_ISA_Version y))

def vector_support_ge (x : vector_support) (y : vector_support) : Bool :=
  ((num_of_vector_support x) ≥b (num_of_vector_support y))

/-- Type quantifiers: n : Nat, n ≥ 0, n ≥ 0 -/
def sail_ones (n : Nat) : (BitVec n) :=
  (Complement.complement (BitVec.zero n))

/-- Type quantifiers: n : Nat, n ≥ 0, n > 0 -/
def to_bytes_le {n : _} (b : (BitVec (8 * n))) : (Vector (BitVec 8) n) := Id.run do
  let res := (vectorInit (BitVec.zero 8))
  let loop_i_lower := 0
  let loop_i_upper := (n -i 1)
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper:1]i do
    let res := loop_vars
    loop_vars := (vectorUpdate res i (Sail.BitVec.extractLsb b ((8 *i i) +i 7) (8 *i i)))
  (pure loop_vars)

/-- Type quantifiers: n : Nat, n ≥ 0, n > 0 -/
def from_bytes_le {n : _} (v : (Vector (BitVec 8) n)) : (BitVec (8 * n)) := Id.run do
  let res := (BitVec.zero (8 *i n))
  let loop_i_lower := 0
  let loop_i_upper := (n -i 1)
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper:1]i do
    let res := loop_vars
    loop_vars := (Sail.BitVec.updateSubrange res ((8 *i i) +i 7) (8 *i i) (GetElem?.getElem! v i))
  (pure loop_vars)

def get_config_print_clint (_ : Unit) : Bool :=
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

/-- Type quantifiers: k_ex433936_ : Bool -/
def bool_bit_forwards (arg_ : Bool) : (BitVec 1) :=
  match arg_ with
  | true => 1#1
  | false => 0#1

def bool_bit_backwards (arg_ : (BitVec 1)) : Bool :=
  match arg_ with
  | 1 => true
  | _ => false

def bool_bit_backwards_matches (arg_ : (BitVec 1)) : Bool :=
  match arg_ with
  | 1 => true
  | 0 => true
  | _ => false

/-- Type quantifiers: k_ex433942_ : Bool -/
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
  assert ((BitVec.toNatInt bv) == n) (HAppend.hAppend "Couldn't convert integer "
    (HAppend.hAppend (Int.repr n)
      (HAppend.hAppend " to " (HAppend.hAppend (Int.repr l) " bits without overflow."))))
  (pure bv)

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
def zopz0zK_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNatInt x) >b (BitVec.toNatInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zopz0zIzJ_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNatInt x) ≤b (BitVec.toNatInt y))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zopz0zKzJ_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNatInt x) ≥b (BitVec.toNatInt y))

/-- Type quantifiers: k_ex433947_ : Bool, k_ex433946_ : Bool -/
def zopz0zJzJzK (x : Bool) (y : Bool) : Bool :=
  ((not x) || y)

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_n : Nat, k_n ≥ 0, k_n ≥ 1 -/
def shift_bits_right_arith (value : (BitVec k_n)) (shift : (BitVec k_m)) : (BitVec k_n) :=
  (BitVec.sshiftRight value (BitVec.toNatInt shift))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ≥ 0 -/
def hex_bits_str (x : (BitVec k_n)) : String :=
  (BitVec.toFormatted
    (zero_extend
      (m := ((3 -i (Int.tmod ((Sail.BitVec.length x) +i 3) 4)) +i (Sail.BitVec.length x))) x))

/-- Type quantifiers: line : Int, k_a : Type -/
def internal_error (file : String) (line : Int) (s : String) : SailM k_a := do
  sailThrow ((Error_internal_error
    (HAppend.hAppend file
      (HAppend.hAppend ":" (HAppend.hAppend (Int.repr line) (HAppend.hAppend ": " s))))))

def amo_mnemonic_forwards (arg_ : amoop) : String :=
  match arg_ with
  | .AMOSWAP => "amoswap"
  | .AMOAND => "amoand"
  | .AMOOR => "amoor"
  | .AMOXOR => "amoxor"
  | .AMOADD => "amoadd"
  | .AMOMIN => "amomin"
  | .AMOMAX => "amomax"
  | .AMOMINU => "amominu"
  | .AMOMAXU => "amomaxu"
  | .AMOCAS => "amocas"

def pmm_mode_backwards (arg_ : (BitVec 2)) : PointerMaskingMode :=
  match arg_ with
  | 0b00 => PMM_Disabled
  | 0b01 => PMM_Reserved
  | 0b10 => PMM_PMLEN_7
  | _ => PMM_PMLEN_16

def priv_isa_version : Privileged_ISA_Version := Privileged_ISA_1_13

def pte_reserved_bits_must_be_zero :=
  (privileged_isa_version_ge priv_isa_version Privileged_ISA_1_12)

def log2_xlen := 5

def xlen_bytes := 4

def xlen := 32

def gpalen := 34

def geilen := 31

def flen := (8 *i 8)

def vector_support_level : vector_support := Float_single

def bits_of_physaddr (app_0 : physaddr) : (BitVec (if ( 32 = 32  : Bool) then 34 else 64)) :=
  let .Physaddr paddr := app_0
  paddr

def bits_of_virtaddr (app_0 : virtaddr) : (BitVec 32) :=
  let .Virtaddr vaddr := app_0
  vaddr

def default_meta : mem_meta := ()

/-- Type quantifiers: _width : Nat, 1 ≤ _width ∧ _width ≤ 4096 -/
def __WriteRAM_Meta (_addr : (BitVec (if ( 32 = 32  : Bool) then 34 else 64))) (_width : Nat) (_meta : Unit) : Unit :=
  ()

/-- Type quantifiers: _width : Nat, 1 ≤ _width ∧ _width ≤ 4096 -/
def __ReadRAM_Meta (_addr : (BitVec (if ( 32 = 32  : Bool) then 34 else 64))) (_width : Nat) : Unit :=
  default_meta

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

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, 0 ≤ k_n ∧ k_n ≤ 64 -/
def range_subset (a_begin : (BitVec k_n)) (a_size : (BitVec k_n)) (b_begin : (BitVec k_n)) (b_size : (BitVec k_n)) : Bool :=
  let a_end := ((a_begin + a_size) - b_begin)
  let b_end := ((b_begin + b_size) - b_begin)
  let a_begin := (a_begin - b_begin)
  ((zopz0zIzJ_u a_begin b_end) && ((zopz0zIzJ_u a_end b_end) && (zopz0zIzJ_u a_begin a_end)))

def plat_reservation_set_size_exp : Nat := 3

def misaligned_exception_str_forwards (arg_ : misaligned_exception) : String :=
  match arg_ with
  | .AccessFault => "AccessFault"
  | .AlignmentException => "AlignmentException"

def mem_payload_str_forwards (arg_ : mem_payload) : String :=
  match arg_ with
  | .Data => ""
  | .Vector => ""
  | .PageTableEntry => ""
  | .ShadowStack => ".ss"

def sp : regidx := (Regidx (zero_extend (m := 5) 0b10#2))

def accessType_to_str (access : (MemoryAccessType mem_payload)) : String :=
  match access with
  | .Load p => (HAppend.hAppend "R" (mem_payload_str_forwards p))
  | .LoadReserved (_, _, p) => (HAppend.hAppend "R" (mem_payload_str_forwards p))
  | .Store p => (HAppend.hAppend "W" (mem_payload_str_forwards p))
  | .StoreConditional (_, _, p) => (HAppend.hAppend "W" (mem_payload_str_forwards p))
  | .Atomic (_, _, _, lp, sp) =>
    (HAppend.hAppend "R"
      (HAppend.hAppend (mem_payload_str_forwards lp)
        (HAppend.hAppend "W" (mem_payload_str_forwards sp))))
  | .InstructionFetch () => "X"
  | .LoadExecute p => (HAppend.hAppend "RX" (mem_payload_str_forwards p))
  | .CacheAccess _ => "C"

def atomic_support_str_forwards (arg_ : AtomicSupport) : String :=
  match arg_ with
  | .AMONone => "AMONone"
  | .AMOSwap => "AMOSwap"
  | .AMOLogical => "AMOLogical"
  | .AMOArithmetic => "AMOArithmetic"
  | .AMOCASW => "AMOCASW"
  | .AMOCASD => "AMOCASD"
  | .AMOCASQ => "AMOCASQ"

def optional_misaligned_exception_str (opt_e : (Option misaligned_exception)) : String :=
  match opt_e with
  | none => "NoFault"
  | .some e => (misaligned_exception_str_forwards e)

def pma_misaligned_to_str (m : PMAMisalignedExceptions) : String :=
  (HAppend.hAppend "misaligned-load-store:"
    (HAppend.hAppend (optional_misaligned_exception_str m.load_store)
      (HAppend.hAppend " misaligned-amo:"
        (HAppend.hAppend (misaligned_exception_str_forwards m.amo)
          (HAppend.hAppend " misaligned-vector:" (optional_misaligned_exception_str m.vector))))))

def reservability_str_forwards (arg_ : Reservability) : String :=
  match arg_ with
  | .RsrvNone => "RsrvNone"
  | .RsrvNonEventual => "RsrvNonEventual"
  | .RsrvEventual => "RsrvEventual"

def pma_attributes_to_str (attr : PMA) : String :=
  (HAppend.hAppend
    (match attr.mem_type with
    | .MainMemory => " main-memory"
    | .IOMemory => " io-memory")
    (HAppend.hAppend
      (if (attr.cacheable : Bool)
      then " cacheable"
      else "")
      (HAppend.hAppend
        (if (attr.coherent : Bool)
        then " coherent"
        else "")
        (HAppend.hAppend
          (if (attr.executable : Bool)
          then " executable"
          else "")
          (HAppend.hAppend
            (if (attr.readable : Bool)
            then " readable"
            else "")
            (HAppend.hAppend
              (if (attr.writable : Bool)
              then " writable"
              else "")
              (HAppend.hAppend
                (if (attr.read_idempotent : Bool)
                then " read-idempotent"
                else "")
                (HAppend.hAppend
                  (if (attr.write_idempotent : Bool)
                  then " write-idempotent"
                  else "")
                  (HAppend.hAppend " "
                    (HAppend.hAppend (pma_misaligned_to_str attr.misaligned_exceptions)
                      (HAppend.hAppend " "
                        (HAppend.hAppend (atomic_support_str_forwards attr.atomic_support)
                          (HAppend.hAppend " "
                            (HAppend.hAppend (reservability_str_forwards attr.reservability)
                              (HAppend.hAppend
                                (if (attr.supports_cbo_zero : Bool)
                                then " supports-cbo-zero"
                                else "")
                                (HAppend.hAppend
                                  (if (attr.supports_pte_read : Bool)
                                  then " supports-pte-read"
                                  else "")
                                  (HAppend.hAppend
                                    (if (attr.supports_pte_write : Bool)
                                    then " supports-pte-write"
                                    else "")
                                    (HAppend.hAppend " misaligned_atomicity_granule_size_exp="
                                      (HAppend.hAppend
                                        (Int.repr attr.misaligned_atomicity_granule_size_exp)
                                        (HAppend.hAppend
                                          " vector_misaligned_atomicity_granule_size_exp="
                                          (HAppend.hAppend
                                            (Int.repr
                                              attr.vector_misaligned_atomicity_granule_size_exp) " ")))))))))))))))))))))

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

def _get_MEnvcfg_PMM (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

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

def _get_Seccfg_PMM (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

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

def _get_HEnvcfg_PMM (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

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

def _get_SEnvcfg_PMM (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _get_SEnvcfg_SSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_SEnvcfg_UKTE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

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
  | .Ext_Zicsr => (pure (hartSupports Ext_Zicsr))
  | _ =>
    (do
      assert false "Pattern match failure at /private/tmp/airbender-sail-integration/model/model/extensions/Zicsr/zicsr_insts.sail:12.0-12.69"
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

def plat_misaligned_access : GlobalMisalignedExceptions :=
  { load_store := none
    vector := none
    amo := none
    lrsc := (some AccessFault) }

def plat_have_clint : Bool := true

def plat_clint_base : physaddrbits := unwrapValue ((to_bits_checked (l := 34) (33554432 : Int)))

def plat_clint_size : physaddrbits := unwrapValue ((to_bits_checked (l := 34) (49152 : Int)))

def plat_have_sig : Bool := true

def plat_sig_base : physaddrbits := unwrapValue ((to_bits_checked (l := 34) (201326592 : Int)))

def plat_sig_size : physaddrbits := (zero_extend (m := 34) 0x20#8)

def plat_has_msi : Bool := true

def plat_has_mti : Bool := true

def plat_has_mei : Bool := true

def plat_has_ssi : Bool := true

def plat_has_sti : Bool := true

def plat_has_sei : Bool := true

def init_ext_ptw : ext_ptw := ()

def ext_translate_exception (e : Unit) : Unit :=
  e

def ext_exc_type_bits_forwards (arg_ : Unit) : (BitVec 6) :=
  match arg_ with
  | () => 0b011000#6

def pagesize_bits := 12

def base_E_enabled := false

def regidx_bit_width := 5

def architecture_bits_backwards (arg_ : (BitVec 2)) : SailM Architecture := do
  match arg_ with
  | 0b01 => (pure RV32)
  | 0b10 => (pure RV64)
  | 0b11 => (pure RV128)
  | _ =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/core/types.sail" 62
      "architecture(0b00) is invalid")

def privLevel_bits_forwards (arg_ : ((BitVec 2) × (BitVec 1))) : SailM Privilege := do
  match arg_ with
  | (0b00, 0) => (pure User)
  | (0b00, 1) => (pure VirtualUser)
  | (0b01, 0) => (pure Supervisor)
  | (0b01, 1) => (pure VirtualSupervisor)
  | (0b11, 0) => (pure Machine)
  | _ =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/core/types.sail" 79
      "Invalid privilege level or virtual mode")

/-- Type quantifiers: k_a : Type -/
def is_load_store (access : (MemoryAccessType k_a)) : Bool :=
  match access with
  | .Load _ => true
  | .Store _ => true
  | .LoadReserved _ => true
  | .LoadExecute _ => true
  | .StoreConditional _ => true
  | .Atomic _ => true
  | .InstructionFetch _ => false
  | .CacheAccess _ => true

/-- Type quantifiers: k_a : Type -/
def is_prefetch_access (access : (MemoryAccessType k_a)) : Bool :=
  match access with
  | .CacheAccess (.CB_prefetch _) => true
  | _ => false

/-- Type quantifiers: k_a : Type -/
def is_load_reserved (access : (MemoryAccessType k_a)) : Bool :=
  match access with
  | .LoadReserved _ => true
  | _ => false

/-- Type quantifiers: k_a : Type -/
def is_store_conditional (access : (MemoryAccessType k_a)) : Bool :=
  match access with
  | .StoreConditional _ => true
  | _ => false

def exceptionType_bits_forwards (arg_ : ExceptionType) : (BitVec 6) :=
  match arg_ with
  | .E_Fetch_Addr_Align () => 0b000000#6
  | .E_Fetch_Access_Fault () => 0b000001#6
  | .E_Illegal_Instr () => 0b000010#6
  | .E_Load_Addr_Align () => 0b000100#6
  | .E_Load_Access_Fault () => 0b000101#6
  | .E_SAMO_Addr_Align () => 0b000110#6
  | .E_SAMO_Access_Fault () => 0b000111#6
  | .E_U_EnvCall () => 0b001000#6
  | .E_S_EnvCall () => 0b001001#6
  | .E_VS_EnvCall () => 0b001010#6
  | .E_M_EnvCall () => 0b001011#6
  | .E_Fetch_Page_Fault () => 0b001100#6
  | .E_Load_Page_Fault () => 0b001101#6
  | .E_Reserved_14 () => 0b001110#6
  | .E_SAMO_Page_Fault () => 0b001111#6
  | .E_Double_Trap () => 0b010000#6
  | .E_Reserved_17 () => 0b010001#6
  | .E_Software_Check () => 0b010010#6
  | .E_Hardware_Error () => 0b010011#6
  | .E_Fetch_GPage_Fault () => 0b010100#6
  | .E_Load_GPage_Fault () => 0b010101#6
  | .E_Virtual_Instr () => 0b010110#6
  | .E_SAMO_GPage_Fault () => 0b010111#6
  | .E_Breakpoint .Brk_Software => 0b000011#6
  | .E_Breakpoint .Brk_Hardware => 0b000011#6
  | .E_Extension e => (ext_exc_type_bits_forwards e)

def is_guest_page_fault (e : ExceptionType) : Bool :=
  match e with
  | .E_Fetch_GPage_Fault () => true
  | .E_Load_GPage_Fault () => true
  | .E_SAMO_GPage_Fault () => true
  | _ => false

def hgatpMode_of_bits (a : Architecture) (m : (BitVec 4)) : SailM (Option HGATPMode) := do
  match (a, m) with
  | (_, 0x0) => (pure (some HBare))
  | (.RV32, 0x1) => (pure (some Sv32x4))
  | (.RV64, 0x8) => (pure (some Sv39x4))
  | (.RV64, 0x9) => (pure (some Sv48x4))
  | (.RV64, 0xA) => (pure (some Sv57x4))
  | (_, _) => (pure none)

def satpMode_of_bits (a : Architecture) (m : (BitVec 4)) : SailM (Option SATPMode) := do
  match (a, m) with
  | (_, 0x0) => (pure (some Bare))
  | (.RV32, 0x1) => (pure (some Sv32))
  | (.RV64, 0x8) => (pure (some Sv39))
  | (.RV64, 0x9) => (pure (some Sv48))
  | (.RV64, 0xA) => (pure (some Sv57))
  | (_, _) => (pure none)

def width_enc_backwards (arg_ : (BitVec 2)) : Int :=
  match arg_ with
  | 0b00 => 1
  | 0b01 => 2
  | 0b10 => 4
  | _ => 8

def width_enc_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

/-- Type quantifiers: sv_width : Nat, (is_sv_or_svx4_mode sv_width) -/
def get_root_level (sv_width : Nat) : Nat :=
  if (((sv_width == 32) || (sv_width == 34)) : Bool)
  then 1
  else
    (if (((sv_width == 39) || (sv_width == 41)) : Bool)
    then 2
    else
      (if (((sv_width == 48) || (sv_width == 50)) : Bool)
      then 3
      else 4))

/-- Type quantifiers: sv_width : Nat, (is_sv_or_svx4_mode sv_width) -/
def get_vpn_level_size (sv_width : Nat) : Nat :=
  (12 -i (if (((sv_width == 32) || (sv_width == 34)) : Bool)
    then 2
    else 3))

def mem_payload_name_forwards (arg_ : mem_payload) : String :=
  match arg_ with
  | .Data => "Data"
  | .Vector => "Vector"
  | .PageTableEntry => "PageTableEntry"
  | .ShadowStack => "ShadowStack"

def is_shadow_stack_access (access : (MemoryAccessType mem_payload)) : SailM Bool := do
  match access with
  | .Load .ShadowStack => (pure true)
  | .Store .ShadowStack => (pure true)
  | .Atomic (_, _, _, .ShadowStack, .ShadowStack) => (pure true)
  | .InstructionFetch () => (pure false)
  | .Load .Data => (pure false)
  | .Load .Vector => (pure false)
  | .Load .PageTableEntry => (pure false)
  | .LoadExecute .Data => (pure false)
  | .LoadReserved (_, _, .Data) => (pure false)
  | .Store .Data => (pure false)
  | .Store .Vector => (pure false)
  | .Store .PageTableEntry => (pure false)
  | .StoreConditional (_, _, .Data) => (pure false)
  | .Atomic (_, _, _, .Data, .Data) => (pure false)
  | .CacheAccess _ => (pure false)
  | .LoadExecute p =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/core/vmem_types.sail" 111
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadExecute.")))
  | .LoadReserved (_, _, p) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/core/vmem_types.sail" 112
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadReserved.")))
  | .StoreConditional (_, _, p) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/core/vmem_types.sail" 113
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for StoreConditional.")))
  | .Atomic (_, _, _, rp, wp) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/core/vmem_types.sail" 114
      (HAppend.hAppend "Invalid payloads ("
        (HAppend.hAppend (mem_payload_name_forwards rp)
          (HAppend.hAppend ", " (HAppend.hAppend (mem_payload_name_forwards wp) ") for Atomic.")))))

def is_amo_access (access : (MemoryAccessType mem_payload)) : Bool :=
  match access with
  | .Atomic _ => true
  | _ => false

def is_vector_access (access : (MemoryAccessType mem_payload)) : Bool :=
  match access with
  | .Load .Vector => true
  | .Store .Vector => true
  | _ => false

def page_based_mem_type_forwards (arg_ : (BitVec 2)) : SailM page_based_mem_type := do
  match arg_ with
  | 0b00 => (pure PBMT_PMA)
  | 0b01 => (pure PBMT_NC)
  | 0b10 => (pure PBMT_IO)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def page_based_mem_type_forwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | _ => false

/-- Type quantifiers: x_0 : Nat, x_0 ≥ 0, List.elem x_0 [32, 64] -/
def sail_branch_announce (x_0 : Nat) (x_1 : (BitVec x_0)) : Unit :=
  ()

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ≥ 0 -/
def __monomorphize (bv : (BitVec k_n)) : (BitVec k_n) :=
  bv

def __monomorphize_reads : Bool := false

def __monomorphize_writes : Bool := false

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def write_ram (wk : write_kind) (access : (MemoryAccessType mem_payload)) (app_2 : physaddr) (width : Nat) (data : (BitVec (8 * width))) (meta' : Unit) : SailM Bool := do
  let .Physaddr addr := app_2
  let request ← (( do
    (pure { access_kind := ← match wk with
              | .Write_RISCV_release =>
                (internal_error
                  "/private/tmp/airbender-sail-integration/model/model/core/phys_mem_interface.sail"
                  146 "Write_RISCV_release is unused")
              | .Write_RISCV_strong_release =>
                (internal_error
                  "/private/tmp/airbender-sail-integration/model/model/core/phys_mem_interface.sail"
                  147 "Write_RISCV_strong_release is unused")
              | _ => (pure (AK_Write (wk, access)))
            address := addr
            address_space := ()
            size := width
            num_tag := 0 }) ) : SailM (Mem_request width 0 physaddrbits_len Unit access_kind) )
  match (← (sail_mem_write request (to_bytes_le (n := width) data) #v[])) with
  | .Ok _ =>
    (let _ : Unit := (__WriteRAM_Meta addr width meta')
    (pure true))
  | .Err () => (pure false)

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def write_ram_ea (wk : write_kind) (access : (MemoryAccessType mem_payload)) (app_2 : physaddr) (width : Nat) : SailM Unit := do
  let .Physaddr addr := app_2
  let request ← (( do
    (pure { access_kind := ← match wk with
              | .Write_RISCV_release =>
                (internal_error
                  "/private/tmp/airbender-sail-integration/model/model/core/phys_mem_interface.sail"
                  183 "Write_RISCV_release is unused")
              | .Write_RISCV_strong_release =>
                (internal_error
                  "/private/tmp/airbender-sail-integration/model/model/core/phys_mem_interface.sail"
                  184 "Write_RISCV_strong_release is unused")
              | _ => (pure (AK_Write (wk, access)))
            address := addr
            address_space := ()
            size := width
            num_tag := 0 }) ) : SailM (Mem_request width 0 physaddrbits_len Unit access_kind) )
  (sail_mem_address_announce request)

/-- Type quantifiers: k_ex436101_ : Bool, width : Nat, width ≥ 0, 0 < width ∧
  width ≤ max_mem_access -/
def read_ram (rk : read_kind) (access : (MemoryAccessType mem_payload)) (app_2 : physaddr) (width : Nat) (read_meta : Bool) : SailM ((BitVec (8 * width)) × Unit) := do
  let .Physaddr addr := app_2
  let meta' :=
    if (read_meta : Bool)
    then (__ReadRAM_Meta addr width)
    else default_meta
  let request ← (( do
    (pure { access_kind := ← match rk with
              | .Read_RISCV_acquire =>
                (internal_error
                  "/private/tmp/airbender-sail-integration/model/model/core/phys_mem_interface.sail"
                  219 "Read_RISCV_acquire is unused")
              | .Read_RISCV_strong_acquire =>
                (internal_error
                  "/private/tmp/airbender-sail-integration/model/model/core/phys_mem_interface.sail"
                  220 "Read_RISCV_strong_acquire is unused")
              | _ => (pure (AK_Read (rk, access)))
            address := addr
            address_space := ()
            size := width
            num_tag := 0 }) ) : SailM (Mem_request width 0 physaddrbits_len Unit access_kind) )
  match (← (sail_mem_read request)) with
  | .Ok (value, _) => (pure ((from_bytes_le (n := width) value), meta'))
  | .Err () => throw Error.Exit

def accessFaultFromAccessType (access : (MemoryAccessType mem_payload)) : SailM ExceptionType := do
  match access with
  | .InstructionFetch () => (pure (E_Fetch_Access_Fault ()))
  | .Load .Data => (pure (E_Load_Access_Fault ()))
  | .Load .Vector => (pure (E_Load_Access_Fault ()))
  | .Load .PageTableEntry => (pure (E_Load_Access_Fault ()))
  | .LoadExecute .Data => (pure (E_Load_Access_Fault ()))
  | .LoadReserved (_, _, .Data) => (pure (E_Load_Access_Fault ()))
  | .Store .Data => (pure (E_SAMO_Access_Fault ()))
  | .Store .Vector => (pure (E_SAMO_Access_Fault ()))
  | .Store .PageTableEntry => (pure (E_SAMO_Access_Fault ()))
  | .StoreConditional (_, _, .Data) => (pure (E_SAMO_Access_Fault ()))
  | .Atomic (_, _, _, .Data, .Data) => (pure (E_SAMO_Access_Fault ()))
  | .Load .ShadowStack => (pure (E_SAMO_Access_Fault ()))
  | .Store .ShadowStack => (pure (E_SAMO_Access_Fault ()))
  | .Atomic (_, _, _, .ShadowStack, .ShadowStack) => (pure (E_SAMO_Access_Fault ()))
  | .LoadExecute p =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/core/mem_type_utils.sail"
      32
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadExecute.")))
  | .LoadReserved (_, _, p) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/core/mem_type_utils.sail"
      33
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadReserved.")))
  | .StoreConditional (_, _, p) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/core/mem_type_utils.sail"
      34
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for StoreConditional.")))
  | .Atomic (_, _, _, rp, wp) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/core/mem_type_utils.sail"
      35
      (HAppend.hAppend "Invalid payloads ("
        (HAppend.hAppend (mem_payload_name_forwards rp)
          (HAppend.hAppend ", " (HAppend.hAppend (mem_payload_str_forwards wp) ") for Atomic.")))))
  | .CacheAccess (.CB_manage _) => (pure (E_SAMO_Access_Fault ()))
  | .CacheAccess (.CB_zero ()) => (pure (E_SAMO_Access_Fault ()))
  | .CacheAccess (.CB_prefetch p) =>
    (match p with
    | .PREFETCH_R => (pure (E_Load_Access_Fault ()))
    | .PREFETCH_W => (pure (E_SAMO_Access_Fault ()))
    | .PREFETCH_I => (pure (E_Fetch_Access_Fault ())))

def alignmentFaultFromAccessType (access : (MemoryAccessType mem_payload)) : SailM ExceptionType := do
  match access with
  | .InstructionFetch () => (pure (E_Fetch_Addr_Align ()))
  | .Load .Data => (pure (E_Load_Addr_Align ()))
  | .Load .Vector => (pure (E_Load_Addr_Align ()))
  | .Load .PageTableEntry => (pure (E_Load_Addr_Align ()))
  | .LoadReserved (_, _, .Data) => (pure (E_Load_Addr_Align ()))
  | .LoadExecute .Data => (pure (E_Load_Addr_Align ()))
  | .Store .Data => (pure (E_SAMO_Addr_Align ()))
  | .Store .Vector => (pure (E_SAMO_Addr_Align ()))
  | .Store .PageTableEntry => (pure (E_SAMO_Addr_Align ()))
  | .StoreConditional (_, _, .Data) => (pure (E_SAMO_Addr_Align ()))
  | .Atomic (_, _, _, .Data, .Data) => (pure (E_SAMO_Addr_Align ()))
  | .Load .ShadowStack => (pure (E_SAMO_Addr_Align ()))
  | .Store .ShadowStack => (pure (E_SAMO_Addr_Align ()))
  | .Atomic (_, _, _, .ShadowStack, .ShadowStack) => (pure (E_SAMO_Addr_Align ()))
  | .LoadExecute p =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/core/mem_type_utils.sail"
      75
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadExecute.")))
  | .LoadReserved (_, _, p) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/core/mem_type_utils.sail"
      76
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadReserved.")))
  | .StoreConditional (_, _, p) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/core/mem_type_utils.sail"
      77
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for StoreConditional.")))
  | .Atomic (_, _, _, rp, wp) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/core/mem_type_utils.sail"
      78
      (HAppend.hAppend "Invalid payloads ("
        (HAppend.hAppend (mem_payload_name_forwards rp)
          (HAppend.hAppend ", " (HAppend.hAppend (mem_payload_str_forwards wp) ") for Atomic.")))))
  | .CacheAccess (.CB_manage _) => (pure (E_SAMO_Addr_Align ()))
  | .CacheAccess (.CB_zero ()) => (pure (E_SAMO_Addr_Align ()))
  | .CacheAccess (.CB_prefetch p) =>
    (match p with
    | .PREFETCH_R => (pure (E_Load_Addr_Align ()))
    | .PREFETCH_W => (pure (E_SAMO_Addr_Align ()))
    | .PREFETCH_I => (pure (E_Fetch_Addr_Align ())))

/-- Type quantifiers: x_2 : Nat, x_2 ≥ 0, 0 < x_2 ∧ x_2 ≤ max_mem_access -/
def mem_write_callback (x_0 : String) (x_1 : (BitVec (if ( 32 = 32  : Bool) then 34 else 64))) (x_2 : Nat) (x_3 : (BitVec (8 * x_2))) : Unit :=
  ()

/-- Type quantifiers: x_2 : Nat, x_2 ≥ 0, 0 < x_2 ∧ x_2 ≤ max_mem_access -/
def mem_read_callback (x_0 : String) (x_1 : (BitVec (if ( 32 = 32  : Bool) then 34 else 64))) (x_2 : Nat) (x_3 : (BitVec (8 * x_2))) : Unit :=
  ()

def mem_exception_callback (x_0 : (BitVec (if ( 32 = 32  : Bool) then 34 else 64))) (x_1 : (BitVec 6)) : Unit :=
  ()

def pc_write_callback (x_0 : (BitVec 32)) : Unit :=
  ()

def xreg_full_write_callback (x_0 : String) (x_1 : regidx) (x_2 : (BitVec 32)) : Unit :=
  ()

def csr_full_write_callback (x_0 : String) (x_1 : (BitVec 12)) (x_2 : (BitVec 32)) : Unit :=
  ()

def redirect_callback (x_0 : (BitVec 32)) : Unit :=
  ()

def csr_name_map_backwards (arg_ : String) : SailM (BitVec 12) := do
  match arg_ with
  | "misa" => (pure 0x301#12)
  | "mstatus" => (pure 0x300#12)
  | "mstatush" => (pure 0x310#12)
  | "hstatus" => (pure 0x600#12)
  | "mseccfg" => (pure 0x747#12)
  | "mseccfgh" => (pure 0x757#12)
  | "menvcfg" => (pure 0x30A#12)
  | "menvcfgh" => (pure 0x31A#12)
  | "senvcfg" => (pure 0x10A#12)
  | "henvcfg" => (pure 0x60A#12)
  | "henvcfgh" => (pure 0x61A#12)
  | "mcause" => (pure 0x342#12)
  | "mtval" => (pure 0x343#12)
  | "mscratch" => (pure 0x340#12)
  | "scounteren" => (pure 0x106#12)
  | "hcounteren" => (pure 0x606#12)
  | "mcounteren" => (pure 0x306#12)
  | "mcountinhibit" => (pure 0x320#12)
  | "mvendorid" => (pure 0xF11#12)
  | "marchid" => (pure 0xF12#12)
  | "mimpid" => (pure 0xF13#12)
  | "mhartid" => (pure 0xF14#12)
  | "mconfigptr" => (pure 0xF15#12)
  | "mtinst" => (pure 0x34A#12)
  | "mtval2" => (pure 0x34B#12)
  | "htimedelta" => (pure 0x605#12)
  | "htimedeltah" => (pure 0x615#12)
  | "htval" => (pure 0x643#12)
  | "htinst" => (pure 0x64A#12)
  | "vsstatus" => (pure 0x200#12)
  | "sstatus" => (pure 0x100#12)
  | "vsscratch" => (pure 0x240#12)
  | "vscause" => (pure 0x242#12)
  | "vstval" => (pure 0x243#12)
  | "sscratch" => (pure 0x140#12)
  | "scause" => (pure 0x142#12)
  | "stval" => (pure 0x143#12)
  | "tselect" => (pure 0x7A0#12)
  | "tdata1" => (pure 0x7A1#12)
  | "tdata2" => (pure 0x7A2#12)
  | "tdata3" => (pure 0x7A3#12)
  | "mcycle" => (pure 0xB00#12)
  | "minstret" => (pure 0xB02#12)
  | "mcycleh" => (pure 0xB80#12)
  | "minstreth" => (pure 0xB82#12)
  | "mhpmevent3" => (pure 0x323#12)
  | "mhpmevent4" => (pure 0x324#12)
  | "mhpmevent5" => (pure 0x325#12)
  | "mhpmevent6" => (pure 0x326#12)
  | "mhpmevent7" => (pure 0x327#12)
  | "mhpmevent8" => (pure 0x328#12)
  | "mhpmevent9" => (pure 0x329#12)
  | "mhpmevent10" => (pure 0x32A#12)
  | "mhpmevent11" => (pure 0x32B#12)
  | "mhpmevent12" => (pure 0x32C#12)
  | "mhpmevent13" => (pure 0x32D#12)
  | "mhpmevent14" => (pure 0x32E#12)
  | "mhpmevent15" => (pure 0x32F#12)
  | "mhpmevent16" => (pure 0x330#12)
  | "mhpmevent17" => (pure 0x331#12)
  | "mhpmevent18" => (pure 0x332#12)
  | "mhpmevent19" => (pure 0x333#12)
  | "mhpmevent20" => (pure 0x334#12)
  | "mhpmevent21" => (pure 0x335#12)
  | "mhpmevent22" => (pure 0x336#12)
  | "mhpmevent23" => (pure 0x337#12)
  | "mhpmevent24" => (pure 0x338#12)
  | "mhpmevent25" => (pure 0x339#12)
  | "mhpmevent26" => (pure 0x33A#12)
  | "mhpmevent27" => (pure 0x33B#12)
  | "mhpmevent28" => (pure 0x33C#12)
  | "mhpmevent29" => (pure 0x33D#12)
  | "mhpmevent30" => (pure 0x33E#12)
  | "mhpmevent31" => (pure 0x33F#12)
  | "mhpmcounter3" => (pure 0xB03#12)
  | "mhpmcounter4" => (pure 0xB04#12)
  | "mhpmcounter5" => (pure 0xB05#12)
  | "mhpmcounter6" => (pure 0xB06#12)
  | "mhpmcounter7" => (pure 0xB07#12)
  | "mhpmcounter8" => (pure 0xB08#12)
  | "mhpmcounter9" => (pure 0xB09#12)
  | "mhpmcounter10" => (pure 0xB0A#12)
  | "mhpmcounter11" => (pure 0xB0B#12)
  | "mhpmcounter12" => (pure 0xB0C#12)
  | "mhpmcounter13" => (pure 0xB0D#12)
  | "mhpmcounter14" => (pure 0xB0E#12)
  | "mhpmcounter15" => (pure 0xB0F#12)
  | "mhpmcounter16" => (pure 0xB10#12)
  | "mhpmcounter17" => (pure 0xB11#12)
  | "mhpmcounter18" => (pure 0xB12#12)
  | "mhpmcounter19" => (pure 0xB13#12)
  | "mhpmcounter20" => (pure 0xB14#12)
  | "mhpmcounter21" => (pure 0xB15#12)
  | "mhpmcounter22" => (pure 0xB16#12)
  | "mhpmcounter23" => (pure 0xB17#12)
  | "mhpmcounter24" => (pure 0xB18#12)
  | "mhpmcounter25" => (pure 0xB19#12)
  | "mhpmcounter26" => (pure 0xB1A#12)
  | "mhpmcounter27" => (pure 0xB1B#12)
  | "mhpmcounter28" => (pure 0xB1C#12)
  | "mhpmcounter29" => (pure 0xB1D#12)
  | "mhpmcounter30" => (pure 0xB1E#12)
  | "mhpmcounter31" => (pure 0xB1F#12)
  | "mhpmcounter3h" => (pure 0xB83#12)
  | "mhpmcounter4h" => (pure 0xB84#12)
  | "mhpmcounter5h" => (pure 0xB85#12)
  | "mhpmcounter6h" => (pure 0xB86#12)
  | "mhpmcounter7h" => (pure 0xB87#12)
  | "mhpmcounter8h" => (pure 0xB88#12)
  | "mhpmcounter9h" => (pure 0xB89#12)
  | "mhpmcounter10h" => (pure 0xB8A#12)
  | "mhpmcounter11h" => (pure 0xB8B#12)
  | "mhpmcounter12h" => (pure 0xB8C#12)
  | "mhpmcounter13h" => (pure 0xB8D#12)
  | "mhpmcounter14h" => (pure 0xB8E#12)
  | "mhpmcounter15h" => (pure 0xB8F#12)
  | "mhpmcounter16h" => (pure 0xB90#12)
  | "mhpmcounter17h" => (pure 0xB91#12)
  | "mhpmcounter18h" => (pure 0xB92#12)
  | "mhpmcounter19h" => (pure 0xB93#12)
  | "mhpmcounter20h" => (pure 0xB94#12)
  | "mhpmcounter21h" => (pure 0xB95#12)
  | "mhpmcounter22h" => (pure 0xB96#12)
  | "mhpmcounter23h" => (pure 0xB97#12)
  | "mhpmcounter24h" => (pure 0xB98#12)
  | "mhpmcounter25h" => (pure 0xB99#12)
  | "mhpmcounter26h" => (pure 0xB9A#12)
  | "mhpmcounter27h" => (pure 0xB9B#12)
  | "mhpmcounter28h" => (pure 0xB9C#12)
  | "mhpmcounter29h" => (pure 0xB9D#12)
  | "mhpmcounter30h" => (pure 0xB9E#12)
  | "mhpmcounter31h" => (pure 0xB9F#12)
  | "hgeie" => (pure 0x607#12)
  | "hgeip" => (pure 0xE12#12)
  | "mie" => (pure 0x304#12)
  | "mip" => (pure 0x344#12)
  | "medeleg" => (pure 0x302#12)
  | "medelegh" => (pure 0x312#12)
  | "mideleg" => (pure 0x303#12)
  | "hvip" => (pure 0x645#12)
  | "hie" => (pure 0x604#12)
  | "hip" => (pure 0x644#12)
  | "hedeleg" => (pure 0x602#12)
  | "hideleg" => (pure 0x603#12)
  | "hedelegh" => (pure 0x612#12)
  | "sip" => (pure 0x144#12)
  | "sie" => (pure 0x104#12)
  | "vsie" => (pure 0x204#12)
  | "vsip" => (pure 0x244#12)
  | "vstvec" => (pure 0x205#12)
  | "vsepc" => (pure 0x241#12)
  | "stvec" => (pure 0x105#12)
  | "sepc" => (pure 0x141#12)
  | "mtvec" => (pure 0x305#12)
  | "mepc" => (pure 0x341#12)
  | "pmpcfg0" => (pure 0x3A0#12)
  | "pmpcfg1" => (pure 0x3A1#12)
  | "pmpcfg2" => (pure 0x3A2#12)
  | "pmpcfg3" => (pure 0x3A3#12)
  | "pmpcfg4" => (pure 0x3A4#12)
  | "pmpcfg5" => (pure 0x3A5#12)
  | "pmpcfg6" => (pure 0x3A6#12)
  | "pmpcfg7" => (pure 0x3A7#12)
  | "pmpcfg8" => (pure 0x3A8#12)
  | "pmpcfg9" => (pure 0x3A9#12)
  | "pmpcfg10" => (pure 0x3AA#12)
  | "pmpcfg11" => (pure 0x3AB#12)
  | "pmpcfg12" => (pure 0x3AC#12)
  | "pmpcfg13" => (pure 0x3AD#12)
  | "pmpcfg14" => (pure 0x3AE#12)
  | "pmpcfg15" => (pure 0x3AF#12)
  | "pmpaddr0" => (pure 0x3B0#12)
  | "pmpaddr1" => (pure 0x3B1#12)
  | "pmpaddr2" => (pure 0x3B2#12)
  | "pmpaddr3" => (pure 0x3B3#12)
  | "pmpaddr4" => (pure 0x3B4#12)
  | "pmpaddr5" => (pure 0x3B5#12)
  | "pmpaddr6" => (pure 0x3B6#12)
  | "pmpaddr7" => (pure 0x3B7#12)
  | "pmpaddr8" => (pure 0x3B8#12)
  | "pmpaddr9" => (pure 0x3B9#12)
  | "pmpaddr10" => (pure 0x3BA#12)
  | "pmpaddr11" => (pure 0x3BB#12)
  | "pmpaddr12" => (pure 0x3BC#12)
  | "pmpaddr13" => (pure 0x3BD#12)
  | "pmpaddr14" => (pure 0x3BE#12)
  | "pmpaddr15" => (pure 0x3BF#12)
  | "pmpaddr16" => (pure 0x3C0#12)
  | "pmpaddr17" => (pure 0x3C1#12)
  | "pmpaddr18" => (pure 0x3C2#12)
  | "pmpaddr19" => (pure 0x3C3#12)
  | "pmpaddr20" => (pure 0x3C4#12)
  | "pmpaddr21" => (pure 0x3C5#12)
  | "pmpaddr22" => (pure 0x3C6#12)
  | "pmpaddr23" => (pure 0x3C7#12)
  | "pmpaddr24" => (pure 0x3C8#12)
  | "pmpaddr25" => (pure 0x3C9#12)
  | "pmpaddr26" => (pure 0x3CA#12)
  | "pmpaddr27" => (pure 0x3CB#12)
  | "pmpaddr28" => (pure 0x3CC#12)
  | "pmpaddr29" => (pure 0x3CD#12)
  | "pmpaddr30" => (pure 0x3CE#12)
  | "pmpaddr31" => (pure 0x3CF#12)
  | "pmpaddr32" => (pure 0x3D0#12)
  | "pmpaddr33" => (pure 0x3D1#12)
  | "pmpaddr34" => (pure 0x3D2#12)
  | "pmpaddr35" => (pure 0x3D3#12)
  | "pmpaddr36" => (pure 0x3D4#12)
  | "pmpaddr37" => (pure 0x3D5#12)
  | "pmpaddr38" => (pure 0x3D6#12)
  | "pmpaddr39" => (pure 0x3D7#12)
  | "pmpaddr40" => (pure 0x3D8#12)
  | "pmpaddr41" => (pure 0x3D9#12)
  | "pmpaddr42" => (pure 0x3DA#12)
  | "pmpaddr43" => (pure 0x3DB#12)
  | "pmpaddr44" => (pure 0x3DC#12)
  | "pmpaddr45" => (pure 0x3DD#12)
  | "pmpaddr46" => (pure 0x3DE#12)
  | "pmpaddr47" => (pure 0x3DF#12)
  | "pmpaddr48" => (pure 0x3E0#12)
  | "pmpaddr49" => (pure 0x3E1#12)
  | "pmpaddr50" => (pure 0x3E2#12)
  | "pmpaddr51" => (pure 0x3E3#12)
  | "pmpaddr52" => (pure 0x3E4#12)
  | "pmpaddr53" => (pure 0x3E5#12)
  | "pmpaddr54" => (pure 0x3E6#12)
  | "pmpaddr55" => (pure 0x3E7#12)
  | "pmpaddr56" => (pure 0x3E8#12)
  | "pmpaddr57" => (pure 0x3E9#12)
  | "pmpaddr58" => (pure 0x3EA#12)
  | "pmpaddr59" => (pure 0x3EB#12)
  | "pmpaddr60" => (pure 0x3EC#12)
  | "pmpaddr61" => (pure 0x3ED#12)
  | "pmpaddr62" => (pure 0x3EE#12)
  | "pmpaddr63" => (pure 0x3EF#12)
  | "fflags" => (pure 0x001#12)
  | "frm" => (pure 0x002#12)
  | "fcsr" => (pure 0x003#12)
  | "vstart" => (pure 0x008#12)
  | "vxsat" => (pure 0x009#12)
  | "vxrm" => (pure 0x00A#12)
  | "vcsr" => (pure 0x00F#12)
  | "vl" => (pure 0xC20#12)
  | "vtype" => (pure 0xC21#12)
  | "vlenb" => (pure 0xC22#12)
  | "mcyclecfg" => (pure 0x321#12)
  | "mcyclecfgh" => (pure 0x721#12)
  | "minstretcfg" => (pure 0x322#12)
  | "minstretcfgh" => (pure 0x722#12)
  | "mstateen0" => (pure 0x30C#12)
  | "mstateen1" => (pure 0x30D#12)
  | "mstateen2" => (pure 0x30E#12)
  | "mstateen3" => (pure 0x30F#12)
  | "mstateen0h" => (pure 0x31C#12)
  | "mstateen1h" => (pure 0x31D#12)
  | "mstateen2h" => (pure 0x31E#12)
  | "mstateen3h" => (pure 0x31F#12)
  | "hstateen0" => (pure 0x60C#12)
  | "hstateen1" => (pure 0x60D#12)
  | "hstateen2" => (pure 0x60E#12)
  | "hstateen3" => (pure 0x60F#12)
  | "hstateen0h" => (pure 0x61C#12)
  | "hstateen1h" => (pure 0x61D#12)
  | "hstateen2h" => (pure 0x61E#12)
  | "hstateen3h" => (pure 0x61F#12)
  | "sstateen0" => (pure 0x10C#12)
  | "sstateen1" => (pure 0x10D#12)
  | "sstateen2" => (pure 0x10E#12)
  | "sstateen3" => (pure 0x10F#12)
  | "hgatp" => (pure 0x680#12)
  | "vsatp" => (pure 0x280#12)
  | "satp" => (pure 0x180#12)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def csr_name_write_callback (name : String) (value : (BitVec 32)) : SailM Unit := do
  let csr ← do (csr_name_map_backwards name)
  (pure (csr_full_write_callback name csr value))

def zero_reg : regtype := (zeros (n := 32))

def regval_from_reg (r : (BitVec 32)) : (BitVec 32) :=
  r

def regval_into_reg (v : (BitVec 32)) : (BitVec 32) :=
  v

def encdec_reg_forwards (arg_ : regidx) : (BitVec 5) :=
  match arg_ with
  | .Regidx r => (zero_extend (m := 5) r)

def encdec_reg_backwards (arg_ : (BitVec 5)) : SailM regidx := do
  let r := arg_
  if (((not base_E_enabled) || ((BitVec.access r 4) == 0#1)) : Bool)
  then (pure (Regidx (Sail.BitVec.extractLsb r (regidx_bit_width -i 1) 0)))
  else
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_reg_forwards_matches (arg_ : regidx) : Bool :=
  match arg_ with
  | .Regidx r => true

def encdec_reg_backwards_matches (arg_ : (BitVec 5)) : Bool :=
  let r := arg_
  if (((not base_E_enabled) || ((BitVec.access r 4) == 0#1)) : Bool)
  then true
  else false

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

def _update_PTE_Flags_A (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_PTE_Flags_A (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_Pmpcfg_ent_A (v : (BitVec 8)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 4 3)

def _update_PTE_Flags_D (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_PTE_Flags_D (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PTE_Flags_G (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_Pmpcfg_ent_L (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PTE_Ext_N (v : (BitVec 10)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PTE_Flags_R (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_Pmpcfg_ent_R (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PTE_Flags_U (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PTE_Flags_V (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PTE_Flags_W (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_Pmpcfg_ent_W (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PTE_Flags_X (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_Pmpcfg_ent_X (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def sys_guest_page_fault_writes_htval : Bool := true

def virtual_memory_supported (_ : Unit) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_Sv32)) || ((← (currentlyEnabled Ext_Sv39)) || ((← (currentlyEnabled
              Ext_Sv48)) || (← (currentlyEnabled Ext_Sv57))))))

def _get_Mstatus_MPP (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 12 11)

def _get_Mstatus_MPRV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_Mstatus_MPV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)

def _get_Mstatus_MXR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_Mstatus_SUM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_Hstatus_HUKTE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_Hstatus_VGEIN (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 17 12)

def _get_Hgatp32_Mode (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_Satp32_Mode (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_Hgatp32_PPN (v : (BitVec 32)) : (BitVec 22) :=
  (Sail.BitVec.extractLsb v 21 0)

def _get_Satp32_PPN (v : (BitVec 32)) : (BitVec 22) :=
  (Sail.BitVec.extractLsb v 21 0)

def _get_Hgatp32_VMID (v : (BitVec 32)) : (BitVec 7) :=
  (Sail.BitVec.extractLsb v 28 22)

def Mk_Hgatp32 (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_Satp32_Asid (v : (BitVec 32)) : (BitVec 9) :=
  (Sail.BitVec.extractLsb v 30 22)

def Mk_Satp32 (v : (BitVec 32)) : (BitVec 32) :=
  v

def architecture (priv : Privilege) : SailM Architecture := SailME.run do
  SailME.throw (RV32 : Architecture)
  (architecture_bits_backwards
    (← do
      assert false "Pattern match failure at /private/tmp/airbender-sail-integration/model/model/core/sys_regs.sail:1293.20-1299.3"
      throw Error.Exit))

def Mk_Minterrupts (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_Minterrupts_MEI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_Minterrupts_MEI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_Minterrupts_MSI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_Minterrupts_MSI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_Minterrupts_MTI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_Minterrupts_SEI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_Minterrupts_SEI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_Minterrupts_SGEI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_Minterrupts_SSI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Minterrupts_SSI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_Minterrupts_STI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_Minterrupts_VSEI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def hgei_mask : xlenbits := (zero_extend (m := 32) ((ones (n := geilen)) +++ 0#1))

def guest_external_interrupts_pending (_ : Unit) : SailM (BitVec 32) := do
  readReg sig_hgeip

def read_hgeip (_ : Unit) : SailM (BitVec 32) := do
  (pure ((← (guest_external_interrupts_pending ())) &&& hgei_mask))

def selected_vgein_in_hgeip (_ : Unit) : SailM (BitVec 1) := do
  let vgein ← do (pure (BitVec.toNatInt (_get_Hstatus_VGEIN (← readReg hstatus))))
  if (((vgein >b 0) && (vgein ≤b geilen)) : Bool)
  then
    (do
      let hgeip ← do (read_hgeip ())
      (pure (BitVec.join1 [(BitVec.access hgeip vgein)])))
  else (pure 0#1)

def supported_interrupts_mask (i : (BitVec 32)) : (BitVec 32) :=
  (Mk_Minterrupts
    ((_update_Minterrupts_SGEI
        (_update_Minterrupts_STI
          (_update_Minterrupts_SSI
            (_update_Minterrupts_SEI
              (_update_Minterrupts_MTI
                (_update_Minterrupts_MSI
                  (_update_Minterrupts_MEI (Mk_Minterrupts (ones (n := 32)))
                    (bool_to_bit plat_has_mei)) (bool_to_bit plat_has_msi))
                (bool_to_bit plat_has_mti)) (bool_to_bit plat_has_sei)) (bool_to_bit plat_has_ssi))
          (bool_to_bit plat_has_sti)) (bool_to_bit (geilen >b 0))) &&& i))

def sig_external_interrupts_pending (hgeie_val : (BitVec 32)) : SailM (BitVec 32) := do
  (pure (_update_Minterrupts_VSEI
      (_update_Minterrupts_SGEI
        (_update_Minterrupts_SEI
          (_update_Minterrupts_MEI (Mk_Minterrupts (zeros (n := 32))) (← readReg sig_meip))
          (← do
            if ((← (currentlyEnabled Ext_S)) : Bool)
            then readReg sig_seip
            else (pure 0#1)))
        (← do
          if ((← (currentlyEnabled Ext_H)) : Bool)
          then (pure (bool_to_bit (((← readReg sig_hgeip) &&& hgeie_val) != (zeros (n := 32)))))
          else (pure 0#1)))
      (← do
        if ((← (currentlyEnabled Ext_H)) : Bool)
        then (selected_vgein_in_hgeip ())
        else (pure 0#1))))

def external_interrupts_pending (hgeie_val : (BitVec 32)) : SailM (BitVec 32) := do
  if (plat_have_sig : Bool)
  then (sig_external_interrupts_pending hgeie_val)
  else (pure (Mk_Minterrupts (zeros (n := 32))))

def sig_supervisor_software_interrupt_pending (_ : Unit) : SailM (BitVec 1) := do
  readReg sig_ssip

def supervisor_software_interrupt_pending (_ : Unit) : SailM (BitVec 1) := do
  if (plat_have_sig : Bool)
  then (sig_supervisor_software_interrupt_pending ())
  else (pure 0#1)

def read_mip (read_type : XipReadType) : SailM (BitVec 32) := do
  match read_type with
  | .IncludePlatformInterrupts =>
    (do
      let platform_interrupts ← do
        (pure (supported_interrupts_mask
            (_update_Minterrupts_SSI (← (external_interrupts_pending (← readReg hgeie)))
              (← do
                if ((← (currentlyEnabled Ext_S)) : Bool)
                then (supervisor_software_interrupt_pending ())
                else (pure 0#1)))))
      (pure (Mk_Minterrupts ((← readReg mip) ||| platform_interrupts))))
  | .ExcludePlatformInterrupts => readReg mip

def ext_control_check_pc (_pc : (BitVec 32)) : (Option Unit) :=
  none

/-- Type quantifiers: _width : Nat, 1 ≤ _width ∧ _width ≤ 4096 -/
def ext_data_get_addr (base : regidx) (offset : (BitVec 32)) (_access : (MemoryAccessType mem_payload)) (_width : Nat) : SailM (Ext_DataAddr_Check Unit) := do
  let addr ← do (pure (Virtaddr ((← (rX_bits base)) + offset)))
  (pure (Ext_DataAddr_OK addr))

def exception_context (e : ExceptionType) (excinfo : (BitVec 32)) : SailM ExceptionContext := do
  (pure { trap := e
          excinfo_is_gva := ← (inVirtualPrivilege ())
          excinfo := excinfo
          excinfo2 := none
          excinst := none
          excinst_offset := (zeros (n := 5))
          ext := none })

/-- Type quantifiers: k_ex436219_ : Bool -/
def make_exception_context (trap : ExceptionType) (excinfo : (BitVec 32)) (excinfo_is_gva : Bool) (excinfo2 : (Option (BitVec 32))) : ExceptionContext :=
  { trap := trap
    excinfo_is_gva := excinfo_is_gva
    excinfo := excinfo
    excinfo2 := excinfo2
    excinst := none
    excinst_offset := (zeros (n := 5))
    ext := none }

def sys_pmp_count : Int := 16

def sys_pmp_grain : Nat := 0

def pmpAddrMatchType_encdec_backwards (arg_ : (BitVec 2)) : PmpAddrMatchType :=
  match arg_ with
  | 0b00 => OFF
  | 0b01 => TOR
  | 0b10 => NA4
  | _ => NAPOT

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 63 -/
def pmpReadAddrReg (n : Nat) : SailM (BitVec 32) := do
  let G := sys_pmp_grain
  let match_type ← do (pure (_get_Pmpcfg_ent_A (GetElem?.getElem! (← readReg pmpcfg_n) n)))
  let addr ← do (pure (GetElem?.getElem! (← readReg pmpaddr_n) n))
  match (BitVec.access match_type 1) with
  | 1 =>
    (if ((G ≥b 2) : Bool)
    then
      (let mask : xlenbits := (zero_extend (m := 32) (ones (n := (Min.min (G -i 1) xlen))))
      (pure (addr ||| mask)))
    else (pure addr))
  | 0 =>
    (if ((G ≥b 1) : Bool)
    then
      (let mask : xlenbits := (zero_extend (m := 32) (ones (n := (Min.min G xlen))))
      (pure (addr &&& (Complement.complement mask))))
    else (pure addr))
  | _ => (pure addr)

def pmpLocked (cfg : (BitVec 8)) : Bool :=
  ((_get_Pmpcfg_ent_L cfg) == 1#1)

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
    (internal_error "/private/tmp/airbender-sail-integration/model/model/pmp/pmp_control.sail" 36
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadExecute.")))
  | .LoadReserved (_, _, p) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/pmp/pmp_control.sail" 37
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadReserved.")))
  | .StoreConditional (_, _, p) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/pmp/pmp_control.sail" 38
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for StoreConditional.")))
  | .Atomic (_, _, _, rp, wp) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/pmp/pmp_control.sail" 39
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
      assert (sys_pmp_grain <b 1) "NA4 cannot be selected when PMP grain G >= 1."
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

def _get_PTE_Ext_reserved (v : (BitVec 10)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

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

def get_pmm (eff_privilege : Privilege) : SailM PointerMaskingMode := do
  match eff_privilege with
  | .Machine => (pure (pmm_mode_backwards (_get_Seccfg_PMM (← readReg mseccfg))))
  | .Supervisor => (pure (pmm_mode_backwards (_get_MEnvcfg_PMM (← readReg menvcfg))))
  | .User =>
    (do
      if ((← (currentlyEnabled Ext_S)) : Bool)
      then (pure (pmm_mode_backwards (_get_SEnvcfg_PMM (← (read_senvcfg ())))))
      else (pure (pmm_mode_backwards (_get_MEnvcfg_PMM (← readReg menvcfg)))))
  | .VirtualSupervisor => (pure (pmm_mode_backwards (_get_HEnvcfg_PMM (← (read_henvcfg ())))))
  | .VirtualUser => (pure (pmm_mode_backwards (_get_SEnvcfg_PMM (← (read_senvcfg ())))))

def is_pmm_applicable (access : (MemoryAccessType mem_payload)) (eff_privilege : Privilege) : SailM Bool := do
  let mxr_in_effect ← (( do
    match eff_privilege with
    | .Machine => (pure false)
    | .VirtualSupervisor =>
      (pure (((_get_Mstatus_MXR (← readReg mstatus)) == 1#1) || ((_get_Mstatus_MXR
              (← readReg vsstatus)) == 1#1)))
    | .VirtualUser =>
      (pure (((_get_Mstatus_MXR (← readReg mstatus)) == 1#1) || ((_get_Mstatus_MXR
              (← readReg vsstatus)) == 1#1)))
    | _ => (pure ((_get_Mstatus_MXR (← readReg mstatus)) == 1#1)) ) : SailM Bool )
  (pure ((bne access (InstructionFetch ())) && ((bne access (LoadExecute Data)) && ((bne access
            (Load PageTableEntry)) && ((bne access (Store PageTableEntry)) && ((not mxr_in_effect) && (xlen == 64)))))))

def pmlen_of_mode (pmm : PointerMaskingMode) : SailM Int := do
  match pmm with
  | .PMM_Disabled => (pure 0)
  | .PMM_PMLEN_7 => (pure 7)
  | .PMM_PMLEN_16 => (pure 16)
  | .PMM_Reserved =>
    (do
      (internal_error
        "/private/tmp/airbender-sail-integration/model/model/extensions/pointer_masking/pm_utils.sail"
        52 "Invalid (reserved) pointer masking mode.")
      (pure 0))

def get_pmlen (access : (MemoryAccessType mem_payload)) (eff_privilege : Privilege) : SailM Int := do
  if ((← (is_pmm_applicable access eff_privilege)) : Bool)
  then (pmlen_of_mode (← (get_pmm eff_privilege)))
  else (pure 0)

/-- Type quantifiers: pmlen : Nat, List.elem pmlen [0, 7, 16] -/
def pm_transform_VA (typ_0 : virtaddr) (pmlen : Nat) : virtaddr :=
  let .Virtaddr effective_address : virtaddr := typ_0
  (Virtaddr
    (sign_extend (m := 32) (Sail.BitVec.extractLsb effective_address ((xlen -i pmlen) -i 1) 0)))

/-- Type quantifiers: pmlen : Nat, List.elem pmlen [0, 7, 16] -/
def pm_transform_PA (typ_0 : virtaddr) (pmlen : Nat) : virtaddr :=
  let .Virtaddr effective_address : virtaddr := typ_0
  (Virtaddr
    (zero_extend (m := 32) (Sail.BitVec.extractLsb effective_address ((xlen -i pmlen) -i 1) 0)))

def effectivePrivilege (access : (MemoryAccessType mem_payload)) (m : (BitVec 64)) (priv : Privilege) : SailM Privilege := do
  if (((not (is_implicit_access access)) && ((_get_Mstatus_MPRV m) == 1#1)) : Bool)
  then
    (privLevel_bits_forwards
      ((_get_Mstatus_MPP m), (if (((_get_Mstatus_MPP m) == 0b11#2) : Bool)
      then 0#1
      else (_get_Mstatus_MPV m))))
  else (pure priv)

/-- Type quantifiers: k_t : Type -/
def MemoryOpResult_drop_meta (r : (Result (k_t × Unit) (physaddr × ExceptionType))) : (Result k_t (physaddr × ExceptionType)) :=
  match r with
  | .Ok (v, _m) => (Ok v)
  | .Err e => (Err e)

def SIG_VERSION_OFFSET := 0

def SIG_PLATFORM_OFFSET := 4

def SIG_GUEST_OFFSET := 8

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def sig_load (access : (MemoryAccessType mem_payload)) (addr : physaddr) (width : Nat) : SailM (Result (BitVec (8 * width)) (physaddr × ExceptionType)) := do
  let .Physaddr paddr := addr
  let VERSION := 0x00010001#32
  if (((width != 4) || ((Sail.BitVec.extractLsb paddr 1 0) != (zeros (n := ((1 -i 0) +i 1))))) : Bool)
  then (pure (Err (addr, (← (accessFaultFromAccessType access)))))
  else
    (do
      if ((paddr == (BitVec.addInt plat_sig_base SIG_VERSION_OFFSET)) : Bool)
      then (pure (Ok VERSION))
      else
        (do
          if ((paddr == (BitVec.addInt plat_sig_base SIG_PLATFORM_OFFSET)) : Bool)
          then (pure (Ok (zeros (n := (8 *i width)))))
          else
            (do
              if (((paddr == (BitVec.addInt plat_sig_base SIG_GUEST_OFFSET)) && (← (currentlyEnabled
                       Ext_H))) : Bool)
              then (pure (Ok (zeros (n := (8 *i width)))))
              else (pure (Err (addr, (← (accessFaultFromAccessType access))))))))

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def sig_store (addr : physaddr) (width : Nat) (data : (BitVec (8 * width))) : SailM (Result Bool (physaddr × ExceptionType)) := do
  let .Physaddr paddr := addr
  if (((width != 4) || ((Sail.BitVec.extractLsb paddr 1 0) != (zeros (n := ((1 -i 0) +i 1))))) : Bool)
  then (pure (Err (addr, (E_SAMO_Access_Fault ()))))
  else
    (do
      if ((paddr == (BitVec.addInt plat_sig_base SIG_VERSION_OFFSET)) : Bool)
      then (pure (Ok true))
      else
        (do
          if ((paddr == (BitVec.addInt plat_sig_base SIG_PLATFORM_OFFSET)) : Bool)
          then
            (do
              let value := (BitVec.access data 31)
              let data := (Mk_Minterrupts (zero_extend (m := 32) data))
              if (((Sail.BitVec.extractLsb
                     (_update_Minterrupts_SSI
                       (_update_Minterrupts_MSI
                         (_update_Minterrupts_SEI (_update_Minterrupts_MEI data 0#1) 0#1) 0#1) 0#1)
                     30 0) != (zeros (n := ((30 -i 0) +i 1)))) : Bool)
              then (pure (Err (addr, (E_SAMO_Access_Fault ()))))
              else
                (do
                  if (((_get_Minterrupts_MEI data) == 1#1) : Bool)
                  then writeReg sig_meip value
                  else (pure ())
                  if (((_get_Minterrupts_SEI data) == 1#1) : Bool)
                  then writeReg sig_seip value
                  else (pure ())
                  if (((_get_Minterrupts_MSI data) == 1#1) : Bool)
                  then writeReg sig_msip value
                  else (pure ())
                  if (((_get_Minterrupts_SSI data) == 1#1) : Bool)
                  then writeReg sig_ssip value
                  else (pure ())
                  (csr_name_write_callback "mip" (← (read_mip IncludePlatformInterrupts)))
                  (pure (Ok true))))
          else
            (do
              if (((paddr == (BitVec.addInt plat_sig_base SIG_GUEST_OFFSET)) && (← (currentlyEnabled
                       Ext_H))) : Bool)
              then
                (do
                  let value := (BitVec.access data 31)
                  let guest := (BitVec.toNatInt (Sail.BitVec.extractLsb data 5 0))
                  if (((Sail.BitVec.extractLsb data 30 6) != (zeros (n := ((30 -i 6) +i 1)))) : Bool)
                  then (pure (Err (addr, (E_SAMO_Access_Fault ()))))
                  else
                    (do
                      if (((guest == 0) || (guest >b geilen)) : Bool)
                      then (pure (Err (addr, (E_SAMO_Access_Fault ()))))
                      else
                        (do
                          writeReg sig_hgeip (BitVec.update (← readReg sig_hgeip) guest value)
                          (csr_name_write_callback "hgeip" (← (read_hgeip ())))
                          (csr_name_write_callback "mip" (← (read_mip IncludePlatformInterrupts)))
                          (pure (Ok true)))))
              else (pure (Err (addr, (E_SAMO_Access_Fault ())))))))

def htif_tohost_size := 8

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_clint (typ_0 : physaddr) (width : Nat) : SailM Bool := do
  let .Physaddr addr : physaddr := typ_0
  if ((not plat_have_clint) : Bool)
  then (pure false)
  else
    (do
      if (((BitVec.toNatInt (← readReg mhartid)) ≥b 4095) : Bool)
      then (pure false)
      else
        (let addr_int := (BitVec.toNatInt addr)
        let clint_base_int := (BitVec.toNatInt plat_clint_base)
        let clint_size_int := (BitVec.toNatInt plat_clint_size)
        (pure ((clint_base_int ≤b addr_int) && ((addr_int +i width) ≤b (clint_base_int +i clint_size_int))))))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_sig (typ_0 : physaddr) (width : Nat) : SailM Bool := do
  let .Physaddr addr : physaddr := typ_0
  if ((not plat_have_sig) : Bool)
  then (pure false)
  else
    (let addr_int := (BitVec.toNatInt addr)
    let sig_base_int := (BitVec.toNatInt plat_sig_base)
    let sig_size_int := (BitVec.toNatInt plat_sig_size)
    (pure ((sig_base_int ≤b addr_int) && ((addr_int +i width) ≤b (sig_base_int +i sig_size_int)))))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_htif_writable (typ_0 : physaddr) (width : Nat) : SailM Bool := do
  let .Physaddr addr : physaddr := typ_0
  match (← readReg htif_tohost_base) with
  | none => (pure false)
  | .some base =>
    (pure ((zopz0zI_u addr (BitVec.addInt base htif_tohost_size)) && (zopz0zK_u
          (BitVec.addInt addr width) base)))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_htif_readable (addr : physaddr) (width : Nat) : SailM Bool := do
  (within_htif_writable addr width)

def MSIP_BASE : physaddrbits := (zero_extend (m := 34) 0x00000#20)

def MTIMECMP_BASE : physaddrbits := (zero_extend (m := 34) 0x04000#20)

def MTIMECMP_BASE_HI : physaddrbits := (zero_extend (m := 34) 0x04004#20)

def MTIME_BASE : physaddrbits := (zero_extend (m := 34) 0x0BFF8#20)

def MTIME_BASE_HI : physaddrbits := (zero_extend (m := 34) 0x0BFFC#20)

/-- Type quantifiers: width : Nat, width ≥ 0, width > 0 -/
def clint_load (access : (MemoryAccessType mem_payload)) (paddr : physaddr) (width : Nat) : SailM (Result (BitVec (8 * width)) (physaddr × ExceptionType)) := do
  let hart_msip_addr ← do
    (pure (MSIP_BASE + (zero_extend (m := 34) ((← readReg mhartid) <<< 2))))
  let hart_mtimecmp_addr ← do
    (pure (MTIMECMP_BASE + (zero_extend (m := 34) ((← readReg mhartid) <<< 3))))
  let hart_mtimecmp_hi_addr ← do
    (pure (MTIMECMP_BASE_HI + (zero_extend (m := 34) ((← readReg mhartid) <<< 3))))
  let .Physaddr addr := paddr
  let addr := (addr - plat_clint_base)
  if (((addr == hart_msip_addr) && ((width == 8) || (width == 4))) : Bool)
  then
    (do
      if ((get_config_print_clint ()) : Bool)
      then
        (pure (print_endline
            (HAppend.hAppend "clint["
              (HAppend.hAppend (BitVec.toFormatted addr)
                (HAppend.hAppend "] -> " (BitVec.toFormatted (← readReg msip)))))))
      else (pure ())
      (pure (Ok (zero_extend (m := (8 *i width)) (← readReg msip)))))
  else
    (do
      if (((addr == hart_mtimecmp_addr) && (width == 4)) : Bool)
      then
        (do
          if ((get_config_print_clint ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "clint<4>["
                  (HAppend.hAppend (BitVec.toFormatted addr)
                    (HAppend.hAppend "] -> "
                      (BitVec.toFormatted (Sail.BitVec.extractLsb (← readReg mtimecmp) 31 0)))))))
          else (pure ())
          (pure (Ok (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg mtimecmp) 31 0)))))
      else
        (do
          if (((addr == hart_mtimecmp_addr) && (width == 8)) : Bool)
          then
            (do
              if ((get_config_print_clint ()) : Bool)
              then
                (pure (print_endline
                    (HAppend.hAppend "clint<8>["
                      (HAppend.hAppend (BitVec.toFormatted addr)
                        (HAppend.hAppend "] -> " (BitVec.toFormatted (← readReg mtimecmp)))))))
              else (pure ())
              (pure (Ok (zero_extend (m := 64) (← readReg mtimecmp)))))
          else
            (do
              if (((addr == hart_mtimecmp_hi_addr) && (width == 4)) : Bool)
              then
                (do
                  if ((get_config_print_clint ()) : Bool)
                  then
                    (pure (print_endline
                        (HAppend.hAppend "clint-hi<4>["
                          (HAppend.hAppend (BitVec.toFormatted addr)
                            (HAppend.hAppend "] -> "
                              (BitVec.toFormatted
                                (Sail.BitVec.extractLsb (← readReg mtimecmp) 63 32)))))))
                  else (pure ())
                  (pure (Ok
                      (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg mtimecmp) 63 32)))))
              else
                (do
                  if (((addr == MTIME_BASE) && (width == 4)) : Bool)
                  then
                    (do
                      if ((get_config_print_clint ()) : Bool)
                      then
                        (pure (print_endline
                            (HAppend.hAppend "clint["
                              (HAppend.hAppend (BitVec.toFormatted addr)
                                (HAppend.hAppend "] -> " (BitVec.toFormatted (← readReg mtime)))))))
                      else (pure ())
                      (pure (Ok
                          (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg mtime) 31 0)))))
                  else
                    (do
                      if (((addr == MTIME_BASE) && (width == 8)) : Bool)
                      then
                        (do
                          if ((get_config_print_clint ()) : Bool)
                          then
                            (pure (print_endline
                                (HAppend.hAppend "clint["
                                  (HAppend.hAppend (BitVec.toFormatted addr)
                                    (HAppend.hAppend "] -> "
                                      (BitVec.toFormatted (← readReg mtime)))))))
                          else (pure ())
                          (pure (Ok (zero_extend (m := 64) (← readReg mtime)))))
                      else
                        (do
                          if (((addr == MTIME_BASE_HI) && (width == 4)) : Bool)
                          then
                            (do
                              if ((get_config_print_clint ()) : Bool)
                              then
                                (pure (print_endline
                                    (HAppend.hAppend "clint["
                                      (HAppend.hAppend (BitVec.toFormatted addr)
                                        (HAppend.hAppend "] -> "
                                          (BitVec.toFormatted (← readReg mtime)))))))
                              else (pure ())
                              (pure (Ok
                                  (zero_extend (m := 32)
                                    (Sail.BitVec.extractLsb (← readReg mtime) 63 32)))))
                          else
                            (do
                              let _ : Unit :=
                                if ((get_config_print_clint ()) : Bool)
                                then
                                  (print_endline
                                    (HAppend.hAppend "clint["
                                      (HAppend.hAppend (BitVec.toFormatted addr) "] -> <not-mapped>")))
                                else ()
                              (pure (Err (paddr, (← (accessFaultFromAccessType access))))))))))))

/-- Type quantifiers: width : Nat, width ≥ 0, width > 0 -/
def clint_store (paddr : physaddr) (width : Nat) (data : (BitVec (8 * width))) : SailM (Result Bool (physaddr × ExceptionType)) := do
  let hart_msip_addr ← do
    (pure (MSIP_BASE + (zero_extend (m := 34) ((← readReg mhartid) <<< 2))))
  let hart_mtimecmp_addr ← do
    (pure (MTIMECMP_BASE + (zero_extend (m := 34) ((← readReg mhartid) <<< 3))))
  let hart_mtimecmp_hi_addr ← do
    (pure (MTIMECMP_BASE_HI + (zero_extend (m := 34) ((← readReg mhartid) <<< 3))))
  let .Physaddr addr := paddr
  let addr := (addr - plat_clint_base)
  if (((addr == hart_msip_addr) && ((width == 8) || (width == 4))) : Bool)
  then
    (do
      let _ : Unit :=
        if ((get_config_print_clint ()) : Bool)
        then
          (print_endline
            (HAppend.hAppend "clint["
              (HAppend.hAppend (BitVec.toFormatted addr)
                (HAppend.hAppend "] <- "
                  (HAppend.hAppend (BitVec.toFormatted data)
                    (HAppend.hAppend " (msip <- " (HAppend.hAppend (BitVec.toFormatted data) ")")))))))
        else ()
      writeReg msip (BitVec.update (← readReg msip) 0 (BitVec.access data 0))
      (pure (Ok true)))
  else
    (do
      if (((addr == hart_mtimecmp_addr) && (width == 8)) : Bool)
      then
        (do
          let _ : Unit :=
            if ((get_config_print_clint ()) : Bool)
            then
              (print_endline
                (HAppend.hAppend "clint<8>["
                  (HAppend.hAppend (BitVec.toFormatted addr)
                    (HAppend.hAppend "] <- "
                      (HAppend.hAppend (BitVec.toFormatted data) " (mtimecmp)")))))
            else ()
          writeReg mtimecmp (zero_extend (m := 64) data)
          (pure (Ok true)))
      else
        (do
          if (((addr == hart_mtimecmp_addr) && (width == 4)) : Bool)
          then
            (do
              let _ : Unit :=
                if ((get_config_print_clint ()) : Bool)
                then
                  (print_endline
                    (HAppend.hAppend "clint<4>["
                      (HAppend.hAppend (BitVec.toFormatted addr)
                        (HAppend.hAppend "] <- "
                          (HAppend.hAppend (BitVec.toFormatted data) " (mtimecmp)")))))
                else ()
              writeReg mtimecmp (Sail.BitVec.updateSubrange (← readReg mtimecmp) 31 0
                (zero_extend (m := 32) data))
              (pure (Ok true)))
          else
            (do
              if (((addr == hart_mtimecmp_hi_addr) && (width == 4)) : Bool)
              then
                (do
                  let _ : Unit :=
                    if ((get_config_print_clint ()) : Bool)
                    then
                      (print_endline
                        (HAppend.hAppend "clint<4>["
                          (HAppend.hAppend (BitVec.toFormatted addr)
                            (HAppend.hAppend "] <- "
                              (HAppend.hAppend (BitVec.toFormatted data) " (mtimecmp)")))))
                    else ()
                  writeReg mtimecmp (Sail.BitVec.updateSubrange (← readReg mtimecmp) 63 32
                    (zero_extend (m := 32) data))
                  (pure (Ok true)))
              else
                (do
                  if (((addr == MTIME_BASE) && (width == 8)) : Bool)
                  then
                    (do
                      let _ : Unit :=
                        if ((get_config_print_clint ()) : Bool)
                        then
                          (print_endline
                            (HAppend.hAppend "clint<8>["
                              (HAppend.hAppend (BitVec.toFormatted addr)
                                (HAppend.hAppend "] <- "
                                  (HAppend.hAppend (BitVec.toFormatted data) " (mtime)")))))
                        else ()
                      writeReg mtime data
                      (pure (Ok true)))
                  else
                    (do
                      if (((addr == MTIME_BASE) && (width == 4)) : Bool)
                      then
                        (do
                          let _ : Unit :=
                            if ((get_config_print_clint ()) : Bool)
                            then
                              (print_endline
                                (HAppend.hAppend "clint<4>["
                                  (HAppend.hAppend (BitVec.toFormatted addr)
                                    (HAppend.hAppend "] <- "
                                      (HAppend.hAppend (BitVec.toFormatted data) " (mtime)")))))
                            else ()
                          writeReg mtime (Sail.BitVec.updateSubrange (← readReg mtime) 31 0 data)
                          (pure (Ok true)))
                      else
                        (do
                          if (((addr == MTIME_BASE_HI) && (width == 4)) : Bool)
                          then
                            (do
                              let _ : Unit :=
                                if ((get_config_print_clint ()) : Bool)
                                then
                                  (print_endline
                                    (HAppend.hAppend "clint<4>["
                                      (HAppend.hAppend (BitVec.toFormatted addr)
                                        (HAppend.hAppend "] <- "
                                          (HAppend.hAppend (BitVec.toFormatted data) " (mtime)")))))
                                else ()
                              writeReg mtime (Sail.BitVec.updateSubrange (← readReg mtime) 63 32
                                data)
                              (pure (Ok true)))
                          else
                            (let _ : Unit :=
                              if ((get_config_print_clint ()) : Bool)
                              then
                                (print_endline
                                  (HAppend.hAppend "clint["
                                    (HAppend.hAppend (BitVec.toFormatted addr)
                                      (HAppend.hAppend "] <- "
                                        (HAppend.hAppend (BitVec.toFormatted data) " (<unmapped>)")))))
                              else ()
                            (pure (Err (paddr, (E_SAMO_Access_Fault ())))))))))))

def Mk_htif_cmd (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_htif_cmd_cmd (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _get_htif_cmd_device (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _get_htif_cmd_payload (v : (BitVec 64)) : (BitVec 48) :=
  (Sail.BitVec.extractLsb v 47 0)

def reset_htif (_ : Unit) : SailM Unit := do
  writeReg htif_cmd_write 0#1
  writeReg htif_payload_writes 0x0#4
  writeReg htif_tohost (zeros (n := 64))

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def htif_load (access : (MemoryAccessType mem_payload)) (addr : physaddr) (width : Nat) : SailM (Result (BitVec (8 * width)) (physaddr × ExceptionType)) := do
  let .Physaddr paddr := addr
  if ((get_config_print_htif ()) : Bool)
  then
    (pure (print_endline
        (HAppend.hAppend "htif["
          (HAppend.hAppend (hex_bits_str paddr)
            (HAppend.hAppend "] -> " (BitVec.toFormatted (← readReg htif_tohost)))))))
  else (pure ())
  let base ← (( do
    match (← readReg htif_tohost_base) with
    | .some base => (pure base)
    | none =>
      (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/platform.sail" 286
        "HTIF load while HTIF isn't enabled") ) : SailM physaddrbits )
  if (((width == 8) && (paddr == base)) : Bool)
  then (pure (Ok (zero_extend (m := 64) (← readReg htif_tohost))))
  else
    (do
      if (((width == 4) && (paddr == base)) : Bool)
      then
        (pure (Ok (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg htif_tohost) 31 0))))
      else
        (do
          if (((width == 4) && (paddr == (BitVec.addInt base 4))) : Bool)
          then
            (pure (Ok
                (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg htif_tohost) 63 32))))
          else (pure (Err (addr, (← (accessFaultFromAccessType access)))))))

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def htif_store (addr : physaddr) (width : Nat) (data : (BitVec (8 * width))) : SailM (Result Bool (physaddr × ExceptionType)) := SailME.run do
  let .Physaddr paddr := addr
  let _ : Unit :=
    if ((get_config_print_htif ()) : Bool)
    then
      (print_endline
        (HAppend.hAppend "htif["
          (HAppend.hAppend (hex_bits_str paddr) (HAppend.hAppend "] <- " (BitVec.toFormatted data)))))
    else ()
  let base ← (( do
    match (← readReg htif_tohost_base) with
    | .some base => (pure base)
    | none =>
      (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/platform.sail" 307
        "HTIF store while HTIF isn't enabled") ) : SailME (Result Bool (physaddr × ExceptionType))
    physaddrbits )
  if (((width == 8) && (paddr == base)) : Bool)
  then
    (do
      writeReg htif_cmd_write 1#1
      writeReg htif_payload_writes (BitVec.addInt (← readReg htif_payload_writes) 1)
      writeReg htif_tohost (zero_extend (m := 64) data))
  else
    (do
      if (((width == 4) && (paddr == base)) : Bool)
      then
        (do
          if ((data == (Sail.BitVec.extractLsb (← readReg htif_tohost) 31 0)) : Bool)
          then writeReg htif_payload_writes (BitVec.addInt (← readReg htif_payload_writes) 1)
          else writeReg htif_payload_writes 0x1#4
          writeReg htif_tohost (Sail.BitVec.updateSubrange (← readReg htif_tohost) 31 0 data))
      else
        (do
          if (((width == 4) && (paddr == (BitVec.addInt base 4))) : Bool)
          then
            (do
              if (((Sail.BitVec.extractLsb data 15 0) == (Sail.BitVec.extractLsb
                     (← readReg htif_tohost) 47 32)) : Bool)
              then writeReg htif_payload_writes (BitVec.addInt (← readReg htif_payload_writes) 1)
              else writeReg htif_payload_writes 0x1#4
              writeReg htif_cmd_write 1#1
              writeReg htif_tohost (Sail.BitVec.updateSubrange (← readReg htif_tohost) 63 32 data))
          else
            SailME.throw ((Err (addr, (E_SAMO_Access_Fault ()))) : (Result Bool (physaddr × ExceptionType)))))
  if (((((← readReg htif_cmd_write) == 1#1) && (← do
           (pure ((BitVec.toNatInt (← readReg htif_payload_writes)) >b 0)))) || (← do
         (pure ((BitVec.toNatInt (← readReg htif_payload_writes)) >b 2)))) : Bool)
  then
    (do
      let cmd ← do (pure (Mk_htif_cmd (← readReg htif_tohost)))
      match (_get_htif_cmd_device cmd) with
      | 0x00 =>
        (do
          let _ : Unit :=
            if ((get_config_print_htif ()) : Bool)
            then
              (print_endline
                (HAppend.hAppend "htif-syscall-proxy cmd: "
                  (BitVec.toFormatted (_get_htif_cmd_payload cmd))))
            else ()
          if (((BitVec.access (_get_htif_cmd_payload cmd) 0) == 1#1) : Bool)
          then
            (do
              writeReg htif_done true
              writeReg htif_exit_code ((zero_extend (m := 64) (_get_htif_cmd_payload cmd)) >>> 1))
          else (pure ()))
      | 0x01 =>
        (do
          let _ : Unit :=
            if ((get_config_print_htif ()) : Bool)
            then
              (print_endline
                (HAppend.hAppend "htif-term cmd: " (BitVec.toFormatted (_get_htif_cmd_payload cmd))))
            else ()
          match (_get_htif_cmd_cmd cmd) with
          | 0x00 => (pure ())
          | 0x01 => (plat_term_write (Sail.BitVec.extractLsb (_get_htif_cmd_payload cmd) 7 0))
          | c => (pure (print (HAppend.hAppend "Unknown term cmd: " (BitVec.toFormatted c))))
          (reset_htif ()))
      | _ => (pure (print (HAppend.hAppend "htif-???? cmd: " (BitVec.toFormatted data)))))
  else (pure ())
  (pure (Ok true))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_mmio_readable (addr : physaddr) (width : Nat) : SailM Bool := do
  if ((get_config_rvfi ()) : Bool)
  then (pure false)
  else
    (pure ((← (within_clint addr width)) || ((← (within_sig addr width)) || ((← (within_htif_readable
                addr width)) && (1 ≤b width)))))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_mmio_writable (addr : physaddr) (width : Nat) : SailM Bool := do
  if ((get_config_rvfi ()) : Bool)
  then (pure false)
  else
    (pure ((← (within_clint addr width)) || ((← (within_sig addr width)) || ((← (within_htif_writable
                addr width)) && (width ≤b 8)))))

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mmio_read (access : (MemoryAccessType mem_payload)) (paddr : physaddr) (width : Nat) : SailM (Result (BitVec (8 * width)) (physaddr × ExceptionType)) := do
  if ((← (within_clint paddr width)) : Bool)
  then (clint_load access paddr width)
  else
    (do
      if ((← (within_sig paddr width)) : Bool)
      then (sig_load access paddr width)
      else
        (do
          if ((← (within_htif_readable paddr width)) : Bool)
          then (htif_load access paddr width)
          else (pure (Err (paddr, (← (accessFaultFromAccessType access)))))))

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mmio_write (paddr : physaddr) (width : Nat) (data : (BitVec (8 * width))) : SailM (Result Bool (physaddr × ExceptionType)) := do
  if ((← (within_clint paddr width)) : Bool)
  then (clint_store paddr width data)
  else
    (do
      if ((← (within_sig paddr width)) : Bool)
      then (sig_store paddr width data)
      else
        (do
          if ((← (within_htif_writable paddr width)) : Bool)
          then (htif_store paddr width data)
          else (pure (Err (paddr, (E_SAMO_Access_Fault ()))))))

/-- Type quantifiers: k_width : Nat, k_width ≥ 0, bytes : Nat, region_width_exp : Nat, region_width_exp
  ≥ 0, region_width_exp ≤ k_width ∧ 1 ≤ bytes ∧ bytes ≤ (2 ^ region_width_exp) -/
def access_within (addr : (BitVec k_width)) (bytes : Nat) (region_width_exp : Nat) : Bool :=
  let mask : (BitVec k_width) :=
    (Complement.complement
      (zero_extend (m := (Sail.BitVec.length addr)) (ones (n := region_width_exp))))
  ((addr &&& mask) == ((BitVec.addInt addr (bytes -i 1)) &&& mask))

/-- Type quantifiers: region_width_exp : Nat, width : Nat, 0 < width ∧ width ≤ max_mem_access, 0
  ≤ region_width_exp ∧ region_width_exp ≤ 12 -/
def allowed_misaligned (addr : (BitVec 32)) (width : Nat) (region_width_exp : Nat) : Bool :=
  let region_width := (2 ^i region_width_exp)
  if ((width >b region_width) : Bool)
  then false
  else (access_within addr width region_width_exp)

/-- Type quantifiers: width : Nat, width > 0 -/
def is_aligned_paddr (typ_0 : physaddr) (width : Nat) : Bool :=
  let .Physaddr addr : physaddr := typ_0
  ((Int.tmod (BitVec.toNatInt addr) width) == 0)

/-- Type quantifiers: width : Nat, width > 0 -/
def is_aligned_vaddr (typ_0 : virtaddr) (width : Nat) : Bool :=
  let .Virtaddr addr : virtaddr := typ_0
  ((Int.tmod (BitVec.toNatInt addr) width) == 0)

def sys_misaligned_allowed_within_exp : mag_size_exp := 0

def sys_misaligned_order_decreasing : Bool := false

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, width : Nat, 13 ≤ k_n ∧ k_n ≤ 64 ∧
  0 < width ∧ width ≤ max_mem_access -/
def split_access (addr : (BitVec k_n)) (width : Nat) : SailM (Int × Int) := do
  let addr_align := (BitVec.countTrailingZeros addr)
  let width_align := (BitVec.countTrailingZeros (to_bits (l := (12 +i 1)) width))
  let bytes_per_access := (2 ^i (Min.min addr_align width_align))
  let num_accesses := (Int.tdiv width bytes_per_access)
  assert (width == (num_accesses *i bytes_per_access)) "/private/tmp/airbender-sail-integration/model/model/sys/split_access_utils.sail:53.49-53.50"
  (pure (num_accesses, bytes_per_access))

def sys_misaligned_byte_by_byte : Bool := false

/-- Type quantifiers: allowed_within_exp : Nat, width : Nat, 0 < width ∧ width ≤ max_mem_access, 0
  ≤ allowed_within_exp ∧ allowed_within_exp ≤ 12 -/
def split_misaligned (app_0 : physaddr) (width : Nat) (allowed_within_exp : Nat) (splittable : Splittability) : SailM (Int × Int) := do
  let .Physaddr addr := app_0
  let do_not_split :=
    ((splittable == CannotSplit) || ((((Int.tmod (BitVec.toNatInt addr) width) == 0) || (allowed_misaligned
          (Sail.BitVec.extractLsb addr (xlen -i 1) 0) width allowed_within_exp)) : Bool))
  if (do_not_split : Bool)
  then (pure (1, width))
  else
    (do
      if (sys_misaligned_byte_by_byte : Bool)
      then (pure (width, 1))
      else (split_access addr width))

/-- Type quantifiers: n : Int -/
def misaligned_order (n : Int) : (Int × Int × Int) :=
  if (sys_misaligned_order_decreasing : Bool)
  then ((n -i 1), 0, (Neg.neg 1))
  else (0, (n -i 1), 1)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, width : Nat, 13 ≤ k_n ∧ k_n ≤ 64 ∧
  (is_mem_width width) -/
def split_on_page_boundary (addr : (BitVec k_n)) (width : Nat) : SailM (Int × Int) := do
  let page_mask :=
    (Sail.BitVec.updateSubrange ((ones (n := (Sail.BitVec.length addr))) : (BitVec k_n))
      (pagesize_bits -i 1) 0 (zeros (n := ((12 -i 1) -i (0 -i 1)))))
  let intra_page_access :=
    ((addr &&& page_mask) == ((BitVec.subInt (BitVec.addInt addr width) 1) &&& page_mask))
  if (intra_page_access : Bool)
  then (pure (width, 0))
  else
    (do
      let nbytes_to_boundary :=
        ((2 ^i 3) -i (BitVec.toNatInt (Sail.BitVec.extractLsb addr (3 -i 1) 0)))
      assert (nbytes_to_boundary <b width) "/private/tmp/airbender-sail-integration/model/model/sys/split_access_utils.sail:111.37-111.38"
      (pure (nbytes_to_boundary, (width -i nbytes_to_boundary))))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def pma_allows_atomic_op (pma : AtomicSupport) (op : amoop) (width : Nat) : Bool :=
  match pma with
  | .AMONone => false
  | .AMOSwap => (op == AMOSWAP)
  | .AMOLogical => ((op == AMOSWAP) || ((op == AMOAND) || ((op == AMOOR) || (op == AMOXOR))))
  | .AMOArithmetic => (bne op AMOCAS)
  | .AMOCASW => ((bne op AMOCAS) || (width ≤b 4))
  | .AMOCASD => ((bne op AMOCAS) || (width ≤b 8))
  | .AMOCASQ => ((bne op AMOCAS) || (width ≤b 16))

def override_PMA (pma : PMA) (pbmt : page_based_mem_type) : PMA :=
  match pbmt with
  | .PBMT_PMA => pma
  | .PBMT_NC =>
    { pma with mem_type := MainMemory, cacheable := false, read_idempotent := true, write_idempotent := true }
  | .PBMT_IO =>
    { pma with mem_type := IOMemory, cacheable := false, read_idempotent := false, write_idempotent := false }

def pma_misaligned_exception (pma : PMA) (access : (MemoryAccessType mem_payload)) : SailM (Option misaligned_exception) := do
  let exceptions := pma.misaligned_exceptions
  match access with
  | .Load .Data => (pure exceptions.load_store)
  | .LoadExecute .Data => (pure exceptions.load_store)
  | .Store .Data => (pure exceptions.load_store)
  | .Load .Vector => (pure exceptions.vector)
  | .Store .Vector => (pure exceptions.vector)
  | .Atomic _ => (pure (some exceptions.amo))
  | .LoadReserved (_, _, .Data) => (pure (some exceptions.lrsc))
  | .StoreConditional (_, _, .Data) => (pure (some exceptions.lrsc))
  | .InstructionFetch () =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/pma.sail" 158
      "PMA: Invalid misaligned instruction fetch.")
  | .Load .PageTableEntry =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/pma.sail" 159
      "PMA: Invalid misaligned load of page-table entry.")
  | .Store .PageTableEntry =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/pma.sail" 160
      "PMA: Invalid misaligned store of page-table entry.")
  | .LoadReserved (_, _, p) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/pma.sail" 161
      (HAppend.hAppend "PMA: Invalid misaligned load-reserved ("
        (HAppend.hAppend (mem_payload_name_forwards p) ").")))
  | .StoreConditional (_, _, p) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/pma.sail" 162
      (HAppend.hAppend "PMA: Invalid misaligned store-conditional ("
        (HAppend.hAppend (mem_payload_name_forwards p) ").")))
  | .Load .ShadowStack =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/pma.sail" 163
      "PMA: Invalid misaligned shadow-stack load.")
  | .Store .ShadowStack =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/pma.sail" 164
      "PMA: Invalid misaligned shadow-stack store.")
  | .CacheAccess _ =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/pma.sail" 165
      "PMA: Invalid misaligned cache-access.")
  | .LoadExecute p =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/pma.sail" 166
      (HAppend.hAppend "PMA: Invalid misaligned load-execute ("
        (HAppend.hAppend (mem_payload_name_forwards p) ").")))

/-- Type quantifiers: width : Nat, 0 ≤ width -/
def is_mag_applicable_access (access : (MemoryAccessType mem_payload)) (width : Nat) : SailM Bool := do
  match access with
  | .Load .Data => (pure (width ≤b xlen_bytes))
  | .Store .Data => (pure (width ≤b xlen_bytes))
  | .LoadExecute .Data => (pure (width ≤b xlen_bytes))
  | .Load .Vector => (pure true)
  | .Store .Vector => (pure true)
  | .Load .PageTableEntry => (pure false)
  | .Store .PageTableEntry => (pure false)
  | .Load .ShadowStack => (pure false)
  | .Store .ShadowStack => (pure false)
  | .Atomic (_, _, _, .Data, .Data) => (pure true)
  | .Atomic (_, _, _, .ShadowStack, .ShadowStack) => (pure false)
  | .InstructionFetch () => (pure false)
  | .LoadReserved (_, _, .Data) => (pure false)
  | .StoreConditional (_, _, .Data) => (pure false)
  | .CacheAccess _ => (pure false)
  | .Atomic (_, _, _, rp, wp) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/pma.sail" 199
      (HAppend.hAppend "Invalid payloads ("
        (HAppend.hAppend (mem_payload_name_forwards rp)
          (HAppend.hAppend ", " (HAppend.hAppend (mem_payload_name_forwards wp) ") for Atomic.")))))
  | .LoadReserved (_, _, p) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/pma.sail" 200
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadReserved.")))
  | .StoreConditional (_, _, p) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/pma.sail" 201
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for StoreConditional.")))
  | .LoadExecute p =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/pma.sail" 202
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadExecute.")))

/-- Type quantifiers: k_ex436317_ : Bool -/
def mag_of_pma (pma : PMA) (is_vector : Bool) : (Option Nat) :=
  let mag :=
    if (is_vector : Bool)
    then pma.vector_misaligned_atomicity_granule_size_exp
    else pma.misaligned_atomicity_granule_size_exp
  if ((mag == 0) : Bool)
  then none
  else (some mag)

/-- Type quantifiers: k_ex436318_ : Bool, width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_pma_mag (pma : PMA) (typ_1 : physaddr) (width : Nat) (is_vector : Bool) : Bool :=
  let .Physaddr addr : physaddr := typ_1
  match (mag_of_pma pma is_vector) with
  | none => false
  | .some mag => (allowed_misaligned (Sail.BitVec.extractLsb addr (xlen -i 1) 0) width mag)

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def mag_pma_check (pma : PMA) (access : (MemoryAccessType mem_payload)) (paddr : physaddr) (width : Nat) : SailM (Result (Splittability × Nat) misaligned_exception) := do
  let is_mag_applicable ← do (is_mag_applicable_access access width)
  if (((is_aligned_paddr paddr width) || (is_mag_applicable && (within_pma_mag pma paddr width
           (is_vector_access access)))) : Bool)
  then (pure (Ok (CannotSplit, 0)))
  else
    (do
      match (← (pma_misaligned_exception pma access)) with
      | .some e => (pure (Err e))
      | none =>
        (match (is_mag_applicable, (mag_of_pma pma (is_vector_access access))) with
        | (true, .some mag) => (pure (Ok (CanSplit, mag)))
        | (_, _) => (pure (Ok (CanSplit, sys_misaligned_allowed_within_exp)))))

def matching_pma_region_bits_range (regions : (List PMA_Region)) (base : (BitVec 64)) (size : (BitVec 64)) : (Option PMA_Region) :=
  match regions with
  | [] => none
  | (region :: rest) =>
    (if ((range_subset base size region.base region.size) : Bool)
    then (some region)
    else (matching_pma_region_bits_range rest base size))

/-- Type quantifiers: width : Nat, 1 ≤ width ∧ width ≤ 4096 -/
def matching_pma_region (regions : (List PMA_Region)) (addr : physaddr) (width : Nat) : (Option PMA_Region) :=
  (matching_pma_region_bits_range regions (zero_extend (m := 64) (bits_of_physaddr addr))
    (to_bits (l := 64) width))

/-- Type quantifiers: k_ex436322_ : Bool, k_ex436321_ : Bool, k_ex436320_ : Bool -/
def read_kind_of_flags (aq : Bool) (rl : Bool) (res : Bool) : SailM read_kind := do
  match (aq, rl, res) with
  | (false, false, false) => (pure Read_plain)
  | (true, false, false) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail" 38
      "Unreserved load with acquire semantics should be unreachable")
  | (true, true, false) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail" 39
      "Unreserved load with acquire-release semantics should be unreachable")
  | (false, false, true) => (pure Read_RISCV_reserved)
  | (true, false, true) => (pure Read_RISCV_reserved_acquire)
  | (true, true, true) => (pure Read_RISCV_reserved_strong_acquire)
  | (false, true, false) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail" 44
      "Unreserved Load with release semantics should be unreachable")
  | (false, true, true) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail" 45
      "Load-reserved with release semantics should be unreachable")

/-- Type quantifiers: k_ex436325_ : Bool, k_ex436324_ : Bool, k_ex436323_ : Bool -/
def write_kind_of_flags (aq : Bool) (rl : Bool) (con : Bool) : SailM write_kind := do
  match (aq, rl, con) with
  | (false, false, false) => (pure Write_plain)
  | (false, true, false) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail" 51
      "Unconditional store with release semantics should be unreachable")
  | (false, false, true) => (pure Write_RISCV_conditional)
  | (false, true, true) => (pure Write_RISCV_conditional_release)
  | (true, true, false) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail" 54
      "Unconditional store with acquire-release semantics should be unreachable")
  | (true, true, true) => (pure Write_RISCV_conditional_strong_release)
  | (true, false, false) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail" 57
      "Unconditional store with acquire semantics should be unreachable")
  | (true, false, true) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail" 58
      "Store-conditional with acquire semantics should be unreachable")

/-- Type quantifiers: k_ex436326_ : Bool, width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def pmaCheck (paddr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (res_or_con : Bool) : SailM (Result Phys_Mem_Access_Info ExceptionType) := SailME.run do
  let attributes ← (( do
    match (matching_pma_region (← readReg pma_regions) paddr width) with
    | none =>
      SailME.throw (← do
          (pure (Err (← (accessFaultFromAccessType access)))))
    | .some { attributes := attributes, size := _, include_in_device_tree := _, base := _ } =>
      (pure (override_PMA attributes pbmt)) ) : SailME (Result Phys_Mem_Access_Info ExceptionType)
    PMA )
  let canAccess ← (( do
    match access with
    | .InstructionFetch () => (pure attributes.executable)
    | .Load .Data =>
      (do
        assert (not res_or_con) "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail:99.53-99.54"
        (pure attributes.readable))
    | .Load .Vector =>
      (do
        assert (not res_or_con) "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail:100.53-100.54"
        (pure attributes.readable))
    | .Load .PageTableEntry =>
      (do
        assert (not res_or_con) "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail:101.53-101.54"
        (pure attributes.supports_pte_read))
    | .LoadExecute .Data =>
      (do
        assert (not res_or_con) "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail:106.53-106.54"
        (pure (attributes.executable && attributes.readable)))
    | .Store .Data =>
      (do
        assert (not res_or_con) "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail:107.53-107.54"
        (pure attributes.writable))
    | .Store .Vector =>
      (do
        assert (not res_or_con) "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail:108.53-108.54"
        (pure attributes.writable))
    | .Store .PageTableEntry =>
      (do
        assert (not res_or_con) "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail:109.53-109.54"
        (pure attributes.supports_pte_write))
    | .LoadReserved (_, _, .Data) =>
      (do
        assert res_or_con "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail:113.55-113.56"
        (pure (attributes.readable && (bne attributes.reservability RsrvNone))))
    | .StoreConditional (_, _, .Data) =>
      (do
        assert res_or_con "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail:114.55-114.56"
        (pure (attributes.writable && (bne attributes.reservability RsrvNone))))
    | .Atomic (op, _, _, .Data, .Data) =>
      (do
        assert res_or_con "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail:115.55-115.56"
        (pure (attributes.readable && (attributes.writable && (pma_allows_atomic_op
                attributes.atomic_support op width)))))
    | .Load .ShadowStack =>
      (do
        assert (not res_or_con) "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail:119.53-119.54"
        (pure (attributes.readable && attributes.read_idempotent)))
    | .Store .ShadowStack =>
      (do
        assert (not res_or_con) "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail:120.53-120.54"
        (pure (attributes.writable && attributes.write_idempotent)))
    | .Atomic (.AMOSWAP, _, _, .ShadowStack, .ShadowStack) =>
      (do
        assert res_or_con "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail:121.73-121.74"
        (pure (attributes.readable && (attributes.writable && (attributes.read_idempotent && (attributes.write_idempotent && (pma_allows_atomic_op
                    attributes.atomic_support AMOSWAP width)))))))
    | .CacheAccess (.CB_zero ()) => (pure (attributes.writable && attributes.supports_cbo_zero))
    | .CacheAccess (.CB_manage _) => (pure (attributes.readable || attributes.writable))
    | .CacheAccess (.CB_prefetch p) =>
      (match p with
      | .PREFETCH_R => (pure attributes.readable)
      | .PREFETCH_W => (pure attributes.writable)
      | .PREFETCH_I => (pure attributes.executable))
    | .LoadExecute p =>
      (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail" 158
        (HAppend.hAppend "Invalid payload ("
          (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadExecute.")))
    | .LoadReserved (_, _, p) =>
      (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail" 159
        (HAppend.hAppend "Invalid payload ("
          (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadReserved.")))
    | .StoreConditional (_, _, p) =>
      (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail" 160
        (HAppend.hAppend "Invalid payload ("
          (HAppend.hAppend (mem_payload_name_forwards p) ") for StoreConditional.")))
    | .Atomic (op, _, _, .ShadowStack, .ShadowStack) =>
      (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail" 162
        (HAppend.hAppend "Invalid op ("
          (HAppend.hAppend (amo_mnemonic_forwards op) ") for ShadowStack Atomic.")))
    | .Atomic (_, _, _, rp, wp) =>
      (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/mem.sail" 163
        (HAppend.hAppend "Invalid payloads ("
          (HAppend.hAppend (mem_payload_name_forwards rp)
            (HAppend.hAppend ", " (HAppend.hAppend (mem_payload_name_forwards wp) ") for Atomic.")))))
    ) : SailME (Result Phys_Mem_Access_Info ExceptionType) Bool )
  if ((not canAccess) : Bool)
  then
    (do
      let _ : Unit :=
        if ((get_config_print_pma ()) : Bool)
        then
          (print_endline
            (HAppend.hAppend "PMA access check failed for a "
              (HAppend.hAppend (Int.repr width)
                (HAppend.hAppend "-byte wide "
                  (HAppend.hAppend (accessType_to_str access)
                    (HAppend.hAppend " access to address "
                      (HAppend.hAppend (hex_bits_str (bits_of_physaddr paddr))
                        (HAppend.hAppend " with PMA {"
                          (HAppend.hAppend (pma_attributes_to_str attributes) "}")))))))))
        else ()
      (pure (Err (← (accessFaultFromAccessType access)))))
  else
    (do
      match (← (mag_pma_check attributes access paddr width)) with
      | .Ok (splittable, granule_size_exp) =>
        (pure (Ok
            { splittable := splittable
              granule_size_exp := granule_size_exp }))
      | .Err e =>
        (do
          let _ : Unit :=
            if ((get_config_print_pma ()) : Bool)
            then
              (print_endline
                (HAppend.hAppend "MAG PMA check failed for a "
                  (HAppend.hAppend (Int.repr width)
                    (HAppend.hAppend "-byte wide "
                      (HAppend.hAppend (accessType_to_str access)
                        (HAppend.hAppend " access to address "
                          (HAppend.hAppend (hex_bits_str (bits_of_physaddr paddr))
                            (HAppend.hAppend " with PMA {"
                              (HAppend.hAppend (pma_attributes_to_str attributes) "}")))))))))
            else ()
          match e with
          | .AccessFault => (pure (Err (← (accessFaultFromAccessType access))))
          | .AlignmentException => (pure (Err (← (alignmentFaultFromAccessType access))))))

/-- Type quantifiers: k_ex436327_ : Bool, width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def phys_access_check (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (paddr : physaddr) (width : Nat) (res_or_con : Bool) : SailM (Result Phys_Mem_Access_Info ExceptionType) := do
  match (← (pmpCheck paddr width access priv)) with
  | .some e => (pure (Err e))
  | none => (pmaCheck paddr width access pbmt res_or_con)

/-- Type quantifiers: k_ex436328_ : Bool, width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def check_pma_with_pmp_priority (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (paddr : physaddr) (width : Nat) (res_or_con : Bool) : SailM (Result Phys_Mem_Access_Info ExceptionType) := do
  match (← (pmaCheck paddr width access pbmt res_or_con)) with
  | .Ok access_info => (pure (Ok access_info))
  | .Err pmaExc =>
    (do
      match (← (pmpCheck paddr width access priv)) with
      | .some pmpExc => (pure (Err pmpExc))
      | none => (pure (Err pmaExc)))

/-- Type quantifiers: k_ex436332_ : Bool, k_ex436331_ : Bool, k_ex436330_ : Bool, k_ex436329_ : Bool, width
  : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def checked_mem_read (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta' : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType)) := SailME.run do
  let access_info ← (( do
    match (← (check_pma_with_pmp_priority access pbmt priv paddr width res)) with
    | .Ok access_info => (pure access_info)
    | .Err e =>
      SailME.throw ((Err (paddr, e)) : (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType)))
    ) : SailME (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType))
    Phys_Mem_Access_Info )
  let (N, split_width) ← do
    (split_misaligned paddr width access_info.granule_size_exp access_info.splittable)
  let paddr_bits := (bits_of_physaddr paddr)
  let data := (zeros (n := ((8 *i N) *i split_width)))
  let (first, last, step) := (misaligned_order N)
  let i : Nat := first
  let finished : Bool := false
  let rk ← do (read_kind_of_flags aq rl res)
  let (data, finished, i) ← (( do
    let loop_vars ← untilFuelM (fuel :=N) (fun (data, finished, i) => (pure finished)) (data, finished, i)
      fun (data, finished, i) => do
        assert true "loop dummy assert"
        let offset := i
        let paddr := (Physaddr (BitVec.addInt paddr_bits (offset *i split_width)))
        match (← (pmpCheck paddr split_width access priv)) with
        | .some e =>
          SailME.throw ((Err (paddr, e)) : (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType)))
        | none => (pure ())
        let split_data ← do
          if ((← (within_mmio_readable paddr split_width)) : Bool)
          then
            (do
              match (← (mmio_read access paddr split_width)) with
              | .Err e =>
                SailME.throw ((Err e) : (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType)))
              | .Ok mmio_data => (pure mmio_data))
          else
            (do
              let (ram_data, _meta) ← do (read_ram rk access paddr split_width meta')
              (pure ram_data))
        let data : (BitVec (8 * N * split_width)) :=
          (Sail.BitVec.updateSubrange data (((8 *i (offset +i 1)) *i split_width) -i 1)
            ((8 *i offset) *i split_width) split_data)
        let (finished, i) : (Bool × Nat) :=
          if ((offset == last) : Bool)
          then
            (let finished : Bool := true
            (finished, i))
          else
            (let i : Nat := (offset +i step)
            (finished, i))
        (pure (data, finished, i))
    (pure loop_vars) ) : SailME (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType))
    ((BitVec (8 * N * split_width)) × Bool × Nat) )
  (pure (Ok (data, default_meta)))

/-- Type quantifiers: k_ex436336_ : Bool, k_ex436335_ : Bool, k_ex436334_ : Bool, k_ex436333_ : Bool, width
  : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_read_priv_meta (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta' : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType)) := do
  let result ← (( do
    match (aq, rl, res) with
    | (false, true, false) => sailThrow ((Error_not_implemented "load.rl"))
    | (false, true, true) => sailThrow ((Error_not_implemented "lr.rl"))
    | (_, _, _) => (checked_mem_read access pbmt priv paddr width aq rl res meta') ) : SailM
    (MemoryOpResult ((BitVec (8 * width)) × mem_meta)) )
  let _ : Unit :=
    match result with
    | .Ok (value, _) =>
      (mem_read_callback (accessType_to_str access) (bits_of_physaddr paddr) width value)
    | .Err (addr, e) =>
      (mem_exception_callback (bits_of_physaddr addr) (exceptionType_bits_forwards e))
  (pure result)

/-- Type quantifiers: k_ex436343_ : Bool, k_ex436342_ : Bool, k_ex436341_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_read (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (eff_priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) (physaddr × ExceptionType)) := do
  (pure (MemoryOpResult_drop_meta
      (← (mem_read_priv_meta access pbmt eff_priv paddr width aq rl res false))))

/-- Type quantifiers: k_ex436346_ : Bool, k_ex436345_ : Bool, k_ex436344_ : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_write_ea (paddr : physaddr) (width : Nat) (priv : Privilege) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Unit (physaddr × ExceptionType)) := SailME.run do
  let access_info ← (( do
    match (← (check_pma_with_pmp_priority access pbmt priv paddr width con)) with
    | .Ok access_info => (pure access_info)
    | .Err e => SailME.throw ((Err (paddr, e)) : (Result Unit (physaddr × ExceptionType))) ) :
    SailME (Result Unit (physaddr × ExceptionType)) Phys_Mem_Access_Info )
  let (N, split_width) ← do
    (split_misaligned paddr width access_info.granule_size_exp access_info.splittable)
  let paddr_bits := (bits_of_physaddr paddr)
  let (first, last, step) := (misaligned_order N)
  let i : Nat := first
  let finished : Bool := false
  let wk ← do (write_kind_of_flags aq rl con)
  let (finished, i) ← (( do
    let loop_vars ← untilFuelM (fuel :=N) (fun (finished, i) => (pure finished)) (finished, i)
      fun (finished, i) => do
        assert true "loop dummy assert"
        let offset := i
        let paddr := (Physaddr (BitVec.addInt paddr_bits (offset *i split_width)))
        match (← (pmpCheck paddr split_width access priv)) with
        | .some e => SailME.throw ((Err (paddr, e)) : (Result Unit (physaddr × ExceptionType)))
        | none =>
          (do
            if ((not (← (within_mmio_writable paddr split_width))) : Bool)
            then (write_ram_ea wk access paddr split_width)
            else (pure ()))
        let (finished, i) : (Bool × Nat) :=
          if ((offset == last) : Bool)
          then
            (let finished : Bool := true
            (finished, i))
          else
            (let i : Nat := (offset +i step)
            (finished, i))
        (pure (finished, i))
    (pure loop_vars) ) : SailME (Result Unit (physaddr × ExceptionType)) (Bool × Nat) )
  (pure (Ok ()))

/-- Type quantifiers: k_ex436349_ : Bool, k_ex436348_ : Bool, k_ex436347_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def checked_mem_write (paddr : physaddr) (width : Nat) (data : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (meta' : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool (physaddr × ExceptionType)) := SailME.run do
  let access_info ← (( do
    match (← (check_pma_with_pmp_priority access pbmt priv paddr width con)) with
    | .Ok access_info => (pure access_info)
    | .Err e => SailME.throw ((Err (paddr, e)) : (Result Bool (physaddr × ExceptionType))) ) :
    SailME (Result Bool (physaddr × ExceptionType)) Phys_Mem_Access_Info )
  let (N, split_width) ← do
    (split_misaligned paddr width access_info.granule_size_exp access_info.splittable)
  let paddr_bits := (bits_of_physaddr paddr)
  let write_success : Bool := true
  let (first, last, step) := (misaligned_order N)
  let i : Nat := first
  let finished : Bool := false
  let wk ← do (write_kind_of_flags aq rl con)
  let (finished, i, write_success) ← (( do
    let loop_vars ← untilFuelM (fuel :=N) (fun (finished, i, write_success) => (pure finished)) (finished, i, write_success)
      fun (finished, i, write_success) => do
        assert true "loop dummy assert"
        let offset := i
        let paddr := (Physaddr (BitVec.addInt paddr_bits (offset *i split_width)))
        match (← (pmpCheck paddr split_width access priv)) with
        | .some e => SailME.throw ((Err (paddr, e)) : (Result Bool (physaddr × ExceptionType)))
        | none => (pure ())
        let write_value :=
          (Sail.BitVec.extractLsb data (((8 *i (offset +i 1)) *i split_width) -i 1)
            ((8 *i offset) *i split_width))
        let write_success ← (( do
          if ((← (within_mmio_writable paddr split_width)) : Bool)
          then
            (do
              match (← (mmio_write paddr split_width write_value)) with
              | .Ok v => (pure (write_success && v))
              | .Err e => SailME.throw ((Err e) : (Result Bool (physaddr × ExceptionType))))
          else
            (do
              let v ← do (write_ram wk access paddr split_width write_value meta')
              (pure (write_success && v))) ) : SailME (Result Bool (physaddr × ExceptionType)) Bool
          )
        let (finished, i) : (Bool × Nat) :=
          if ((offset == last) : Bool)
          then
            (let finished : Bool := true
            (finished, i))
          else
            (let i : Nat := (offset +i step)
            (finished, i))
        (pure (finished, i, write_success))
    (pure loop_vars) ) : SailME (Result Bool (physaddr × ExceptionType)) (Bool × Nat × Bool) )
  (pure (Ok write_success))

/-- Type quantifiers: k_ex436352_ : Bool, k_ex436351_ : Bool, k_ex436350_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_write_value_priv_meta (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (meta' : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool (physaddr × ExceptionType)) := do
  let result ← do (checked_mem_write paddr width value access pbmt priv meta' aq rl con)
  let _ : Unit :=
    match result with
    | .Ok _ => (mem_write_callback (accessType_to_str access) (bits_of_physaddr paddr) width value)
    | .Err (addr, e) =>
      (mem_exception_callback (bits_of_physaddr addr) (exceptionType_bits_forwards e))
  (pure result)

/-- Type quantifiers: k_ex436355_ : Bool, k_ex436354_ : Bool, k_ex436353_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_write_value (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (priv : Privilege) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool (physaddr × ExceptionType)) := do
  (mem_write_value_priv_meta paddr width value access pbmt priv default_meta aq rl con)

def Mk_PTE_Ext (v : (BitVec 10)) : (BitVec 10) :=
  v

def _get_PTE_Ext_PBMT (v : (BitVec 10)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 8 7)

def _get_PTE_Ext_RSW_60t59b (v : (BitVec 10)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 6 5)

def _update_PTE_Ext_RSW_60t59b (v : (BitVec 10)) (x : (BitVec 2)) : (BitVec 10) :=
  (Sail.BitVec.updateSubrange v 6 5 x)

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

/-- Type quantifiers: k_ex436362_ : Bool, k_ex436361_ : Bool -/
def check_PTE_permission (access : (MemoryAccessType mem_payload)) (priv : Privilege) (stage : TranslationStage) (mxr : Bool) (do_sum : Bool) (pte_flags : (BitVec 8)) (_ext : (BitVec 10)) (_ext_ptw : Unit) : SailM PTE_Check := SailME.run do
  let pte_U := (bit_to_bool (_get_PTE_Flags_U pte_flags))
  let pte_R := (bit_to_bool (_get_PTE_Flags_R pte_flags))
  let pte_W := (bit_to_bool (_get_PTE_Flags_W pte_flags))
  let pte_X := (bit_to_bool (_get_PTE_Flags_X pte_flags))
  assert (zopz0zJzJzK pte_W (pte_R || (not pte_X))) "/private/tmp/airbender-sail-integration/model/model/sys/vmem_pte.sail:160.39-160.40"
  let priv_ok ← (( do
    match priv with
    | .User => (pure pte_U)
    | .Supervisor => (pure ((not pte_U) || (do_sum && (is_load_store access))))
    | .Machine =>
      (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/vmem_pte.sail" 168
        "m-mode mem perm check")
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
                assert (bool_bit_backwards (_get_MEnvcfg_SSE (← readReg menvcfg))) "/private/tmp/airbender-sail-integration/model/model/sys/vmem_pte.sail:186.33-186.34"
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
                    (internal_error
                      "/private/tmp/airbender-sail-integration/model/model/sys/vmem_pte.sail" 216
                      (HAppend.hAppend "Invalid payload ("
                        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadExecute.")))
                  | .LoadReserved (_, _, p) =>
                    (internal_error
                      "/private/tmp/airbender-sail-integration/model/model/sys/vmem_pte.sail" 217
                      (HAppend.hAppend "Invalid payload ("
                        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadReserved.")))
                  | .StoreConditional (_, _, p) =>
                    (internal_error
                      "/private/tmp/airbender-sail-integration/model/model/sys/vmem_pte.sail" 218
                      (HAppend.hAppend "Invalid payload ("
                        (HAppend.hAppend (mem_payload_name_forwards p) ") for StoreConditional.")))
                  | .Atomic (_, _, _, rp, wp) =>
                    (internal_error
                      "/private/tmp/airbender-sail-integration/model/model/sys/vmem_pte.sail" 219
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

def ext_get_ptw_error (failure : pte_check_failure) : PTW_Error :=
  match failure with
  | .PTE_No_Permission () => (PTW_No_Permission ())
  | .PTE_No_Access () => (PTW_No_Access ())
  | .PTE_Ext_Failure _ => (PTW_No_Permission ())

def convertToGuestException (e : ExceptionType) : ExceptionType :=
  match e with
  | .E_Fetch_Page_Fault () => (E_Fetch_GPage_Fault ())
  | .E_Load_Page_Fault () => (E_Load_GPage_Fault ())
  | .E_SAMO_Page_Fault () => (E_SAMO_GPage_Fault ())
  | _ => e

def g_stage_tval2_exception_value (trap : ExceptionType) (gpa : (BitVec (if ( 32 = 32  : Bool) then 34 else 64))) : (BitVec 32) :=
  if (((is_guest_page_fault trap) && sys_guest_page_fault_writes_htval) : Bool)
  then (Sail.BitVec.truncate (gpa >>> 2) xlen)
  else (zeros (n := 32))

def translationException (access : (MemoryAccessType mem_payload)) (err : PTW_Error) : SailM ExceptionType := do
  match (access, err) with
  | (_, .PTW_Ext_Error e) => (pure (E_Extension (ext_translate_exception e)))
  | (.Atomic (_, _, _, .Data, .Data), .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.Atomic (_, _, _, .Data, .Data), _) => (pure (E_SAMO_Page_Fault ()))
  | (.Load .Data, .PTW_No_Access ()) => (pure (E_Load_Access_Fault ()))
  | (.Load .Data, _) => (pure (E_Load_Page_Fault ()))
  | (.Load .Vector, .PTW_No_Access ()) => (pure (E_Load_Access_Fault ()))
  | (.Load .Vector, _) => (pure (E_Load_Page_Fault ()))
  | (.Load .PageTableEntry, .PTW_No_Access ()) => (pure (E_Load_Access_Fault ()))
  | (.Load .PageTableEntry, _) => (pure (E_Load_Page_Fault ()))
  | (.LoadExecute .Data, .PTW_No_Access ()) => (pure (E_Load_Access_Fault ()))
  | (.LoadExecute .Data, _) => (pure (E_Load_Page_Fault ()))
  | (.LoadReserved (_, _, .Data), .PTW_No_Access ()) => (pure (E_Load_Access_Fault ()))
  | (.LoadReserved (_, _, .Data), _) => (pure (E_Load_Page_Fault ()))
  | (.Store .Data, .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.Store .Data, _) => (pure (E_SAMO_Page_Fault ()))
  | (.Store .Vector, .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.Store .Vector, _) => (pure (E_SAMO_Page_Fault ()))
  | (.Store .PageTableEntry, .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.Store .PageTableEntry, _) => (pure (E_SAMO_Page_Fault ()))
  | (.StoreConditional (_, _, .Data), .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.StoreConditional (_, _, .Data), _) => (pure (E_SAMO_Page_Fault ()))
  | (.Atomic (_, _, _, .ShadowStack, .ShadowStack), .PTW_No_Access ()) =>
    (pure (E_SAMO_Access_Fault ()))
  | (.Atomic (_, _, _, .ShadowStack, .ShadowStack), _) => (pure (E_SAMO_Page_Fault ()))
  | (.Load .ShadowStack, .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.Load .ShadowStack, _) => (pure (E_SAMO_Page_Fault ()))
  | (.Store .ShadowStack, .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.Store .ShadowStack, _) => (pure (E_SAMO_Page_Fault ()))
  | (.InstructionFetch (), .PTW_No_Access ()) => (pure (E_Fetch_Access_Fault ()))
  | (.InstructionFetch (), _) => (pure (E_Fetch_Page_Fault ()))
  | (.CacheAccess (.CB_manage _), .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.CacheAccess (.CB_manage _), _) => (pure (E_SAMO_Page_Fault ()))
  | (.CacheAccess (.CB_zero ()), .PTW_No_Access ()) => (pure (E_SAMO_Access_Fault ()))
  | (.CacheAccess (.CB_zero ()), _) => (pure (E_SAMO_Page_Fault ()))
  | (.CacheAccess (.CB_prefetch p), .PTW_No_Access ()) =>
    (match p with
    | .PREFETCH_R => (pure (E_Load_Access_Fault ()))
    | .PREFETCH_W => (pure (E_SAMO_Access_Fault ()))
    | .PREFETCH_I => (pure (E_Fetch_Access_Fault ())))
  | (.CacheAccess (.CB_prefetch p), _) =>
    (match p with
    | .PREFETCH_R => (pure (E_Load_Page_Fault ()))
    | .PREFETCH_W => (pure (E_SAMO_Page_Fault ()))
    | .PREFETCH_I => (pure (E_Fetch_Page_Fault ())))
  | (.LoadExecute p, _) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/vmem_ptw.sail" 137
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadExecute.")))
  | (.LoadReserved (_, _, p), _) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/vmem_ptw.sail" 138
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadReserved.")))
  | (.StoreConditional (_, _, p), _) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/vmem_ptw.sail" 139
      (HAppend.hAppend "Invalid payload ("
        (HAppend.hAppend (mem_payload_name_forwards p) ") for StoreConditional.")))
  | (.Atomic (_, _, _, rp, wp), _) =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/vmem_ptw.sail" 140
      (HAppend.hAppend "Invalid payloads ("
        (HAppend.hAppend (mem_payload_name_forwards rp)
          (HAppend.hAppend ", " (HAppend.hAppend (mem_payload_name_forwards wp) ") for Atomic.")))))

/-- Type quantifiers: x_1 : Nat, 0 ≤ x_1 ∧ x_1 ≤ 4 -/
def ptw_start_callback (x_0 : TranslationStage) (x_1 : Nat) (x_2 : (BitVec 64)) (x_3 : (MemoryAccessType mem_payload)) (x_4 : Privilege) : Unit :=
  ()

/-- Type quantifiers: x_1 : Nat, 0 ≤ x_1 ∧ x_1 ≤ 4 -/
def ptw_step_callback (x_0 : TranslationStage) (x_1 : Nat) (x_2 : (BitVec (if ( 32 = 32  : Bool) then 34 else 64))) (x_3 : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: x_1 : Nat, 0 ≤ x_1 ∧ x_1 ≤ 4 -/
def ptw_success_callback (x_0 : TranslationStage) (x_1 : Nat) (x_2 : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: x_1 : Nat, 0 ≤ x_1 ∧ x_1 ≤ 4 -/
def ptw_fail_callback (x_0 : TranslationStage) (x_1 : Nat) (x_2 : PTW_Error) (x_3 : (BitVec (if ( 32
  = 32  : Bool) then 34 else 64))) : Unit :=
  ()

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

/-- Type quantifiers: _sv_mode : Nat, (is_sv_or_svx4_mode _sv_mode) -/
def tlb_hash (_sv_mode : Nat) (vpn : (BitVec (_sv_mode - 12))) (stage : TranslationStage) : Nat :=
  let stage_bits : (BitVec num_tlb_entries_exp) :=
    match stage with
    | .S_Stage => (zero_extend (m := 6) 0b00#2)
    | .VS_Stage => (zero_extend (m := 6) 0b01#2)
    | .G_Stage => (zero_extend (m := 6) 0b10#2)
  (BitVec.toNatInt ((Sail.BitVec.extractLsb vpn (num_tlb_entries_exp -i 1) 0) ^^^ stage_bits))

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

/-- Type quantifiers: k_ex436393_ : Bool, level : Nat, sv_width : Nat, (is_sv_or_svx4_mode sv_width), 0
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
        assert (xlen ≥b 64) "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail:377.31-377.32"
        throw Error.Exit)
    | .RV32 =>
      (pure (0b000#3 +++ (_get_Hgatp32_Mode
            (Mk_Hgatp32 (Sail.BitVec.extractLsb (← readReg hgatp) 31 0)))))
    | .RV128 =>
      (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail" 379
        "RV128 not supported") ) : SailM SailRV32.hgatp_mode )
  match (← (hgatpMode_of_bits arch mbits)) with
  | .some m => (pure m)
  | none =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail" 384
      "invalid translation mode in hgatp")

def hgatp_mode_width_forwards (arg_ : HGATPMode) : SailM Int := do
  match arg_ with
  | .Sv32x4 => (pure 34)
  | .Sv39x4 => (pure 41)
  | .Sv48x4 => (pure 50)
  | .Sv57x4 => (pure 59)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
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

/-- Type quantifiers: k_ex273606_ : Bool, k_ex273607_ : Bool, tlb_index : Nat, sv_width : Nat, (is_sv_or_svx4_mode
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

/-- Type quantifiers: k_ex273596_ : Bool, k_ex273597_ : Bool, level : Nat, k_ex273599_ : Bool, sv_width
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
  assert ((sv_width == 32) || ((sv_width == 34) || false)) "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail:176.41-176.42"
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

/-- Type quantifiers: k_ex273596_ : Bool, k_ex273597_ : Bool, level : Nat, sv_width : Nat, (is_sv_or_svx4_mode
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
  assert ((sv_width == 32) || ((sv_width == 34) || false)) "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail:176.41-176.42"
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

/-- Type quantifiers: k_ex273614_ : Bool, k_ex273615_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
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

/-- Type quantifiers: k_ex273625_ : Bool, k_ex273626_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width) -/
def translate_mutrec_vvvvvv_zUservv_zG_Stagev (sv_width : Nat) (asid : (BitVec (if ( 32 = 32  : Bool) then 9 else 16))) (vmid : (BitVec (if ( 32
  = 32  : Bool) then 7 else 14))) (base_ppn : (BitVec (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  match (← (lookup_TLB sv_width asid vmid vpn G_Stage)) with
  | .some (index, ent) =>
    (translate_TLB_hit_mutrec_vvvvv_zUservvvv_zG_Stagev sv_width asid vmid vpn access mxr do_sum
      index ent ext_ptw)
  | none =>
    (translate_TLB_miss_mutrec_vvvvvv_zUservv_zG_Stagev sv_width asid vmid base_ppn vpn access mxr
      do_sum ext_ptw)

/-- Type quantifiers: k_n : Nat, sv_width : Nat, k_n ≥ 0, (is_sv_or_svx4_mode sv_width) ∧
  k_n ≥ sv_width -/
def translate_stage_mutrec_vvv_zUser_zG_Stage (sv_width : Nat) (addr : (BitVec k_n)) (access : (MemoryAccessType mem_payload)) : SailM (Result ((BitVec (if ( 32
  = 32  : Bool) then 34 else 64)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  match (translate_validate_address addr sv_width G_Stage) with
  | .Err e => (pure (Err (e, init_ext_ptw)))
  | .Ok valid_addr =>
    (do
      assert ((true && ((sv_width == 32) || (sv_width == 34))) || false) "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail:542.60-542.61"
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
      assert (sv_width ≤b gpalen) "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail:588.27-588.28"
      (translate_stage_mutrec_vvv_zUser_zG_Stage sv_width gpa access))

def translate_PTE_addr (pte_addr : (BitVec (if ( 32 = 32  : Bool) then 34 else 64))) (access : (MemoryAccessType mem_payload)) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result (physaddr × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  if ((stage == VS_Stage) : Bool)
  then
    (do
      match (← (translate_g_stage pte_addr access)) with
      | .Ok (pa, pbmt, ext_ptw) => (pure (Ok ((Physaddr pa), pbmt, ext_ptw)))
      | .Err (f, ext_ptw) => (pure (Err (f, ext_ptw))))
  else (pure (Ok ((Physaddr pte_addr), PBMT_PMA, ext_ptw)))

/-- Type quantifiers: k_ex436455_ : Bool, level : Nat, k_ex436453_ : Bool, k_ex436452_ : Bool, sv_width
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
  assert ((sv_width == 32) || ((sv_width == 34) || (xlen == 64))) "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail:176.41-176.42"
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

/-- Type quantifiers: tlb_index : Nat, k_ex436463_ : Bool, k_ex436462_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
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

/-- Type quantifiers: k_ex436471_ : Bool, k_ex436470_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
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

/-- Type quantifiers: k_ex436478_ : Bool, k_ex436477_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width) -/
def translate (sv_width : Nat) (asid : (BitVec (if ( 32 = 32  : Bool) then 9 else 16))) (vmid : (BitVec (if ( 32
  = 32  : Bool) then 7 else 14))) (base_ppn : (BitVec (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  match (← (lookup_TLB sv_width asid vmid vpn stage)) with
  | .some (index, ent) =>
    (translate_TLB_hit sv_width asid vmid vpn access priv mxr do_sum index ent stage ext_ptw)
  | none =>
    (translate_TLB_miss sv_width asid vmid base_ppn vpn access priv mxr do_sum stage ext_ptw)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, sv_width : Nat, (is_sv_or_svx4_mode sv_width) ∧
  k_n ≥ sv_width -/
def translate_stage (sv_width : Nat) (addr : (BitVec k_n)) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (stage : TranslationStage) : SailM (Result ((BitVec (if ( 32
  = 32  : Bool) then 34 else 64)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  match (translate_validate_address addr sv_width stage) with
  | .Err e => (pure (Err (e, init_ext_ptw)))
  | .Ok valid_addr =>
    (do
      assert (((xlen == 32) && ((sv_width == 32) || (sv_width == 34))) || ((xlen == 64) && ((sv_width != 32) && (sv_width != 34)))) "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail:542.60-542.61"
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
            assert (xlen ≥b 64) "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail:342.33-342.34"
            throw Error.Exit)
        | .RV32 =>
          (pure (0b000#3 +++ (_get_Satp32_Mode
                (Mk_Satp32 (Sail.BitVec.extractLsb (← readReg satp) 31 0)))))
        | .RV128 =>
          (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail" 344
            "RV128 not supported") ) : SailM SailRV32.satp_mode )
      match (← (satpMode_of_bits arch mbits)) with
      | .some m => (pure m)
      | none =>
        (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail" 349
          "invalid translation mode in satp"))

def vsatp_mode (_ : Unit) : SailM SATPMode := do
  let arch ← do (architecture VirtualSupervisor)
  let mbits ← (( do
    match arch with
    | .RV64 =>
      (do
        assert (xlen ≥b 64) "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail:360.31-360.32"
        throw Error.Exit)
    | .RV32 =>
      (pure (0b000#3 +++ (_get_Satp32_Mode
            (Mk_Satp32 (Sail.BitVec.extractLsb (← readReg vsatp) 31 0)))))
    | .RV128 =>
      (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail" 362
        "RV128 not supported") ) : SailM SailRV32.satp_mode )
  match (← (satpMode_of_bits arch mbits)) with
  | .some m => (pure m)
  | none =>
    (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail" 367
      "invalid translation mode in vsatp")

def satp_mode_width_forwards (arg_ : SATPMode) : SailM Int := do
  match arg_ with
  | .Sv32 => (pure 32)
  | .Sv39 => (pure 39)
  | .Sv48 => (pure 48)
  | .Sv57 => (pure 57)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

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
      assert (sv_width ≤b xlen) "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail:575.25-575.26"
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
            | _ =>
              (internal_error "/private/tmp/airbender-sail-integration/model/model/sys/vmem.sail"
                636 "invalid memory access type") ) : SailM Bool )
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

def RETIRE_SUCCESS : ExecutionResult := (Retire_Success ())

def trap (exc : ExceptionContext) : SailM ExecutionResult := do
  (pure (Trap ((← readReg cur_privilege), exc, (← readReg PC))))

/-- Type quantifiers: k_ex436522_ : Bool -/
def plat_misaligned_exception (access : (MemoryAccessType mem_payload)) (res : Bool) : (Option misaligned_exception) :=
  if ((is_amo_access access) : Bool)
  then plat_misaligned_access.amo
  else
    (if (res : Bool)
    then plat_misaligned_access.lrsc
    else
      (if ((is_vector_access access) : Bool)
      then plat_misaligned_access.vector
      else plat_misaligned_access.load_store))

def offset_virtaddr_by (typ_0 : virtaddr) (typ_1 : physaddr) (typ_2 : physaddr) : virtaddr :=
  let .Virtaddr base_vaddr : virtaddr := typ_0
  let .Physaddr base_paddr : physaddr := typ_1
  let .Physaddr exc_paddr : physaddr := typ_2
  let offset := (Sail.BitVec.extractLsb (exc_paddr - base_paddr) (xlen -i 1) 0)
  let reconstructed := (base_vaddr + offset)
  let masked := reconstructed
  (Virtaddr masked)

def default_access_info (access : (MemoryAccessType mem_payload)) : SailM AccessInfo := do
  let eff_priv ← do (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))
  (pure { eff_privilege := eff_priv
          pmlen := ← (get_pmlen access eff_priv)
          as_guest := false })

def transform_effective_address (vaddr : virtaddr) (access_info : AccessInfo) : SailM virtaddr := do
  let eff_privilege := access_info.eff_privilege
  let pmlen := access_info.pmlen
  let mode ← do
    if (((eff_privilege == VirtualSupervisor) || (eff_privilege == VirtualUser)) : Bool)
    then (vsatp_mode ())
    else (satp_mode eff_privilege)
  if ((mode == Bare) : Bool)
  then (pure (pm_transform_PA vaddr pmlen))
  else (pure (pm_transform_VA vaddr pmlen))

def access_is_gva (access_info : AccessInfo) : Bool :=
  ((privLevel_is_virtual access_info.eff_privilege) || access_info.as_guest)

def mem_exception_context (e : ExceptionType) (excinfo : (BitVec 32)) (access_info : AccessInfo) : ExceptionContext :=
  (make_exception_context e excinfo (access_is_gva access_info) none)

def with_excinst_offset (e : ExecutionResult) (vaddr : virtaddr) : ExecutionResult :=
  match e with
  | .Trap (priv, ctx, pc) =>
    (Trap
      (priv, { ctx with excinst_offset := (Sail.BitVec.truncate
          (ctx.excinfo - (bits_of_virtaddr vaddr)) 5) }, pc))
  | _ => e

def memory_exception (e : ExceptionType) (excinfo : (BitVec 32)) (access_info : AccessInfo) : SailM ExecutionResult := do
  (trap (mem_exception_context e excinfo access_info))

/-- Type quantifiers: k_ex436525_ : Bool, k_ex436524_ : Bool, k_ex436523_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def translate_and_read_value (vaddr : virtaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (access_info : AccessInfo) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (physaddr × (BitVec (8 * width))) ExecutionResult) := do
  let eff_priv := access_info.eff_privilege
  match (← (translateAddr vaddr access eff_priv)) with
  | .Err (e, _) => (pure (Err (← (trap e))))
  | .Ok (paddr, pbmt, _) =>
    (do
      match (← (mem_read access pbmt eff_priv paddr width aq rl res)) with
      | .Err (exc_paddr, e) =>
        (do
          let exc_vaddr := (offset_virtaddr_by vaddr paddr exc_paddr)
          (pure (Err (← (memory_exception e (bits_of_virtaddr exc_vaddr) access_info)))))
      | .Ok v => (pure (Ok (paddr, v))))

/-- Type quantifiers: k_ex436531_ : Bool, k_ex436530_ : Bool, k_ex436529_ : Bool, width : Nat, width
  ≥ 0, (is_mem_width width) -/
def vmem_read_addr (vaddr : virtaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (access_info : AccessInfo) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExecutionResult) := SailME.run do
  assert (res == (is_load_reserved access)) "/private/tmp/airbender-sail-integration/model/model/sys/vmem_utils.sail:143.40-143.41"
  let eff_priv := access_info.eff_privilege
  if ((not (is_aligned_vaddr vaddr width)) : Bool)
  then
    (do
      match (plat_misaligned_exception access res) with
      | .some .AccessFault =>
        SailME.throw (← do
            (pure (Err
                (← (memory_exception (E_Load_Access_Fault ()) (bits_of_virtaddr vaddr) access_info)))))
      | .some .AlignmentException =>
        SailME.throw (← do
            (pure (Err
                (← (memory_exception (E_Load_Addr_Align ()) (bits_of_virtaddr vaddr) access_info)))))
      | none => (pure ()))
  else (pure ())
  let vaddr_bits := (bits_of_virtaddr vaddr)
  let (in_page_bytes, next_page_bytes) ← do (split_on_page_boundary vaddr_bits width)
  let data := (zeros (n := (8 *i width)))
  let vmem_active ← (( do
    if ((privLevel_is_virtual eff_priv) : Bool)
    then (pure ((bne (← (vsatp_mode ())) Bare) || (bne (← (hgatp_mode ())) HBare)))
    else (pure (bne (← (satp_mode eff_priv)) Bare)) ) : SailME
    (Result (BitVec (8 * width)) ExecutionResult) Bool )
  let do_split_access := (vmem_active && ((next_page_bytes >b 0) && (not res)))
  let data ← (( do
    if ((sys_misaligned_order_decreasing && do_split_access) : Bool)
    then
      (do
        let access_addr := (Virtaddr (BitVec.addInt vaddr_bits in_page_bytes))
        match (← (translate_and_read_value access_addr next_page_bytes access access_info aq rl
            res)) with
        | .Err e => SailME.throw ((Err e) : (Result (BitVec (8 * width)) ExecutionResult))
        | .Ok (_, v) =>
          (pure (Sail.BitVec.updateSubrange data ((8 *i width) -i 1) (8 *i in_page_bytes) v)))
    else (pure data) ) : SailME (Result (BitVec (8 * width)) ExecutionResult) (BitVec (8 * width)) )
  let access_width :=
    if (do_split_access : Bool)
    then in_page_bytes
    else width
  let data ← (( do
    match (← (translate_and_read_value vaddr access_width access access_info aq rl res)) with
    | .Err e => SailME.throw ((Err e) : (Result (BitVec (8 * width)) ExecutionResult))
    | .Ok (paddr, v) =>
      (do
        if (res : Bool)
        then
          (do
            assert (width == access_width) "/private/tmp/airbender-sail-integration/model/model/sys/vmem_utils.sail:192.36-192.37"
            (load_reservation (bits_of_physaddr paddr) width))
        else (pure ())
        (pure (Sail.BitVec.updateSubrange data ((8 *i access_width) -i 1) 0 v))) ) : SailME
    (Result (BitVec (8 * width)) ExecutionResult) (BitVec (8 * width)) )
  let data ← (( do
    if (((not sys_misaligned_order_decreasing) && do_split_access) : Bool)
    then
      (do
        let access_addr := (Virtaddr (BitVec.addInt vaddr_bits in_page_bytes))
        match (← (translate_and_read_value access_addr next_page_bytes access access_info aq rl
            res)) with
        | .Err e => SailME.throw ((Err e) : (Result (BitVec (8 * width)) ExecutionResult))
        | .Ok (_, v) =>
          (pure (Sail.BitVec.updateSubrange data ((8 *i width) -i 1) (8 *i in_page_bytes) v)))
    else (pure data) ) : SailME (Result (BitVec (8 * width)) ExecutionResult) (BitVec (8 * width)) )
  (pure (Ok data))

/-- Type quantifiers: k_ex436536_ : Bool, k_ex436535_ : Bool, k_ex436534_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def translate_and_write_value (vaddr : virtaddr) (width : Nat) (value : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (access_info : AccessInfo) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := do
  let eff_priv := access_info.eff_privilege
  match (← (translateAddr vaddr access eff_priv)) with
  | .Err (e, _) => (pure (Err (← (trap e))))
  | .Ok (paddr, pbmt, _) =>
    (do
      match (← (mem_write_ea paddr width eff_priv access pbmt aq rl res)) with
      | .Err (exc_paddr, e) =>
        (do
          let exc_vaddr := (offset_virtaddr_by vaddr paddr exc_paddr)
          (pure (Err (← (memory_exception e (bits_of_virtaddr exc_vaddr) access_info)))))
      | .Ok () =>
        (do
          match (← (mem_write_value paddr width value eff_priv access pbmt aq rl res)) with
          | .Err (exc_paddr, e) =>
            (do
              let exc_vaddr := (offset_virtaddr_by vaddr paddr exc_paddr)
              (pure (Err (← (memory_exception e (bits_of_virtaddr exc_vaddr) access_info)))))
          | .Ok s => (pure (Ok s))))

/-- Type quantifiers: k_ex436542_ : Bool, k_ex436541_ : Bool, k_ex436540_ : Bool, width : Nat, width
  ≥ 0, (is_mem_width width) -/
def vmem_write_addr (vaddr : virtaddr) (width : Nat) (data : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (access_info : AccessInfo) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := SailME.run do
  assert (res == (is_store_conditional access)) "/private/tmp/airbender-sail-integration/model/model/sys/vmem_utils.sail:245.44-245.45"
  let eff_priv := access_info.eff_privilege
  if ((not (is_aligned_vaddr vaddr width)) : Bool)
  then
    (do
      match (plat_misaligned_exception access res) with
      | .some .AccessFault =>
        SailME.throw (← do
            (pure (Err
                (← (memory_exception (E_SAMO_Access_Fault ()) (bits_of_virtaddr vaddr) access_info)))))
      | .some .AlignmentException =>
        SailME.throw (← do
            (pure (Err
                (← (memory_exception (E_SAMO_Addr_Align ()) (bits_of_virtaddr vaddr) access_info)))))
      | none => (pure ()))
  else (pure ())
  let vaddr_bits := (bits_of_virtaddr vaddr)
  let write_success : Bool := true
  let (in_page_bytes, next_page_bytes) ← do (split_on_page_boundary vaddr_bits width)
  let vmem_active ← (( do
    if ((privLevel_is_virtual eff_priv) : Bool)
    then (pure ((bne (← (vsatp_mode ())) Bare) || (bne (← (hgatp_mode ())) HBare)))
    else (pure (bne (← (satp_mode eff_priv)) Bare)) ) : SailME (Result Bool ExecutionResult) Bool
    )
  let do_split_access := (vmem_active && ((next_page_bytes >b 0) && (not res)))
  let write_success ← (( do
    if ((sys_misaligned_order_decreasing && do_split_access) : Bool)
    then
      (do
        let access_addr := (Virtaddr (BitVec.addInt vaddr_bits in_page_bytes))
        let write_value := (Sail.BitVec.extractLsb data ((8 *i width) -i 1) (8 *i in_page_bytes))
        match (← (translate_and_write_value access_addr next_page_bytes write_value access
            access_info aq rl res)) with
        | .Err e => SailME.throw ((Err e) : (Result Bool ExecutionResult))
        | .Ok s => (pure (write_success && s)))
    else (pure write_success) ) : SailME (Result Bool ExecutionResult) Bool )
  let access_width :=
    if (do_split_access : Bool)
    then in_page_bytes
    else width
  let write_success ← (( do
    match (← (translateAddr vaddr access eff_priv)) with
    | .Err (e, _) =>
      SailME.throw (← do
          (pure (Err (← (trap e)))))
    | .Ok (paddr, pbmt, _) =>
      (do
        if ((res && (not (match_reservation (bits_of_physaddr paddr)))) : Bool)
        then
          (do
            match (← (phys_access_check access pbmt eff_priv paddr access_width true)) with
            | .Err e =>
              SailME.throw (← do
                  (pure (Err (← (memory_exception e (bits_of_virtaddr vaddr) access_info)))))
            | .Ok _ => (pure false))
        else
          (do
            match (← (mem_write_ea paddr access_width eff_priv access pbmt aq rl res)) with
            | .Err (exc_paddr, e) =>
              SailME.throw (← do
                  let exc_vaddr := (offset_virtaddr_by vaddr paddr exc_paddr)
                  (pure (Err (← (memory_exception e (bits_of_virtaddr exc_vaddr) access_info)))))
            | .Ok () =>
              (do
                let write_value := (Sail.BitVec.extractLsb data ((8 *i access_width) -i 1) 0)
                match (← (mem_write_value paddr access_width write_value eff_priv access pbmt aq
                    rl res)) with
                | .Err (exc_paddr, e) =>
                  SailME.throw (← do
                      let exc_vaddr := (offset_virtaddr_by vaddr paddr exc_paddr)
                      (pure (Err (← (memory_exception e (bits_of_virtaddr exc_vaddr) access_info)))))
                | .Ok s => (pure (write_success && s))))) ) : SailME (Result Bool ExecutionResult)
    Bool )
  let write_success ← (( do
    if (((not sys_misaligned_order_decreasing) && do_split_access) : Bool)
    then
      (do
        let access_addr := (Virtaddr (BitVec.addInt vaddr_bits in_page_bytes))
        let write_value := (Sail.BitVec.extractLsb data ((8 *i width) -i 1) (8 *i in_page_bytes))
        match (← (translate_and_write_value access_addr next_page_bytes write_value access
            access_info aq rl res)) with
        | .Err e => SailME.throw ((Err e) : (Result Bool ExecutionResult))
        | .Ok s => (pure (write_success && s)))
    else (pure write_success) ) : SailME (Result Bool ExecutionResult) Bool )
  (pure (Ok write_success))

/-- Type quantifiers: width : Nat, 1 ≤ width ∧ width ≤ 4096 -/
def get_transformed_data_addr (base : regidx) (offset : (BitVec 32)) (access : (MemoryAccessType mem_payload)) (access_info : AccessInfo) (width : Nat) : SailM (Ext_DataAddr_Check Unit) := do
  let eff_priv := access_info.eff_privilege
  match (← (ext_data_get_addr base offset access width)) with
  | .Ext_DataAddr_Error e => (pure (Ext_DataAddr_Error e))
  | .Ext_DataAddr_OK vaddr =>
    (do
      let vaddr ← do (transform_effective_address vaddr access_info)
      (pure (Ext_DataAddr_OK vaddr)))

/-- Type quantifiers: k_ex436551_ : Bool, k_ex436550_ : Bool, k_ex436549_ : Bool, width : Nat, width
  ≥ 0, (is_mem_width width) -/
def vmem_read_explicit (rs : regidx) (offset : (BitVec 32)) (width : Nat) (access : (MemoryAccessType mem_payload)) (access_info : AccessInfo) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExecutionResult) := SailME.run do
  let vaddr ← (( do
    match (← (get_transformed_data_addr rs offset access access_info width)) with
    | .Ext_DataAddr_OK vaddr => (pure vaddr)
    | .Ext_DataAddr_Error e =>
      SailME.throw ((Err (Ext_DataAddr_Check_Failure e)) : (Result (BitVec (8 * width)) ExecutionResult))
    ) : SailME (Result (BitVec (8 * width)) ExecutionResult) virtaddr )
  match (← (vmem_read_addr vaddr width access access_info aq rl res)) with
  | .Ok data => (pure (Ok data))
  | .Err e => (pure (Err (with_excinst_offset e vaddr)))

/-- Type quantifiers: k_ex436559_ : Bool, k_ex436558_ : Bool, k_ex436557_ : Bool, width : Nat, width
  ≥ 0, (is_mem_width width) -/
def vmem_read (rs : regidx) (offset : (BitVec 32)) (width : Nat) (access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExecutionResult) := do
  (vmem_read_explicit rs offset width access (← (default_access_info access)) aq rl res)

/-- Type quantifiers: k_ex436567_ : Bool, k_ex436566_ : Bool, k_ex436565_ : Bool, width : Nat, width
  ≥ 0, (is_mem_width width) -/
def vmem_write_explicit (rs_addr : regidx) (offset : (BitVec 32)) (width : Nat) (data : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (access_info : AccessInfo) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := SailME.run do
  let vaddr ← (( do
    match (← (get_transformed_data_addr rs_addr offset access access_info width)) with
    | .Ext_DataAddr_OK vaddr => (pure vaddr)
    | .Ext_DataAddr_Error e =>
      SailME.throw ((Err (Ext_DataAddr_Check_Failure e)) : (Result Bool ExecutionResult)) ) : SailME
    (Result Bool ExecutionResult) virtaddr )
  match (← (vmem_write_addr vaddr width data access access_info aq rl res)) with
  | .Ok s => (pure (Ok s))
  | .Err e => (pure (Err (with_excinst_offset e vaddr)))

/-- Type quantifiers: k_ex436575_ : Bool, k_ex436574_ : Bool, k_ex436573_ : Bool, width : Nat, width
  ≥ 0, (is_mem_width width) -/
def vmem_write (rs_addr : regidx) (offset : (BitVec 32)) (width : Nat) (data : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := do
  (vmem_write_explicit rs_addr offset width data access (← (default_access_info access)) aq rl res)

def encdec_uop_backwards (arg_ : (BitVec 7)) : SailM uop := do
  match arg_ with
  | 0b0110111 => (pure LUI)
  | 0b0010111 => (pure AUIPC)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_uop_backwards_matches (arg_ : (BitVec 7)) : Bool :=
  match arg_ with
  | 0b0110111 => true
  | 0b0010111 => true
  | _ => false

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

def encdec_bop_backwards (arg_ : (BitVec 3)) : SailM bop := do
  match arg_ with
  | 0b000 => (pure BEQ)
  | 0b001 => (pure BNE)
  | 0b100 => (pure BLT)
  | 0b101 => (pure BGE)
  | 0b110 => (pure BLTU)
  | 0b111 => (pure BGEU)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_bop_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match arg_ with
  | 0b000 => true
  | 0b001 => true
  | 0b100 => true
  | 0b101 => true
  | 0b110 => true
  | 0b111 => true
  | _ => false

def encdec_iop_backwards (arg_ : (BitVec 3)) : SailM iop := do
  match arg_ with
  | 0b000 => (pure ADDI)
  | 0b010 => (pure SLTI)
  | 0b011 => (pure SLTIU)
  | 0b111 => (pure ANDI)
  | 0b110 => (pure ORI)
  | 0b100 => (pure XORI)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_iop_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match arg_ with
  | 0b000 => true
  | 0b010 => true
  | 0b011 => true
  | 0b111 => true
  | 0b110 => true
  | 0b100 => true
  | _ => false

/-- Type quantifiers: k_ex436579_ : Bool, width : Nat, List.elem width [1, 2, 4, 8] -/
def valid_load_encdec (width : Nat) (is_unsigned : Bool) : Bool :=
  ((width <b xlen_bytes) || ((not is_unsigned) && (width ≤b xlen_bytes)))

/-- Type quantifiers: k_ex436580_ : Bool, k_n : Nat, k_n ≥ 0, 0 < k_n ∧ k_n ≤ xlen -/
def extend_value (is_unsigned : Bool) (value : (BitVec k_n)) : (BitVec 32) :=
  if (is_unsigned : Bool)
  then (zero_extend (m := 32) value)
  else (sign_extend (m := 32) value)

def encdec_mul_op_backwards (arg_ : (BitVec 3)) : SailM mul_op := do
  match arg_ with
  | 0b000 =>
    (pure { result_part := Low
            signed_rs1 := Signed
            signed_rs2 := Signed })
  | 0b001 =>
    (pure { result_part := High
            signed_rs1 := Signed
            signed_rs2 := Signed })
  | 0b010 =>
    (pure { result_part := High
            signed_rs1 := Signed
            signed_rs2 := Unsigned })
  | 0b011 =>
    (pure { result_part := High
            signed_rs1 := Unsigned
            signed_rs2 := Unsigned })
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_mul_op_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match arg_ with
  | 0b000 => true
  | 0b001 => true
  | 0b010 => true
  | 0b011 => true
  | _ => false

def encdec_csrop_backwards (arg_ : (BitVec 2)) : SailM csrop := do
  match arg_ with
  | 0b01 => (pure CSRRW)
  | 0b10 => (pure CSRRS)
  | 0b11 => (pure CSRRC)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_csrop_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

def encdec_backwards (arg_ : (BitVec 32)) : SailM instruction := do
  let head_exp_ := arg_
  match (← do
    let v__354 := head_exp_
    if ((let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__354 6 0)
       let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__354 11 7)
       ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_))) : Bool)
    then
      (do
        let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__354 31 12)
        let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__354 6 0)
        let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__354 11 7)
        let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__354 31 12)
        match ((← (encdec_reg_backwards mapping0_)), (← (encdec_uop_backwards mapping1_))) with
        | (rd, op) => (pure (some (UTYPE (imm, rd, op)))))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__352 := head_exp_
        if (((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__352 11 7)
             (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__352 6 0) == (0b1101111#7 : (BitVec 7)))) : Bool)
        then
          (do
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__352 31 31)
            let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__352 11 7)
            let imm_9_0_ : (BitVec 10) := (Sail.BitVec.extractLsb v__352 30 21)
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__352 31 31)
            let imm_18_11_ : (BitVec 8) := (Sail.BitVec.extractLsb v__352 19 12)
            let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__352 20 20)
            match (← (encdec_reg_backwards mapping2_)) with
            | rd =>
              (pure (some
                  (let imm := (((imm_19_19_ +++ imm_18_11_) +++ imm_10_10_) +++ imm_9_0_)
                  (JAL ((imm +++ 0#1), rd))))))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (do
          match (← do
            let v__349 := head_exp_
            if (((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__349 11 7)
                 let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__349 19 15)
                 ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__349 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__349 6 0) == (0b1100111#7 : (BitVec 7))))) : Bool)
            then
              (do
                let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__349 31 20)
                let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__349 11 7)
                let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__349 19 15)
                let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__349 31 20)
                match ((← (encdec_reg_backwards mapping3_)), (← (encdec_reg_backwards mapping4_))) with
                | (rs1, rd) => (pure (some (JALR (imm, rs1, rd)))))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__347 := head_exp_
                if (((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__347 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__347 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__347 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__347 6 0) == (0b1100011#7 : (BitVec 7)))) : Bool)
                then
                  (do
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__347 31 31)
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__347 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__347 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__347 24 20)
                    let imm_9_4_ : (BitVec 6) := (Sail.BitVec.extractLsb v__347 30 25)
                    let imm_3_0_ : (BitVec 4) := (Sail.BitVec.extractLsb v__347 11 8)
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__347 31 31)
                    let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__347 7 7)
                    match ((← (encdec_reg_backwards mapping5_)), (← (encdec_reg_backwards
                        mapping6_)), (← (encdec_bop_backwards mapping7_))) with
                    | (rs2, rs1, op) =>
                      (pure (some
                          (let imm := (((imm_11_11_ +++ imm_10_10_) +++ imm_9_4_) +++ imm_3_0_)
                          (BTYPE ((imm +++ 0#1), rs2, rs1, op))))))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__345 := head_exp_
                    if (((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__345 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__345 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__345 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__345 6 0) == (0b0010011#7 : (BitVec 7)))) : Bool)
                    then
                      (do
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__345 31 20)
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__345 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__345 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__345 11 7)
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__345 31 20)
                        match ((← (encdec_reg_backwards mapping8_)), (← (encdec_iop_backwards
                            mapping9_)), (← (encdec_reg_backwards mapping10_))) with
                        | (rs1, op, rd) => (pure (some (ITYPE (imm, rs1, rd, op)))))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__341 := head_exp_
                        if (((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__341 11 7)
                             let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__341 19 15)
                             ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                                 mapping12_))) && (((Sail.BitVec.extractLsb v__341 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                     v__341 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                     v__341 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                        then
                          (do
                            let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__341 25 20)
                            let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__341 11 7)
                            let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__341 19 15)
                            match ((← (encdec_reg_backwards mapping11_)), (← (encdec_reg_backwards
                                mapping12_))) with
                            | (rs1, rd) =>
                              (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                              then (pure (some (SHIFTIOP (shamt, rs1, rd, SLLI))))
                              else (pure none)))
                        else (pure none)) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (← do
                            let v__337 := head_exp_
                            if (((let mapping14_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__337 11 7)
                                 let mapping13_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__337 19 15)
                                 ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                     mapping14_))) && (((Sail.BitVec.extractLsb v__337 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                         v__337 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                         v__337 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                            then
                              (do
                                let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__337 25 20)
                                let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__337 11 7)
                                let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__337 19 15)
                                match ((← (encdec_reg_backwards mapping13_)), (← (encdec_reg_backwards
                                    mapping14_))) with
                                | (rs1, rd) =>
                                  (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                  then (pure (some (SHIFTIOP (shamt, rs1, rd, SRLI))))
                                  else (pure none)))
                            else (pure none)) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (← do
                                let v__333 := head_exp_
                                if (((let mapping16_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__333 11 7)
                                     let mapping15_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__333 19 15)
                                     ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                         mapping16_))) && (((Sail.BitVec.extractLsb v__333 31 26) == (0b010000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                             v__333 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                             v__333 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                then
                                  (do
                                    let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__333 25 20)
                                    let mapping16_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__333 11 7)
                                    let mapping15_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__333 19 15)
                                    match ((← (encdec_reg_backwards mapping15_)), (← (encdec_reg_backwards
                                        mapping16_))) with
                                    | (rs1, rd) =>
                                      (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                      then (pure (some (SHIFTIOP (shamt, rs1, rd, SRAI))))
                                      else (pure none)))
                                else (pure none)) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (← do
                                    let v__329 := head_exp_
                                    if (((let mapping19_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__329 11 7)
                                         let mapping18_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__329 19 15)
                                         let mapping17_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__329 24 20)
                                         ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                               mapping18_) && (encdec_reg_backwards_matches
                                               mapping19_)))) && (((Sail.BitVec.extractLsb v__329 31
                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                 v__329 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                 v__329 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                    then
                                      (do
                                        let mapping19_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__329 11 7)
                                        let mapping18_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__329 19 15)
                                        let mapping17_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__329 24 20)
                                        match ((← (encdec_reg_backwards mapping17_)), (← (encdec_reg_backwards
                                            mapping18_)), (← (encdec_reg_backwards mapping19_))) with
                                        | (rs2, rs1, rd) =>
                                          (pure (some (RTYPE (rs2, rs1, rd, ADD)))))
                                    else (pure none)) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__325 := head_exp_
                                        if (((let mapping22_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__325 11 7)
                                             let mapping21_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__325 19 15)
                                             let mapping20_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__325 24 20)
                                             ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                   mapping21_) && (encdec_reg_backwards_matches
                                                   mapping22_)))) && (((Sail.BitVec.extractLsb
                                                   v__325 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                     v__325 14 12) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                     v__325 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                        then
                                          (do
                                            let mapping22_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__325 11 7)
                                            let mapping21_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__325 19 15)
                                            let mapping20_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__325 24 20)
                                            match ((← (encdec_reg_backwards mapping20_)), (← (encdec_reg_backwards
                                                mapping21_)), (← (encdec_reg_backwards mapping22_))) with
                                            | (rs2, rs1, rd) =>
                                              (pure (some (RTYPE (rs2, rs1, rd, SLT)))))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__321 := head_exp_
                                            if (((let mapping25_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__321 11 7)
                                                 let mapping24_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__321 19 15)
                                                 let mapping23_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__321 24 20)
                                                 ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                       mapping24_) && (encdec_reg_backwards_matches
                                                       mapping25_)))) && (((Sail.BitVec.extractLsb
                                                       v__321 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                         v__321 14 12) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                         v__321 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                            then
                                              (do
                                                let mapping25_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__321 11 7)
                                                let mapping24_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__321 19 15)
                                                let mapping23_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__321 24 20)
                                                match ((← (encdec_reg_backwards mapping23_)), (← (encdec_reg_backwards
                                                    mapping24_)), (← (encdec_reg_backwards
                                                    mapping25_))) with
                                                | (rs2, rs1, rd) =>
                                                  (pure (some (RTYPE (rs2, rs1, rd, SLTU)))))
                                            else (pure none)) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (← do
                                                let v__317 := head_exp_
                                                if (((let mapping28_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__317 11 7)
                                                     let mapping27_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__317 19 15)
                                                     let mapping26_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__317 24 20)
                                                     ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                           mapping27_) && (encdec_reg_backwards_matches
                                                           mapping28_)))) && (((Sail.BitVec.extractLsb
                                                           v__317 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                             v__317 14 12) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                             v__317 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping28_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__317 11 7)
                                                    let mapping27_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__317 19 15)
                                                    let mapping26_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__317 24 20)
                                                    match ((← (encdec_reg_backwards mapping26_)), (← (encdec_reg_backwards
                                                        mapping27_)), (← (encdec_reg_backwards
                                                        mapping28_))) with
                                                    | (rs2, rs1, rd) =>
                                                      (pure (some (RTYPE (rs2, rs1, rd, AND)))))
                                                else (pure none)) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (← do
                                                    let v__313 := head_exp_
                                                    if (((let mapping31_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__313 11 7)
                                                         let mapping30_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__313 19 15)
                                                         let mapping29_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__313 24 20)
                                                         ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                               mapping30_) && (encdec_reg_backwards_matches
                                                               mapping31_)))) && (((Sail.BitVec.extractLsb
                                                               v__313 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                 v__313 14 12) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                 v__313 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping31_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__313 11 7)
                                                        let mapping30_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__313 19 15)
                                                        let mapping29_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__313 24 20)
                                                        match ((← (encdec_reg_backwards mapping29_)), (← (encdec_reg_backwards
                                                            mapping30_)), (← (encdec_reg_backwards
                                                            mapping31_))) with
                                                        | (rs2, rs1, rd) =>
                                                          (pure (some (RTYPE (rs2, rs1, rd, OR)))))
                                                    else (pure none)) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (← do
                                                        let v__309 := head_exp_
                                                        if (((let mapping34_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__309 11 7)
                                                             let mapping33_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__309 19 15)
                                                             let mapping32_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__309 24 20)
                                                             ((encdec_reg_backwards_matches
                                                                 mapping32_) && ((encdec_reg_backwards_matches
                                                                   mapping33_) && (encdec_reg_backwards_matches
                                                                   mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                   v__309 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                     v__309 14 12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                     v__309 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping34_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__309 11 7)
                                                            let mapping33_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__309 19 15)
                                                            let mapping32_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__309 24 20)
                                                            match ((← (encdec_reg_backwards
                                                                mapping32_)), (← (encdec_reg_backwards
                                                                mapping33_)), (← (encdec_reg_backwards
                                                                mapping34_))) with
                                                            | (rs2, rs1, rd) =>
                                                              (pure (some
                                                                  (RTYPE (rs2, rs1, rd, XOR)))))
                                                        else (pure none)) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (← do
                                                            let v__305 := head_exp_
                                                            if (((let mapping37_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__305 11
                                                                     7)
                                                                 let mapping36_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__305 19
                                                                     15)
                                                                 let mapping35_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__305 24
                                                                     20)
                                                                 ((encdec_reg_backwards_matches
                                                                     mapping35_) && ((encdec_reg_backwards_matches
                                                                       mapping36_) && (encdec_reg_backwards_matches
                                                                       mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                       v__305 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                         v__305 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                         v__305 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping37_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__305 11
                                                                    7)
                                                                let mapping36_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__305 19
                                                                    15)
                                                                let mapping35_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__305 24
                                                                    20)
                                                                match ((← (encdec_reg_backwards
                                                                    mapping35_)), (← (encdec_reg_backwards
                                                                    mapping36_)), (← (encdec_reg_backwards
                                                                    mapping37_))) with
                                                                | (rs2, rs1, rd) =>
                                                                  (pure (some
                                                                      (RTYPE (rs2, rs1, rd, SLL)))))
                                                            else (pure none)) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (← do
                                                                let v__301 := head_exp_
                                                                if (((let mapping40_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__301 11 7)
                                                                     let mapping39_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__301 19 15)
                                                                     let mapping38_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__301 24 20)
                                                                     ((encdec_reg_backwards_matches
                                                                         mapping38_) && ((encdec_reg_backwards_matches
                                                                           mapping39_) && (encdec_reg_backwards_matches
                                                                           mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                           v__301 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                             v__301 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                             v__301 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping40_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__301
                                                                        11 7)
                                                                    let mapping39_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__301
                                                                        19 15)
                                                                    let mapping38_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__301
                                                                        24 20)
                                                                    match ((← (encdec_reg_backwards
                                                                        mapping38_)), (← (encdec_reg_backwards
                                                                        mapping39_)), (← (encdec_reg_backwards
                                                                        mapping40_))) with
                                                                    | (rs2, rs1, rd) =>
                                                                      (pure (some
                                                                          (RTYPE (rs2, rs1, rd, SRL)))))
                                                                else (pure none)) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (← do
                                                                    let v__297 := head_exp_
                                                                    if (((let mapping43_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__297 11 7)
                                                                         let mapping42_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__297 19 15)
                                                                         let mapping41_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__297 24 20)
                                                                         ((encdec_reg_backwards_matches
                                                                             mapping41_) && ((encdec_reg_backwards_matches
                                                                               mapping42_) && (encdec_reg_backwards_matches
                                                                               mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                               v__297 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                 v__297 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                 v__297 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping43_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__297 11 7)
                                                                        let mapping42_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__297 19 15)
                                                                        let mapping41_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__297 24 20)
                                                                        match ((← (encdec_reg_backwards
                                                                            mapping41_)), (← (encdec_reg_backwards
                                                                            mapping42_)), (← (encdec_reg_backwards
                                                                            mapping43_))) with
                                                                        | (rs2, rs1, rd) =>
                                                                          (pure (some
                                                                              (RTYPE
                                                                                (rs2, rs1, rd, SUB)))))
                                                                    else (pure none)) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (← do
                                                                        let v__293 := head_exp_
                                                                        if (((let mapping46_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__293 11 7)
                                                                             let mapping45_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__293 19 15)
                                                                             let mapping44_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__293 24 20)
                                                                             ((encdec_reg_backwards_matches
                                                                                 mapping44_) && ((encdec_reg_backwards_matches
                                                                                   mapping45_) && (encdec_reg_backwards_matches
                                                                                   mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                   v__293 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                     v__293 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                     v__293 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping46_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__293 11 7)
                                                                            let mapping45_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__293 19 15)
                                                                            let mapping44_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__293 24 20)
                                                                            match ((← (encdec_reg_backwards
                                                                                mapping44_)), (← (encdec_reg_backwards
                                                                                mapping45_)), (← (encdec_reg_backwards
                                                                                mapping46_))) with
                                                                            | (rs2, rs1, rd) =>
                                                                              (pure (some
                                                                                  (RTYPE
                                                                                    (rs2, rs1, rd, SRA)))))
                                                                        else (pure none)) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (← do
                                                                            let v__291 := head_exp_
                                                                            if (((let mapping50_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__291 11 7)
                                                                                 let mapping49_ : (BitVec 2) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__291 13 12)
                                                                                 let mapping48_ : (BitVec 1) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__291 14 14)
                                                                                 let mapping47_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__291 19 15)
                                                                                 ((encdec_reg_backwards_matches
                                                                                     mapping47_) && ((bool_bit_backwards_matches
                                                                                       mapping48_) && ((width_enc_backwards_matches
                                                                                         mapping49_) && (encdec_reg_backwards_matches
                                                                                         mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                     v__291 6 0) == (0b0000011#7 : (BitVec 7)))) : Bool)
                                                                            then
                                                                              (do
                                                                                let imm : (BitVec 12) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__291 31 20)
                                                                                let mapping50_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__291 11 7)
                                                                                let mapping49_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__291 13 12)
                                                                                let mapping48_ : (BitVec 1) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__291 14 14)
                                                                                let mapping47_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__291 19 15)
                                                                                let imm : (BitVec 12) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__291 31 20)
                                                                                match ((← (encdec_reg_backwards
                                                                                    mapping47_)), (bool_bit_backwards
                                                                                  mapping48_), (width_enc_backwards
                                                                                  mapping49_), (← (encdec_reg_backwards
                                                                                    mapping50_))) with
                                                                                | (rs1, is_unsigned, width, rd) =>
                                                                                  (if ((valid_load_encdec
                                                                                       width
                                                                                       is_unsigned) : Bool)
                                                                                  then
                                                                                    (pure (some
                                                                                        (LOAD
                                                                                          (imm, rs1, rd, is_unsigned, width))))
                                                                                  else (pure none)))
                                                                            else (pure none)) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (← do
                                                                                let v__288 :=
                                                                                  head_exp_
                                                                                if (((let mapping53_ : (BitVec 2) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__288 13
                                                                                         12)
                                                                                     let mapping52_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__288 19
                                                                                         15)
                                                                                     let mapping51_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__288 24
                                                                                         20)
                                                                                     ((encdec_reg_backwards_matches
                                                                                         mapping51_) && ((encdec_reg_backwards_matches
                                                                                           mapping52_) && (width_enc_backwards_matches
                                                                                           mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                           v__288 14
                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                           v__288 6
                                                                                           0) == (0b0100011#7 : (BitVec 7))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__288 31 25)
                                                                                    let mapping53_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__288 13 12)
                                                                                    let mapping52_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__288 19 15)
                                                                                    let mapping51_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__288 24 20)
                                                                                    let imm_4_0_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__288 11 7)
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__288 31 25)
                                                                                    match ((← (encdec_reg_backwards
                                                                                        mapping51_)), (← (encdec_reg_backwards
                                                                                        mapping52_)), (width_enc_backwards
                                                                                      mapping53_)) with
                                                                                    | (rs2, rs1, width) =>
                                                                                      (if ((let imm :=
                                                                                           (imm_11_5_ +++ imm_4_0_)
                                                                                         (width ≤b xlen_bytes)) : Bool)
                                                                                      then
                                                                                        (pure (some
                                                                                            (let imm :=
                                                                                              (imm_11_5_ +++ imm_4_0_)
                                                                                            (STORE
                                                                                              (imm, rs2, rs1, width)))))
                                                                                      else
                                                                                        (pure none)))
                                                                                else (pure none)) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__285 :=
                                                                                      head_exp_
                                                                                    if (((let mapping55_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__285
                                                                                             11 7)
                                                                                         let mapping54_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__285
                                                                                             19 15)
                                                                                         ((encdec_reg_backwards_matches
                                                                                             mapping54_) && (encdec_reg_backwards_matches
                                                                                             mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                               v__285
                                                                                               14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__285
                                                                                               6 0) == (0b0011011#7 : (BitVec 7))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let imm : (BitVec 12) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__285
                                                                                            31 20)
                                                                                        let mapping55_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__285
                                                                                            11 7)
                                                                                        let mapping54_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__285
                                                                                            19 15)
                                                                                        let imm : (BitVec 12) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__285
                                                                                            31 20)
                                                                                        match ((← (encdec_reg_backwards
                                                                                            mapping54_)), (← (encdec_reg_backwards
                                                                                            mapping55_))) with
                                                                                        | (rs1, rd) =>
                                                                                          (if ((xlen == 64) : Bool)
                                                                                          then
                                                                                            (pure (some
                                                                                                (ADDIW
                                                                                                  (imm, rs1, rd))))
                                                                                          else
                                                                                            (pure none)))
                                                                                    else (pure none)) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (← do
                                                                                        let v__281 :=
                                                                                          head_exp_
                                                                                        if (((let mapping58_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__281
                                                                                                 11
                                                                                                 7)
                                                                                             let mapping57_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__281
                                                                                                 19
                                                                                                 15)
                                                                                             let mapping56_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__281
                                                                                                 24
                                                                                                 20)
                                                                                             ((encdec_reg_backwards_matches
                                                                                                 mapping56_) && ((encdec_reg_backwards_matches
                                                                                                   mapping57_) && (encdec_reg_backwards_matches
                                                                                                   mapping58_)))) && (((Sail.BitVec.extractLsb
                                                                                                   v__281
                                                                                                   31
                                                                                                   25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                     v__281
                                                                                                     14
                                                                                                     12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                     v__281
                                                                                                     6
                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let mapping58_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__281
                                                                                                11 7)
                                                                                            let mapping57_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__281
                                                                                                19
                                                                                                15)
                                                                                            let mapping56_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__281
                                                                                                24
                                                                                                20)
                                                                                            match ((← (encdec_reg_backwards
                                                                                                mapping56_)), (← (encdec_reg_backwards
                                                                                                mapping57_)), (← (encdec_reg_backwards
                                                                                                mapping58_))) with
                                                                                            | (rs2, rs1, rd) =>
                                                                                              (if ((xlen == 64) : Bool)
                                                                                              then
                                                                                                (pure (some
                                                                                                    (RTYPEW
                                                                                                      (rs2, rs1, rd, ADDW))))
                                                                                              else
                                                                                                (pure none)))
                                                                                        else
                                                                                          (pure none)) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (← do
                                                                                            let v__277 :=
                                                                                              head_exp_
                                                                                            if (((let mapping61_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__277
                                                                                                     11
                                                                                                     7)
                                                                                                 let mapping60_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__277
                                                                                                     19
                                                                                                     15)
                                                                                                 let mapping59_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__277
                                                                                                     24
                                                                                                     20)
                                                                                                 ((encdec_reg_backwards_matches
                                                                                                     mapping59_) && ((encdec_reg_backwards_matches
                                                                                                       mapping60_) && (encdec_reg_backwards_matches
                                                                                                       mapping61_)))) && (((Sail.BitVec.extractLsb
                                                                                                       v__277
                                                                                                       31
                                                                                                       25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                         v__277
                                                                                                         14
                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                         v__277
                                                                                                         6
                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__277
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping60_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__277
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping59_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__277
                                                                                                    24
                                                                                                    20)
                                                                                                match ((← (encdec_reg_backwards
                                                                                                    mapping59_)), (← (encdec_reg_backwards
                                                                                                    mapping60_)), (← (encdec_reg_backwards
                                                                                                    mapping61_))) with
                                                                                                | (rs2, rs1, rd) =>
                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                  then
                                                                                                    (pure (some
                                                                                                        (RTYPEW
                                                                                                          (rs2, rs1, rd, SUBW))))
                                                                                                  else
                                                                                                    (pure none)))
                                                                                            else
                                                                                              (pure none)) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (← do
                                                                                                let v__273 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping64_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__273
                                                                                                         11
                                                                                                         7)
                                                                                                     let mapping63_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__273
                                                                                                         19
                                                                                                         15)
                                                                                                     let mapping62_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__273
                                                                                                         24
                                                                                                         20)
                                                                                                     ((encdec_reg_backwards_matches
                                                                                                         mapping62_) && ((encdec_reg_backwards_matches
                                                                                                           mapping63_) && (encdec_reg_backwards_matches
                                                                                                           mapping64_)))) && (((Sail.BitVec.extractLsb
                                                                                                           v__273
                                                                                                           31
                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                             v__273
                                                                                                             14
                                                                                                             12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                             v__273
                                                                                                             6
                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__273
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping63_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__273
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping62_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__273
                                                                                                        24
                                                                                                        20)
                                                                                                    match ((← (encdec_reg_backwards
                                                                                                        mapping62_)), (← (encdec_reg_backwards
                                                                                                        mapping63_)), (← (encdec_reg_backwards
                                                                                                        mapping64_))) with
                                                                                                    | (rs2, rs1, rd) =>
                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                      then
                                                                                                        (pure (some
                                                                                                            (RTYPEW
                                                                                                              (rs2, rs1, rd, SLLW))))
                                                                                                      else
                                                                                                        (pure none)))
                                                                                                else
                                                                                                  (pure none)) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (← do
                                                                                                    let v__269 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping67_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__269
                                                                                                             11
                                                                                                             7)
                                                                                                         let mapping66_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__269
                                                                                                             19
                                                                                                             15)
                                                                                                         let mapping65_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__269
                                                                                                             24
                                                                                                             20)
                                                                                                         ((encdec_reg_backwards_matches
                                                                                                             mapping65_) && ((encdec_reg_backwards_matches
                                                                                                               mapping66_) && (encdec_reg_backwards_matches
                                                                                                               mapping67_)))) && (((Sail.BitVec.extractLsb
                                                                                                               v__269
                                                                                                               31
                                                                                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                 v__269
                                                                                                                 14
                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                 v__269
                                                                                                                 6
                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let mapping67_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__269
                                                                                                            11
                                                                                                            7)
                                                                                                        let mapping66_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__269
                                                                                                            19
                                                                                                            15)
                                                                                                        let mapping65_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__269
                                                                                                            24
                                                                                                            20)
                                                                                                        match ((← (encdec_reg_backwards
                                                                                                            mapping65_)), (← (encdec_reg_backwards
                                                                                                            mapping66_)), (← (encdec_reg_backwards
                                                                                                            mapping67_))) with
                                                                                                        | (rs2, rs1, rd) =>
                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                          then
                                                                                                            (pure (some
                                                                                                                (RTYPEW
                                                                                                                  (rs2, rs1, rd, SRLW))))
                                                                                                          else
                                                                                                            (pure none)))
                                                                                                    else
                                                                                                      (pure none)) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (← do
                                                                                                        let v__265 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping70_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__265
                                                                                                                 11
                                                                                                                 7)
                                                                                                             let mapping69_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__265
                                                                                                                 19
                                                                                                                 15)
                                                                                                             let mapping68_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__265
                                                                                                                 24
                                                                                                                 20)
                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                 mapping68_) && ((encdec_reg_backwards_matches
                                                                                                                   mapping69_) && (encdec_reg_backwards_matches
                                                                                                                   mapping70_)))) && (((Sail.BitVec.extractLsb
                                                                                                                   v__265
                                                                                                                   31
                                                                                                                   25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                     v__265
                                                                                                                     14
                                                                                                                     12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                     v__265
                                                                                                                     6
                                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping70_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__265
                                                                                                                11
                                                                                                                7)
                                                                                                            let mapping69_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__265
                                                                                                                19
                                                                                                                15)
                                                                                                            let mapping68_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__265
                                                                                                                24
                                                                                                                20)
                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                mapping68_)), (← (encdec_reg_backwards
                                                                                                                mapping69_)), (← (encdec_reg_backwards
                                                                                                                mapping70_))) with
                                                                                                            | (rs2, rs1, rd) =>
                                                                                                              (if ((xlen == 64) : Bool)
                                                                                                              then
                                                                                                                (pure (some
                                                                                                                    (RTYPEW
                                                                                                                      (rs2, rs1, rd, SRAW))))
                                                                                                              else
                                                                                                                (pure none)))
                                                                                                        else
                                                                                                          (pure none)) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (← do
                                                                                                            let v__261 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping72_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__261
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 let mapping71_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__261
                                                                                                                     19
                                                                                                                     15)
                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                     mapping71_) && (encdec_reg_backwards_matches
                                                                                                                     mapping72_))) && (((Sail.BitVec.extractLsb
                                                                                                                       v__261
                                                                                                                       31
                                                                                                                       25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                         v__261
                                                                                                                         14
                                                                                                                         12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                         v__261
                                                                                                                         6
                                                                                                                         0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let shamt : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__261
                                                                                                                    24
                                                                                                                    20)
                                                                                                                let mapping72_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__261
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let mapping71_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__261
                                                                                                                    19
                                                                                                                    15)
                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                    mapping71_)), (← (encdec_reg_backwards
                                                                                                                    mapping72_))) with
                                                                                                                | (rs1, rd) =>
                                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                                  then
                                                                                                                    (pure (some
                                                                                                                        (SHIFTIWOP
                                                                                                                          (shamt, rs1, rd, SLLIW))))
                                                                                                                  else
                                                                                                                    (pure none)))
                                                                                                            else
                                                                                                              (pure none)) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (← do
                                                                                                                let v__257 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping74_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__257
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     let mapping73_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__257
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping73_) && (encdec_reg_backwards_matches
                                                                                                                         mapping74_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__257
                                                                                                                           31
                                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                             v__257
                                                                                                                             14
                                                                                                                             12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                             v__257
                                                                                                                             6
                                                                                                                             0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let shamt : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__257
                                                                                                                        24
                                                                                                                        20)
                                                                                                                    let mapping74_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__257
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    let mapping73_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__257
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                        mapping73_)), (← (encdec_reg_backwards
                                                                                                                        mapping74_))) with
                                                                                                                    | (rs1, rd) =>
                                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                                      then
                                                                                                                        (pure (some
                                                                                                                            (SHIFTIWOP
                                                                                                                              (shamt, rs1, rd, SRLIW))))
                                                                                                                      else
                                                                                                                        (pure none)))
                                                                                                                else
                                                                                                                  (pure none)) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (← do
                                                                                                                    let v__253 :=
                                                                                                                      head_exp_
                                                                                                                    if (((let mapping76_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__253
                                                                                                                             11
                                                                                                                             7)
                                                                                                                         let mapping75_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__253
                                                                                                                             19
                                                                                                                             15)
                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                             mapping75_) && (encdec_reg_backwards_matches
                                                                                                                             mapping76_))) && (((Sail.BitVec.extractLsb
                                                                                                                               v__253
                                                                                                                               31
                                                                                                                               25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                 v__253
                                                                                                                                 14
                                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                 v__253
                                                                                                                                 6
                                                                                                                                 0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let shamt : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__253
                                                                                                                            24
                                                                                                                            20)
                                                                                                                        let mapping76_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__253
                                                                                                                            11
                                                                                                                            7)
                                                                                                                        let mapping75_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__253
                                                                                                                            19
                                                                                                                            15)
                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                            mapping75_)), (← (encdec_reg_backwards
                                                                                                                            mapping76_))) with
                                                                                                                        | (rs1, rd) =>
                                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                                          then
                                                                                                                            (pure (some
                                                                                                                                (SHIFTIWOP
                                                                                                                                  (shamt, rs1, rd, SRAIW))))
                                                                                                                          else
                                                                                                                            (pure none)))
                                                                                                                    else
                                                                                                                      (pure none)) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (do
                                                                                                                      match (← do
                                                                                                                        let v__242 :=
                                                                                                                          head_exp_
                                                                                                                        if ((v__242 == (0x8330000F#32 : (BitVec 32))) : Bool)
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              (FENCE_TSO
                                                                                                                                ())))
                                                                                                                        else
                                                                                                                          (do
                                                                                                                            if (((let mapping78_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__242
                                                                                                                                     11
                                                                                                                                     7)
                                                                                                                                 let mapping77_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__242
                                                                                                                                     19
                                                                                                                                     15)
                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                     mapping77_) && (encdec_reg_backwards_matches
                                                                                                                                     mapping78_))) && (((Sail.BitVec.extractLsb
                                                                                                                                       v__242
                                                                                                                                       14
                                                                                                                                       12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                       v__242
                                                                                                                                       6
                                                                                                                                       0) == (0b0001111#7 : (BitVec 7))))) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let fm : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__242
                                                                                                                                    31
                                                                                                                                    28)
                                                                                                                                let succ : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__242
                                                                                                                                    23
                                                                                                                                    20)
                                                                                                                                let pred : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__242
                                                                                                                                    27
                                                                                                                                    24)
                                                                                                                                let mapping78_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__242
                                                                                                                                    11
                                                                                                                                    7)
                                                                                                                                let mapping77_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__242
                                                                                                                                    19
                                                                                                                                    15)
                                                                                                                                let fm : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__242
                                                                                                                                    31
                                                                                                                                    28)
                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                    mapping77_)), (← (encdec_reg_backwards
                                                                                                                                    mapping78_))) with
                                                                                                                                | (rs, rd) =>
                                                                                                                                  (pure (some
                                                                                                                                      (FENCE
                                                                                                                                        (fm, pred, succ, rs, rd)))))
                                                                                                                            else
                                                                                                                              (pure none))) with
                                                                                                                      | .some result =>
                                                                                                                        (pure result)
                                                                                                                      | none =>
                                                                                                                        (do
                                                                                                                          match (← do
                                                                                                                            let v__205 :=
                                                                                                                              head_exp_
                                                                                                                            if ((v__205 == (0x00000073#32 : (BitVec 32))) : Bool)
                                                                                                                            then
                                                                                                                              (pure (some
                                                                                                                                  (ECALL
                                                                                                                                    ())))
                                                                                                                            else
                                                                                                                              (do
                                                                                                                                if ((v__205 == (0x30200073#32 : (BitVec 32))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      (MRET
                                                                                                                                        ())))
                                                                                                                                else
                                                                                                                                  (do
                                                                                                                                    if ((v__205 == (0x10200073#32 : (BitVec 32))) : Bool)
                                                                                                                                    then
                                                                                                                                      (pure (some
                                                                                                                                          (SRET
                                                                                                                                            ())))
                                                                                                                                    else
                                                                                                                                      (do
                                                                                                                                        if ((v__205 == (0x00100073#32 : (BitVec 32))) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              (EBREAK
                                                                                                                                                ())))
                                                                                                                                        else
                                                                                                                                          (do
                                                                                                                                            if ((v__205 == (0x10500073#32 : (BitVec 32))) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  (WFI
                                                                                                                                                    ())))
                                                                                                                                            else
                                                                                                                                              (do
                                                                                                                                                if (((let mapping80_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__205
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping79_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__205
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping79_) && (encdec_reg_backwards_matches
                                                                                                                                                         mapping80_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__205
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0001001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                                           v__205
                                                                                                                                                           14
                                                                                                                                                           0) == (0b000000001110011#15 : (BitVec 15))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping80_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__205
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping79_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__205
                                                                                                                                                        24
                                                                                                                                                        20)
                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                        mapping79_)), (← (encdec_reg_backwards
                                                                                                                                                        mapping80_))) with
                                                                                                                                                    | (rs2, rs1) =>
                                                                                                                                                      (do
                                                                                                                                                        if (((← (virtual_memory_supported
                                                                                                                                                                 ())) || (not
                                                                                                                                                               (true : Bool))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (pure (some
                                                                                                                                                              (SFENCE_VMA
                                                                                                                                                                (rs1, rs2))))
                                                                                                                                                        else
                                                                                                                                                          (pure none)))
                                                                                                                                                else
                                                                                                                                                  (pure none))))))) with
                                                                                                                          | .some result =>
                                                                                                                            (pure result)
                                                                                                                          | none =>
                                                                                                                            (do
                                                                                                                              match (← do
                                                                                                                                let v__202 :=
                                                                                                                                  head_exp_
                                                                                                                                if (((let mapping84_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__202
                                                                                                                                         11
                                                                                                                                         7)
                                                                                                                                     let mapping83_ : (BitVec 3) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__202
                                                                                                                                         14
                                                                                                                                         12)
                                                                                                                                     let mapping82_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__202
                                                                                                                                         19
                                                                                                                                         15)
                                                                                                                                     let mapping81_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__202
                                                                                                                                         24
                                                                                                                                         20)
                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                         mapping81_) && ((encdec_reg_backwards_matches
                                                                                                                                           mapping82_) && ((encdec_mul_op_backwards_matches
                                                                                                                                             mapping83_) && (encdec_reg_backwards_matches
                                                                                                                                             mapping84_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                           v__202
                                                                                                                                           31
                                                                                                                                           25) == (0b0000001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                           v__202
                                                                                                                                           6
                                                                                                                                           0) == (0b0110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let mapping84_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__202
                                                                                                                                        11
                                                                                                                                        7)
                                                                                                                                    let mapping83_ : (BitVec 3) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__202
                                                                                                                                        14
                                                                                                                                        12)
                                                                                                                                    let mapping82_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__202
                                                                                                                                        19
                                                                                                                                        15)
                                                                                                                                    let mapping81_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__202
                                                                                                                                        24
                                                                                                                                        20)
                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                        mapping81_)), (← (encdec_reg_backwards
                                                                                                                                        mapping82_)), (← (encdec_mul_op_backwards
                                                                                                                                        mapping83_)), (← (encdec_reg_backwards
                                                                                                                                        mapping84_))) with
                                                                                                                                    | (rs2, rs1, mul_op, rd) =>
                                                                                                                                      (do
                                                                                                                                        if (((← (currentlyEnabled
                                                                                                                                                 Ext_M)) || (← (currentlyEnabled
                                                                                                                                                 Ext_Zmmul))) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              (MUL
                                                                                                                                                (rs2, rs1, rd, mul_op))))
                                                                                                                                        else
                                                                                                                                          (pure none)))
                                                                                                                                else
                                                                                                                                  (pure none)) with
                                                                                                                              | .some result =>
                                                                                                                                (pure result)
                                                                                                                              | none =>
                                                                                                                                (do
                                                                                                                                  match (← do
                                                                                                                                    let v__198 :=
                                                                                                                                      head_exp_
                                                                                                                                    if (((let mapping88_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__198
                                                                                                                                             11
                                                                                                                                             7)
                                                                                                                                         let mapping87_ : (BitVec 1) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__198
                                                                                                                                             12
                                                                                                                                             12)
                                                                                                                                         let mapping86_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__198
                                                                                                                                             19
                                                                                                                                             15)
                                                                                                                                         let mapping85_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__198
                                                                                                                                             24
                                                                                                                                             20)
                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                             mapping85_) && ((encdec_reg_backwards_matches
                                                                                                                                               mapping86_) && ((bool_bit_backwards_matches
                                                                                                                                                 mapping87_) && (encdec_reg_backwards_matches
                                                                                                                                                 mapping88_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                               v__198
                                                                                                                                               31
                                                                                                                                               25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                 v__198
                                                                                                                                                 14
                                                                                                                                                 13) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                 v__198
                                                                                                                                                 6
                                                                                                                                                 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let mapping88_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__198
                                                                                                                                            11
                                                                                                                                            7)
                                                                                                                                        let mapping87_ : (BitVec 1) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__198
                                                                                                                                            12
                                                                                                                                            12)
                                                                                                                                        let mapping86_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__198
                                                                                                                                            19
                                                                                                                                            15)
                                                                                                                                        let mapping85_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__198
                                                                                                                                            24
                                                                                                                                            20)
                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                            mapping85_)), (← (encdec_reg_backwards
                                                                                                                                            mapping86_)), (bool_bit_backwards
                                                                                                                                          mapping87_), (← (encdec_reg_backwards
                                                                                                                                            mapping88_))) with
                                                                                                                                        | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                          (do
                                                                                                                                            if ((← (currentlyEnabled
                                                                                                                                                   Ext_M)) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  (DIV
                                                                                                                                                    (rs2, rs1, rd, is_unsigned))))
                                                                                                                                            else
                                                                                                                                              (pure none)))
                                                                                                                                    else
                                                                                                                                      (pure none)) with
                                                                                                                                  | .some result =>
                                                                                                                                    (pure result)
                                                                                                                                  | none =>
                                                                                                                                    (do
                                                                                                                                      match (← do
                                                                                                                                        let v__194 :=
                                                                                                                                          head_exp_
                                                                                                                                        if (((let mapping92_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__194
                                                                                                                                                 11
                                                                                                                                                 7)
                                                                                                                                             let mapping91_ : (BitVec 1) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__194
                                                                                                                                                 12
                                                                                                                                                 12)
                                                                                                                                             let mapping90_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__194
                                                                                                                                                 19
                                                                                                                                                 15)
                                                                                                                                             let mapping89_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__194
                                                                                                                                                 24
                                                                                                                                                 20)
                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                 mapping89_) && ((encdec_reg_backwards_matches
                                                                                                                                                   mapping90_) && ((bool_bit_backwards_matches
                                                                                                                                                     mapping91_) && (encdec_reg_backwards_matches
                                                                                                                                                     mapping92_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                   v__194
                                                                                                                                                   31
                                                                                                                                                   25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                     v__194
                                                                                                                                                     14
                                                                                                                                                     13) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                     v__194
                                                                                                                                                     6
                                                                                                                                                     0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let mapping92_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__194
                                                                                                                                                11
                                                                                                                                                7)
                                                                                                                                            let mapping91_ : (BitVec 1) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__194
                                                                                                                                                12
                                                                                                                                                12)
                                                                                                                                            let mapping90_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__194
                                                                                                                                                19
                                                                                                                                                15)
                                                                                                                                            let mapping89_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__194
                                                                                                                                                24
                                                                                                                                                20)
                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                mapping89_)), (← (encdec_reg_backwards
                                                                                                                                                mapping90_)), (bool_bit_backwards
                                                                                                                                              mapping91_), (← (encdec_reg_backwards
                                                                                                                                                mapping92_))) with
                                                                                                                                            | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                              (do
                                                                                                                                                if ((← (currentlyEnabled
                                                                                                                                                       Ext_M)) : Bool)
                                                                                                                                                then
                                                                                                                                                  (pure (some
                                                                                                                                                      (REM
                                                                                                                                                        (rs2, rs1, rd, is_unsigned))))
                                                                                                                                                else
                                                                                                                                                  (pure none)))
                                                                                                                                        else
                                                                                                                                          (pure none)) with
                                                                                                                                      | .some result =>
                                                                                                                                        (pure result)
                                                                                                                                      | none =>
                                                                                                                                        (do
                                                                                                                                          match (← do
                                                                                                                                            let v__190 :=
                                                                                                                                              head_exp_
                                                                                                                                            if (((let mapping95_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__190
                                                                                                                                                     11
                                                                                                                                                     7)
                                                                                                                                                 let mapping94_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__190
                                                                                                                                                     19
                                                                                                                                                     15)
                                                                                                                                                 let mapping93_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__190
                                                                                                                                                     24
                                                                                                                                                     20)
                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                     mapping93_) && ((encdec_reg_backwards_matches
                                                                                                                                                       mapping94_) && (encdec_reg_backwards_matches
                                                                                                                                                       mapping95_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                       v__190
                                                                                                                                                       31
                                                                                                                                                       25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                         v__190
                                                                                                                                                         14
                                                                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                         v__190
                                                                                                                                                         6
                                                                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let mapping95_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__190
                                                                                                                                                    11
                                                                                                                                                    7)
                                                                                                                                                let mapping94_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__190
                                                                                                                                                    19
                                                                                                                                                    15)
                                                                                                                                                let mapping93_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__190
                                                                                                                                                    24
                                                                                                                                                    20)
                                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                                    mapping93_)), (← (encdec_reg_backwards
                                                                                                                                                    mapping94_)), (← (encdec_reg_backwards
                                                                                                                                                    mapping95_))) with
                                                                                                                                                | (rs2, rs1, rd) =>
                                                                                                                                                  (do
                                                                                                                                                    if (((xlen == 64) && ((← (currentlyEnabled
                                                                                                                                                               Ext_M)) || (← (currentlyEnabled
                                                                                                                                                               Ext_Zmmul)))) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (pure (some
                                                                                                                                                          (MULW
                                                                                                                                                            (rs2, rs1, rd))))
                                                                                                                                                    else
                                                                                                                                                      (pure none)))
                                                                                                                                            else
                                                                                                                                              (pure none)) with
                                                                                                                                          | .some result =>
                                                                                                                                            (pure result)
                                                                                                                                          | none =>
                                                                                                                                            (do
                                                                                                                                              match (← do
                                                                                                                                                let v__186 :=
                                                                                                                                                  head_exp_
                                                                                                                                                if (((let mapping99_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__186
                                                                                                                                                         11
                                                                                                                                                         7)
                                                                                                                                                     let mapping98_ : (BitVec 1) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__186
                                                                                                                                                         12
                                                                                                                                                         12)
                                                                                                                                                     let mapping97_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__186
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping96_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__186
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping96_) && ((encdec_reg_backwards_matches
                                                                                                                                                           mapping97_) && ((bool_bit_backwards_matches
                                                                                                                                                             mapping98_) && (encdec_reg_backwards_matches
                                                                                                                                                             mapping99_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__186
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                             v__186
                                                                                                                                                             14
                                                                                                                                                             13) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                             v__186
                                                                                                                                                             6
                                                                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping99_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__186
                                                                                                                                                        11
                                                                                                                                                        7)
                                                                                                                                                    let mapping98_ : (BitVec 1) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__186
                                                                                                                                                        12
                                                                                                                                                        12)
                                                                                                                                                    let mapping97_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__186
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping96_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__186
                                                                                                                                                        24
                                                                                                                                                        20)
                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                        mapping96_)), (← (encdec_reg_backwards
                                                                                                                                                        mapping97_)), (bool_bit_backwards
                                                                                                                                                      mapping98_), (← (encdec_reg_backwards
                                                                                                                                                        mapping99_))) with
                                                                                                                                                    | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                      (do
                                                                                                                                                        if (((xlen == 64) && (← (currentlyEnabled
                                                                                                                                                                 Ext_M))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (pure (some
                                                                                                                                                              (DIVW
                                                                                                                                                                (rs2, rs1, rd, is_unsigned))))
                                                                                                                                                        else
                                                                                                                                                          (pure none)))
                                                                                                                                                else
                                                                                                                                                  (pure none)) with
                                                                                                                                              | .some result =>
                                                                                                                                                (pure result)
                                                                                                                                              | none =>
                                                                                                                                                (do
                                                                                                                                                  match (← do
                                                                                                                                                    let v__182 :=
                                                                                                                                                      head_exp_
                                                                                                                                                    if (((let mapping103_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__182
                                                                                                                                                             11
                                                                                                                                                             7)
                                                                                                                                                         let mapping102_ : (BitVec 1) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__182
                                                                                                                                                             12
                                                                                                                                                             12)
                                                                                                                                                         let mapping101_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__182
                                                                                                                                                             19
                                                                                                                                                             15)
                                                                                                                                                         let mapping100_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__182
                                                                                                                                                             24
                                                                                                                                                             20)
                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                             mapping100_) && ((encdec_reg_backwards_matches
                                                                                                                                                               mapping101_) && ((bool_bit_backwards_matches
                                                                                                                                                                 mapping102_) && (encdec_reg_backwards_matches
                                                                                                                                                                 mapping103_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                               v__182
                                                                                                                                                               31
                                                                                                                                                               25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                 v__182
                                                                                                                                                                 14
                                                                                                                                                                 13) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                 v__182
                                                                                                                                                                 6
                                                                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let mapping103_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__182
                                                                                                                                                            11
                                                                                                                                                            7)
                                                                                                                                                        let mapping102_ : (BitVec 1) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__182
                                                                                                                                                            12
                                                                                                                                                            12)
                                                                                                                                                        let mapping101_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__182
                                                                                                                                                            19
                                                                                                                                                            15)
                                                                                                                                                        let mapping100_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__182
                                                                                                                                                            24
                                                                                                                                                            20)
                                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                                            mapping100_)), (← (encdec_reg_backwards
                                                                                                                                                            mapping101_)), (bool_bit_backwards
                                                                                                                                                          mapping102_), (← (encdec_reg_backwards
                                                                                                                                                            mapping103_))) with
                                                                                                                                                        | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                          (do
                                                                                                                                                            if (((xlen == 64) && (← (currentlyEnabled
                                                                                                                                                                     Ext_M))) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (pure (some
                                                                                                                                                                  (REMW
                                                                                                                                                                    (rs2, rs1, rd, is_unsigned))))
                                                                                                                                                            else
                                                                                                                                                              (pure none)))
                                                                                                                                                    else
                                                                                                                                                      (pure none)) with
                                                                                                                                                  | .some result =>
                                                                                                                                                    (pure result)
                                                                                                                                                  | none =>
                                                                                                                                                    (do
                                                                                                                                                      match (← do
                                                                                                                                                        let v__178 :=
                                                                                                                                                          head_exp_
                                                                                                                                                        if (((let mapping105_ : (BitVec 5) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__178
                                                                                                                                                                 11
                                                                                                                                                                 7)
                                                                                                                                                             let mapping104_ : (BitVec 5) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__178
                                                                                                                                                                 19
                                                                                                                                                                 15)
                                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                                 mapping104_) && (encdec_reg_backwards_matches
                                                                                                                                                                 mapping105_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                   v__178
                                                                                                                                                                   31
                                                                                                                                                                   25) == (0b0110000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                     v__178
                                                                                                                                                                     14
                                                                                                                                                                     12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                     v__178
                                                                                                                                                                     6
                                                                                                                                                                     0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let shamt : (BitVec 5) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__178
                                                                                                                                                                24
                                                                                                                                                                20)
                                                                                                                                                            let mapping105_ : (BitVec 5) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__178
                                                                                                                                                                11
                                                                                                                                                                7)
                                                                                                                                                            let mapping104_ : (BitVec 5) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__178
                                                                                                                                                                19
                                                                                                                                                                15)
                                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                                mapping104_)), (← (encdec_reg_backwards
                                                                                                                                                                mapping105_))) with
                                                                                                                                                            | (rs1, rd) =>
                                                                                                                                                              (do
                                                                                                                                                                if ((((← (currentlyEnabled
                                                                                                                                                                           Ext_Zbb)) || (← (currentlyEnabled
                                                                                                                                                                           Ext_Zbkb))) && (xlen == 64)) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (pure (some
                                                                                                                                                                      (RORIW
                                                                                                                                                                        (shamt, rs1, rd))))
                                                                                                                                                                else
                                                                                                                                                                  (pure none)))
                                                                                                                                                        else
                                                                                                                                                          (pure none)) with
                                                                                                                                                      | .some result =>
                                                                                                                                                        (pure result)
                                                                                                                                                      | none =>
                                                                                                                                                        (do
                                                                                                                                                          match (← do
                                                                                                                                                            let v__174 :=
                                                                                                                                                              head_exp_
                                                                                                                                                            if (((let mapping107_ : (BitVec 5) :=
                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                     v__174
                                                                                                                                                                     11
                                                                                                                                                                     7)
                                                                                                                                                                 let mapping106_ : (BitVec 5) :=
                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                     v__174
                                                                                                                                                                     19
                                                                                                                                                                     15)
                                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                                     mapping106_) && (encdec_reg_backwards_matches
                                                                                                                                                                     mapping107_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                       v__174
                                                                                                                                                                       31
                                                                                                                                                                       26) == (0b011000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                         v__174
                                                                                                                                                                         14
                                                                                                                                                                         12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                         v__174
                                                                                                                                                                         6
                                                                                                                                                                         0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let shamt : (BitVec 6) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__174
                                                                                                                                                                    25
                                                                                                                                                                    20)
                                                                                                                                                                let mapping107_ : (BitVec 5) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__174
                                                                                                                                                                    11
                                                                                                                                                                    7)
                                                                                                                                                                let mapping106_ : (BitVec 5) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__174
                                                                                                                                                                    19
                                                                                                                                                                    15)
                                                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                                                    mapping106_)), (← (encdec_reg_backwards
                                                                                                                                                                    mapping107_))) with
                                                                                                                                                                | (rs1, rd) =>
                                                                                                                                                                  (do
                                                                                                                                                                    if ((((← (currentlyEnabled
                                                                                                                                                                               Ext_Zbb)) || (← (currentlyEnabled
                                                                                                                                                                               Ext_Zbkb))) && ((xlen == 64) || ((BitVec.access
                                                                                                                                                                               shamt
                                                                                                                                                                               5) == 0#1))) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (pure (some
                                                                                                                                                                          (RORI
                                                                                                                                                                            (shamt, rs1, rd))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure none)))
                                                                                                                                                            else
                                                                                                                                                              (pure none)) with
                                                                                                                                                          | .some result =>
                                                                                                                                                            (pure result)
                                                                                                                                                          | none =>
                                                                                                                                                            (do
                                                                                                                                                              match (← do
                                                                                                                                                                let v__170 :=
                                                                                                                                                                  head_exp_
                                                                                                                                                                if (((let mapping110_ : (BitVec 5) :=
                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                         v__170
                                                                                                                                                                         11
                                                                                                                                                                         7)
                                                                                                                                                                     let mapping109_ : (BitVec 5) :=
                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                         v__170
                                                                                                                                                                         19
                                                                                                                                                                         15)
                                                                                                                                                                     let mapping108_ : (BitVec 5) :=
                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                         v__170
                                                                                                                                                                         24
                                                                                                                                                                         20)
                                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                                         mapping108_) && ((encdec_reg_backwards_matches
                                                                                                                                                                           mapping109_) && (encdec_reg_backwards_matches
                                                                                                                                                                           mapping110_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                           v__170
                                                                                                                                                                           31
                                                                                                                                                                           25) == (0b0110000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                             v__170
                                                                                                                                                                             14
                                                                                                                                                                             12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                             v__170
                                                                                                                                                                             6
                                                                                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let mapping110_ : (BitVec 5) :=
                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                        v__170
                                                                                                                                                                        11
                                                                                                                                                                        7)
                                                                                                                                                                    let mapping109_ : (BitVec 5) :=
                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                        v__170
                                                                                                                                                                        19
                                                                                                                                                                        15)
                                                                                                                                                                    let mapping108_ : (BitVec 5) :=
                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                        v__170
                                                                                                                                                                        24
                                                                                                                                                                        20)
                                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                                        mapping108_)), (← (encdec_reg_backwards
                                                                                                                                                                        mapping109_)), (← (encdec_reg_backwards
                                                                                                                                                                        mapping110_))) with
                                                                                                                                                                    | (rs2, rs1, rd) =>
                                                                                                                                                                      (do
                                                                                                                                                                        if ((((← (currentlyEnabled
                                                                                                                                                                                   Ext_Zbb)) || (← (currentlyEnabled
                                                                                                                                                                                   Ext_Zbkb))) && (xlen == 64)) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (pure (some
                                                                                                                                                                              (ZBB_RTYPEW
                                                                                                                                                                                (rs2, rs1, rd, ROLW))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure none)))
                                                                                                                                                                else
                                                                                                                                                                  (pure none)) with
                                                                                                                                                              | .some result =>
                                                                                                                                                                (pure result)
                                                                                                                                                              | none =>
                                                                                                                                                                (do
                                                                                                                                                                  match (← do
                                                                                                                                                                    let v__166 :=
                                                                                                                                                                      head_exp_
                                                                                                                                                                    if (((let mapping113_ : (BitVec 5) :=
                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                             v__166
                                                                                                                                                                             11
                                                                                                                                                                             7)
                                                                                                                                                                         let mapping112_ : (BitVec 5) :=
                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                             v__166
                                                                                                                                                                             19
                                                                                                                                                                             15)
                                                                                                                                                                         let mapping111_ : (BitVec 5) :=
                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                             v__166
                                                                                                                                                                             24
                                                                                                                                                                             20)
                                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                                             mapping111_) && ((encdec_reg_backwards_matches
                                                                                                                                                                               mapping112_) && (encdec_reg_backwards_matches
                                                                                                                                                                               mapping113_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                               v__166
                                                                                                                                                                               31
                                                                                                                                                                               25) == (0b0110000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                 v__166
                                                                                                                                                                                 14
                                                                                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                 v__166
                                                                                                                                                                                 6
                                                                                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let mapping113_ : (BitVec 5) :=
                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                            v__166
                                                                                                                                                                            11
                                                                                                                                                                            7)
                                                                                                                                                                        let mapping112_ : (BitVec 5) :=
                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                            v__166
                                                                                                                                                                            19
                                                                                                                                                                            15)
                                                                                                                                                                        let mapping111_ : (BitVec 5) :=
                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                            v__166
                                                                                                                                                                            24
                                                                                                                                                                            20)
                                                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                                                            mapping111_)), (← (encdec_reg_backwards
                                                                                                                                                                            mapping112_)), (← (encdec_reg_backwards
                                                                                                                                                                            mapping113_))) with
                                                                                                                                                                        | (rs2, rs1, rd) =>
                                                                                                                                                                          (do
                                                                                                                                                                            if ((((← (currentlyEnabled
                                                                                                                                                                                       Ext_Zbb)) || (← (currentlyEnabled
                                                                                                                                                                                       Ext_Zbkb))) && (xlen == 64)) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (pure (some
                                                                                                                                                                                  (ZBB_RTYPEW
                                                                                                                                                                                    (rs2, rs1, rd, RORW))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure none)))
                                                                                                                                                                    else
                                                                                                                                                                      (pure none)) with
                                                                                                                                                                  | .some result =>
                                                                                                                                                                    (pure result)
                                                                                                                                                                  | none =>
                                                                                                                                                                    (do
                                                                                                                                                                      match (← do
                                                                                                                                                                        let v__162 :=
                                                                                                                                                                          head_exp_
                                                                                                                                                                        if (((let mapping116_ : (BitVec 5) :=
                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                 v__162
                                                                                                                                                                                 11
                                                                                                                                                                                 7)
                                                                                                                                                                             let mapping115_ : (BitVec 5) :=
                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                 v__162
                                                                                                                                                                                 19
                                                                                                                                                                                 15)
                                                                                                                                                                             let mapping114_ : (BitVec 5) :=
                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                 v__162
                                                                                                                                                                                 24
                                                                                                                                                                                 20)
                                                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                                                 mapping114_) && ((encdec_reg_backwards_matches
                                                                                                                                                                                   mapping115_) && (encdec_reg_backwards_matches
                                                                                                                                                                                   mapping116_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                   v__162
                                                                                                                                                                                   31
                                                                                                                                                                                   25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                     v__162
                                                                                                                                                                                     14
                                                                                                                                                                                     12) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                     v__162
                                                                                                                                                                                     6
                                                                                                                                                                                     0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let mapping116_ : (BitVec 5) :=
                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                v__162
                                                                                                                                                                                11
                                                                                                                                                                                7)
                                                                                                                                                                            let mapping115_ : (BitVec 5) :=
                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                v__162
                                                                                                                                                                                19
                                                                                                                                                                                15)
                                                                                                                                                                            let mapping114_ : (BitVec 5) :=
                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                v__162
                                                                                                                                                                                24
                                                                                                                                                                                20)
                                                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                                                mapping114_)), (← (encdec_reg_backwards
                                                                                                                                                                                mapping115_)), (← (encdec_reg_backwards
                                                                                                                                                                                mapping116_))) with
                                                                                                                                                                            | (rs2, rs1, rd) =>
                                                                                                                                                                              (do
                                                                                                                                                                                if (((← (currentlyEnabled
                                                                                                                                                                                         Ext_Zbb)) || (← (currentlyEnabled
                                                                                                                                                                                         Ext_Zbkb))) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (pure (some
                                                                                                                                                                                      (ZBB_RTYPE
                                                                                                                                                                                        (rs2, rs1, rd, ANDN))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure none)))
                                                                                                                                                                        else
                                                                                                                                                                          (pure none)) with
                                                                                                                                                                      | .some result =>
                                                                                                                                                                        (pure result)
                                                                                                                                                                      | none =>
                                                                                                                                                                        (do
                                                                                                                                                                          match (← do
                                                                                                                                                                            let v__158 :=
                                                                                                                                                                              head_exp_
                                                                                                                                                                            if (((let mapping119_ : (BitVec 5) :=
                                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                                     v__158
                                                                                                                                                                                     11
                                                                                                                                                                                     7)
                                                                                                                                                                                 let mapping118_ : (BitVec 5) :=
                                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                                     v__158
                                                                                                                                                                                     19
                                                                                                                                                                                     15)
                                                                                                                                                                                 let mapping117_ : (BitVec 5) :=
                                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                                     v__158
                                                                                                                                                                                     24
                                                                                                                                                                                     20)
                                                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                                                     mapping117_) && ((encdec_reg_backwards_matches
                                                                                                                                                                                       mapping118_) && (encdec_reg_backwards_matches
                                                                                                                                                                                       mapping119_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                       v__158
                                                                                                                                                                                       31
                                                                                                                                                                                       25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                         v__158
                                                                                                                                                                                         14
                                                                                                                                                                                         12) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                         v__158
                                                                                                                                                                                         6
                                                                                                                                                                                         0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let mapping119_ : (BitVec 5) :=
                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                    v__158
                                                                                                                                                                                    11
                                                                                                                                                                                    7)
                                                                                                                                                                                let mapping118_ : (BitVec 5) :=
                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                    v__158
                                                                                                                                                                                    19
                                                                                                                                                                                    15)
                                                                                                                                                                                let mapping117_ : (BitVec 5) :=
                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                    v__158
                                                                                                                                                                                    24
                                                                                                                                                                                    20)
                                                                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                                                                    mapping117_)), (← (encdec_reg_backwards
                                                                                                                                                                                    mapping118_)), (← (encdec_reg_backwards
                                                                                                                                                                                    mapping119_))) with
                                                                                                                                                                                | (rs2, rs1, rd) =>
                                                                                                                                                                                  (do
                                                                                                                                                                                    if (((← (currentlyEnabled
                                                                                                                                                                                             Ext_Zbb)) || (← (currentlyEnabled
                                                                                                                                                                                             Ext_Zbkb))) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (pure (some
                                                                                                                                                                                          (ZBB_RTYPE
                                                                                                                                                                                            (rs2, rs1, rd, ORN))))
                                                                                                                                                                                    else
                                                                                                                                                                                      (pure none)))
                                                                                                                                                                            else
                                                                                                                                                                              (pure none)) with
                                                                                                                                                                          | .some result =>
                                                                                                                                                                            (pure result)
                                                                                                                                                                          | none =>
                                                                                                                                                                            (do
                                                                                                                                                                              match (← do
                                                                                                                                                                                let v__154 :=
                                                                                                                                                                                  head_exp_
                                                                                                                                                                                if (((let mapping122_ : (BitVec 5) :=
                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                         v__154
                                                                                                                                                                                         11
                                                                                                                                                                                         7)
                                                                                                                                                                                     let mapping121_ : (BitVec 5) :=
                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                         v__154
                                                                                                                                                                                         19
                                                                                                                                                                                         15)
                                                                                                                                                                                     let mapping120_ : (BitVec 5) :=
                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                         v__154
                                                                                                                                                                                         24
                                                                                                                                                                                         20)
                                                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                                                         mapping120_) && ((encdec_reg_backwards_matches
                                                                                                                                                                                           mapping121_) && (encdec_reg_backwards_matches
                                                                                                                                                                                           mapping122_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                           v__154
                                                                                                                                                                                           31
                                                                                                                                                                                           25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                             v__154
                                                                                                                                                                                             14
                                                                                                                                                                                             12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                             v__154
                                                                                                                                                                                             6
                                                                                                                                                                                             0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let mapping122_ : (BitVec 5) :=
                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                        v__154
                                                                                                                                                                                        11
                                                                                                                                                                                        7)
                                                                                                                                                                                    let mapping121_ : (BitVec 5) :=
                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                        v__154
                                                                                                                                                                                        19
                                                                                                                                                                                        15)
                                                                                                                                                                                    let mapping120_ : (BitVec 5) :=
                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                        v__154
                                                                                                                                                                                        24
                                                                                                                                                                                        20)
                                                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                                                        mapping120_)), (← (encdec_reg_backwards
                                                                                                                                                                                        mapping121_)), (← (encdec_reg_backwards
                                                                                                                                                                                        mapping122_))) with
                                                                                                                                                                                    | (rs2, rs1, rd) =>
                                                                                                                                                                                      (do
                                                                                                                                                                                        if (((← (currentlyEnabled
                                                                                                                                                                                                 Ext_Zbb)) || (← (currentlyEnabled
                                                                                                                                                                                                 Ext_Zbkb))) : Bool)
                                                                                                                                                                                        then
                                                                                                                                                                                          (pure (some
                                                                                                                                                                                              (ZBB_RTYPE
                                                                                                                                                                                                (rs2, rs1, rd, XNOR))))
                                                                                                                                                                                        else
                                                                                                                                                                                          (pure none)))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure none)) with
                                                                                                                                                                              | .some result =>
                                                                                                                                                                                (pure result)
                                                                                                                                                                              | none =>
                                                                                                                                                                                (do
                                                                                                                                                                                  match (← do
                                                                                                                                                                                    let v__150 :=
                                                                                                                                                                                      head_exp_
                                                                                                                                                                                    if (((let mapping125_ : (BitVec 5) :=
                                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                                             v__150
                                                                                                                                                                                             11
                                                                                                                                                                                             7)
                                                                                                                                                                                         let mapping124_ : (BitVec 5) :=
                                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                                             v__150
                                                                                                                                                                                             19
                                                                                                                                                                                             15)
                                                                                                                                                                                         let mapping123_ : (BitVec 5) :=
                                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                                             v__150
                                                                                                                                                                                             24
                                                                                                                                                                                             20)
                                                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                                                             mapping123_) && ((encdec_reg_backwards_matches
                                                                                                                                                                                               mapping124_) && (encdec_reg_backwards_matches
                                                                                                                                                                                               mapping125_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                               v__150
                                                                                                                                                                                               31
                                                                                                                                                                                               25) == (0b0000101#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                 v__150
                                                                                                                                                                                                 14
                                                                                                                                                                                                 12) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                 v__150
                                                                                                                                                                                                 6
                                                                                                                                                                                                 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (do
                                                                                                                                                                                        let mapping125_ : (BitVec 5) :=
                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                            v__150
                                                                                                                                                                                            11
                                                                                                                                                                                            7)
                                                                                                                                                                                        let mapping124_ : (BitVec 5) :=
                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                            v__150
                                                                                                                                                                                            19
                                                                                                                                                                                            15)
                                                                                                                                                                                        let mapping123_ : (BitVec 5) :=
                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                            v__150
                                                                                                                                                                                            24
                                                                                                                                                                                            20)
                                                                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                                                                            mapping123_)), (← (encdec_reg_backwards
                                                                                                                                                                                            mapping124_)), (← (encdec_reg_backwards
                                                                                                                                                                                            mapping125_))) with
                                                                                                                                                                                        | (rs2, rs1, rd) =>
                                                                                                                                                                                          (do
                                                                                                                                                                                            if ((← (currentlyEnabled
                                                                                                                                                                                                   Ext_Zbb)) : Bool)
                                                                                                                                                                                            then
                                                                                                                                                                                              (pure (some
                                                                                                                                                                                                  (ZBB_RTYPE
                                                                                                                                                                                                    (rs2, rs1, rd, MAX))))
                                                                                                                                                                                            else
                                                                                                                                                                                              (pure none)))
                                                                                                                                                                                    else
                                                                                                                                                                                      (pure none)) with
                                                                                                                                                                                  | .some result =>
                                                                                                                                                                                    (pure result)
                                                                                                                                                                                  | none =>
                                                                                                                                                                                    (do
                                                                                                                                                                                      match (← do
                                                                                                                                                                                        let v__146 :=
                                                                                                                                                                                          head_exp_
                                                                                                                                                                                        if (((let mapping128_ : (BitVec 5) :=
                                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                                 v__146
                                                                                                                                                                                                 11
                                                                                                                                                                                                 7)
                                                                                                                                                                                             let mapping127_ : (BitVec 5) :=
                                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                                 v__146
                                                                                                                                                                                                 19
                                                                                                                                                                                                 15)
                                                                                                                                                                                             let mapping126_ : (BitVec 5) :=
                                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                                 v__146
                                                                                                                                                                                                 24
                                                                                                                                                                                                 20)
                                                                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                                                                 mapping126_) && ((encdec_reg_backwards_matches
                                                                                                                                                                                                   mapping127_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                   mapping128_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                   v__146
                                                                                                                                                                                                   31
                                                                                                                                                                                                   25) == (0b0000101#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                     v__146
                                                                                                                                                                                                     14
                                                                                                                                                                                                     12) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                     v__146
                                                                                                                                                                                                     6
                                                                                                                                                                                                     0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                        then
                                                                                                                                                                                          (do
                                                                                                                                                                                            let mapping128_ : (BitVec 5) :=
                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                v__146
                                                                                                                                                                                                11
                                                                                                                                                                                                7)
                                                                                                                                                                                            let mapping127_ : (BitVec 5) :=
                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                v__146
                                                                                                                                                                                                19
                                                                                                                                                                                                15)
                                                                                                                                                                                            let mapping126_ : (BitVec 5) :=
                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                v__146
                                                                                                                                                                                                24
                                                                                                                                                                                                20)
                                                                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                                                                mapping126_)), (← (encdec_reg_backwards
                                                                                                                                                                                                mapping127_)), (← (encdec_reg_backwards
                                                                                                                                                                                                mapping128_))) with
                                                                                                                                                                                            | (rs2, rs1, rd) =>
                                                                                                                                                                                              (do
                                                                                                                                                                                                if ((← (currentlyEnabled
                                                                                                                                                                                                       Ext_Zbb)) : Bool)
                                                                                                                                                                                                then
                                                                                                                                                                                                  (pure (some
                                                                                                                                                                                                      (ZBB_RTYPE
                                                                                                                                                                                                        (rs2, rs1, rd, MAXU))))
                                                                                                                                                                                                else
                                                                                                                                                                                                  (pure none)))
                                                                                                                                                                                        else
                                                                                                                                                                                          (pure none)) with
                                                                                                                                                                                      | .some result =>
                                                                                                                                                                                        (pure result)
                                                                                                                                                                                      | none =>
                                                                                                                                                                                        (do
                                                                                                                                                                                          match (← do
                                                                                                                                                                                            let v__142 :=
                                                                                                                                                                                              head_exp_
                                                                                                                                                                                            if (((let mapping131_ : (BitVec 5) :=
                                                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                                                     v__142
                                                                                                                                                                                                     11
                                                                                                                                                                                                     7)
                                                                                                                                                                                                 let mapping130_ : (BitVec 5) :=
                                                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                                                     v__142
                                                                                                                                                                                                     19
                                                                                                                                                                                                     15)
                                                                                                                                                                                                 let mapping129_ : (BitVec 5) :=
                                                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                                                     v__142
                                                                                                                                                                                                     24
                                                                                                                                                                                                     20)
                                                                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                                                                     mapping129_) && ((encdec_reg_backwards_matches
                                                                                                                                                                                                       mapping130_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                       mapping131_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                       v__142
                                                                                                                                                                                                       31
                                                                                                                                                                                                       25) == (0b0000101#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                         v__142
                                                                                                                                                                                                         14
                                                                                                                                                                                                         12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                         v__142
                                                                                                                                                                                                         6
                                                                                                                                                                                                         0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                            then
                                                                                                                                                                                              (do
                                                                                                                                                                                                let mapping131_ : (BitVec 5) :=
                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                    v__142
                                                                                                                                                                                                    11
                                                                                                                                                                                                    7)
                                                                                                                                                                                                let mapping130_ : (BitVec 5) :=
                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                    v__142
                                                                                                                                                                                                    19
                                                                                                                                                                                                    15)
                                                                                                                                                                                                let mapping129_ : (BitVec 5) :=
                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                    v__142
                                                                                                                                                                                                    24
                                                                                                                                                                                                    20)
                                                                                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                                                                                    mapping129_)), (← (encdec_reg_backwards
                                                                                                                                                                                                    mapping130_)), (← (encdec_reg_backwards
                                                                                                                                                                                                    mapping131_))) with
                                                                                                                                                                                                | (rs2, rs1, rd) =>
                                                                                                                                                                                                  (do
                                                                                                                                                                                                    if ((← (currentlyEnabled
                                                                                                                                                                                                           Ext_Zbb)) : Bool)
                                                                                                                                                                                                    then
                                                                                                                                                                                                      (pure (some
                                                                                                                                                                                                          (ZBB_RTYPE
                                                                                                                                                                                                            (rs2, rs1, rd, MIN))))
                                                                                                                                                                                                    else
                                                                                                                                                                                                      (pure none)))
                                                                                                                                                                                            else
                                                                                                                                                                                              (pure none)) with
                                                                                                                                                                                          | .some result =>
                                                                                                                                                                                            (pure result)
                                                                                                                                                                                          | none =>
                                                                                                                                                                                            (do
                                                                                                                                                                                              match (← do
                                                                                                                                                                                                let v__138 :=
                                                                                                                                                                                                  head_exp_
                                                                                                                                                                                                if (((let mapping134_ : (BitVec 5) :=
                                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                                         v__138
                                                                                                                                                                                                         11
                                                                                                                                                                                                         7)
                                                                                                                                                                                                     let mapping133_ : (BitVec 5) :=
                                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                                         v__138
                                                                                                                                                                                                         19
                                                                                                                                                                                                         15)
                                                                                                                                                                                                     let mapping132_ : (BitVec 5) :=
                                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                                         v__138
                                                                                                                                                                                                         24
                                                                                                                                                                                                         20)
                                                                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                                                                         mapping132_) && ((encdec_reg_backwards_matches
                                                                                                                                                                                                           mapping133_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                           mapping134_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                           v__138
                                                                                                                                                                                                           31
                                                                                                                                                                                                           25) == (0b0000101#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                             v__138
                                                                                                                                                                                                             14
                                                                                                                                                                                                             12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                             v__138
                                                                                                                                                                                                             6
                                                                                                                                                                                                             0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                then
                                                                                                                                                                                                  (do
                                                                                                                                                                                                    let mapping134_ : (BitVec 5) :=
                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                        v__138
                                                                                                                                                                                                        11
                                                                                                                                                                                                        7)
                                                                                                                                                                                                    let mapping133_ : (BitVec 5) :=
                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                        v__138
                                                                                                                                                                                                        19
                                                                                                                                                                                                        15)
                                                                                                                                                                                                    let mapping132_ : (BitVec 5) :=
                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                        v__138
                                                                                                                                                                                                        24
                                                                                                                                                                                                        20)
                                                                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                                                                        mapping132_)), (← (encdec_reg_backwards
                                                                                                                                                                                                        mapping133_)), (← (encdec_reg_backwards
                                                                                                                                                                                                        mapping134_))) with
                                                                                                                                                                                                    | (rs2, rs1, rd) =>
                                                                                                                                                                                                      (do
                                                                                                                                                                                                        if ((← (currentlyEnabled
                                                                                                                                                                                                               Ext_Zbb)) : Bool)
                                                                                                                                                                                                        then
                                                                                                                                                                                                          (pure (some
                                                                                                                                                                                                              (ZBB_RTYPE
                                                                                                                                                                                                                (rs2, rs1, rd, MINU))))
                                                                                                                                                                                                        else
                                                                                                                                                                                                          (pure none)))
                                                                                                                                                                                                else
                                                                                                                                                                                                  (pure none)) with
                                                                                                                                                                                              | .some result =>
                                                                                                                                                                                                (pure result)
                                                                                                                                                                                              | none =>
                                                                                                                                                                                                (do
                                                                                                                                                                                                  match (← do
                                                                                                                                                                                                    let v__134 :=
                                                                                                                                                                                                      head_exp_
                                                                                                                                                                                                    if (((let mapping137_ : (BitVec 5) :=
                                                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                                                             v__134
                                                                                                                                                                                                             11
                                                                                                                                                                                                             7)
                                                                                                                                                                                                         let mapping136_ : (BitVec 5) :=
                                                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                                                             v__134
                                                                                                                                                                                                             19
                                                                                                                                                                                                             15)
                                                                                                                                                                                                         let mapping135_ : (BitVec 5) :=
                                                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                                                             v__134
                                                                                                                                                                                                             24
                                                                                                                                                                                                             20)
                                                                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                                                                             mapping135_) && ((encdec_reg_backwards_matches
                                                                                                                                                                                                               mapping136_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                               mapping137_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                               v__134
                                                                                                                                                                                                               31
                                                                                                                                                                                                               25) == (0b0110000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                 v__134
                                                                                                                                                                                                                 14
                                                                                                                                                                                                                 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                 v__134
                                                                                                                                                                                                                 6
                                                                                                                                                                                                                 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                    then
                                                                                                                                                                                                      (do
                                                                                                                                                                                                        let mapping137_ : (BitVec 5) :=
                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                            v__134
                                                                                                                                                                                                            11
                                                                                                                                                                                                            7)
                                                                                                                                                                                                        let mapping136_ : (BitVec 5) :=
                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                            v__134
                                                                                                                                                                                                            19
                                                                                                                                                                                                            15)
                                                                                                                                                                                                        let mapping135_ : (BitVec 5) :=
                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                            v__134
                                                                                                                                                                                                            24
                                                                                                                                                                                                            20)
                                                                                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                                                                                            mapping135_)), (← (encdec_reg_backwards
                                                                                                                                                                                                            mapping136_)), (← (encdec_reg_backwards
                                                                                                                                                                                                            mapping137_))) with
                                                                                                                                                                                                        | (rs2, rs1, rd) =>
                                                                                                                                                                                                          (do
                                                                                                                                                                                                            if (((← (currentlyEnabled
                                                                                                                                                                                                                     Ext_Zbb)) || (← (currentlyEnabled
                                                                                                                                                                                                                     Ext_Zbkb))) : Bool)
                                                                                                                                                                                                            then
                                                                                                                                                                                                              (pure (some
                                                                                                                                                                                                                  (ZBB_RTYPE
                                                                                                                                                                                                                    (rs2, rs1, rd, ROL))))
                                                                                                                                                                                                            else
                                                                                                                                                                                                              (pure none)))
                                                                                                                                                                                                    else
                                                                                                                                                                                                      (pure none)) with
                                                                                                                                                                                                  | .some result =>
                                                                                                                                                                                                    (pure result)
                                                                                                                                                                                                  | none =>
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      match (← do
                                                                                                                                                                                                        let v__130 :=
                                                                                                                                                                                                          head_exp_
                                                                                                                                                                                                        if (((let mapping140_ : (BitVec 5) :=
                                                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                                                 v__130
                                                                                                                                                                                                                 11
                                                                                                                                                                                                                 7)
                                                                                                                                                                                                             let mapping139_ : (BitVec 5) :=
                                                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                                                 v__130
                                                                                                                                                                                                                 19
                                                                                                                                                                                                                 15)
                                                                                                                                                                                                             let mapping138_ : (BitVec 5) :=
                                                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                                                 v__130
                                                                                                                                                                                                                 24
                                                                                                                                                                                                                 20)
                                                                                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                                                                                 mapping138_) && ((encdec_reg_backwards_matches
                                                                                                                                                                                                                   mapping139_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                   mapping140_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                   v__130
                                                                                                                                                                                                                   31
                                                                                                                                                                                                                   25) == (0b0110000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                     v__130
                                                                                                                                                                                                                     14
                                                                                                                                                                                                                     12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                     v__130
                                                                                                                                                                                                                     6
                                                                                                                                                                                                                     0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                        then
                                                                                                                                                                                                          (do
                                                                                                                                                                                                            let mapping140_ : (BitVec 5) :=
                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                v__130
                                                                                                                                                                                                                11
                                                                                                                                                                                                                7)
                                                                                                                                                                                                            let mapping139_ : (BitVec 5) :=
                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                v__130
                                                                                                                                                                                                                19
                                                                                                                                                                                                                15)
                                                                                                                                                                                                            let mapping138_ : (BitVec 5) :=
                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                v__130
                                                                                                                                                                                                                24
                                                                                                                                                                                                                20)
                                                                                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                                                                                mapping138_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                mapping139_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                mapping140_))) with
                                                                                                                                                                                                            | (rs2, rs1, rd) =>
                                                                                                                                                                                                              (do
                                                                                                                                                                                                                if (((← (currentlyEnabled
                                                                                                                                                                                                                         Ext_Zbb)) || (← (currentlyEnabled
                                                                                                                                                                                                                         Ext_Zbkb))) : Bool)
                                                                                                                                                                                                                then
                                                                                                                                                                                                                  (pure (some
                                                                                                                                                                                                                      (ZBB_RTYPE
                                                                                                                                                                                                                        (rs2, rs1, rd, ROR))))
                                                                                                                                                                                                                else
                                                                                                                                                                                                                  (pure none)))
                                                                                                                                                                                                        else
                                                                                                                                                                                                          (pure none)) with
                                                                                                                                                                                                      | .some result =>
                                                                                                                                                                                                        (pure result)
                                                                                                                                                                                                      | none =>
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          match (← do
                                                                                                                                                                                                            let v__125 :=
                                                                                                                                                                                                              head_exp_
                                                                                                                                                                                                            if (((let mapping142_ : (BitVec 5) :=
                                                                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                                                                     v__125
                                                                                                                                                                                                                     11
                                                                                                                                                                                                                     7)
                                                                                                                                                                                                                 let mapping141_ : (BitVec 5) :=
                                                                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                                                                     v__125
                                                                                                                                                                                                                     19
                                                                                                                                                                                                                     15)
                                                                                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                                                                                     mapping141_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                     mapping142_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                       v__125
                                                                                                                                                                                                                       31
                                                                                                                                                                                                                       20) == (0x604#12 : (BitVec 12))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                         v__125
                                                                                                                                                                                                                         14
                                                                                                                                                                                                                         12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                         v__125
                                                                                                                                                                                                                         6
                                                                                                                                                                                                                         0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                            then
                                                                                                                                                                                                              (do
                                                                                                                                                                                                                let mapping142_ : (BitVec 5) :=
                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                    v__125
                                                                                                                                                                                                                    11
                                                                                                                                                                                                                    7)
                                                                                                                                                                                                                let mapping141_ : (BitVec 5) :=
                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                    v__125
                                                                                                                                                                                                                    19
                                                                                                                                                                                                                    15)
                                                                                                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                                                                                                    mapping141_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                    mapping142_))) with
                                                                                                                                                                                                                | (rs1, rd) =>
                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                    if ((← (currentlyEnabled
                                                                                                                                                                                                                           Ext_Zbb)) : Bool)
                                                                                                                                                                                                                    then
                                                                                                                                                                                                                      (pure (some
                                                                                                                                                                                                                          (ZBB_EXTOP
                                                                                                                                                                                                                            (rs1, rd, SEXTB))))
                                                                                                                                                                                                                    else
                                                                                                                                                                                                                      (pure none)))
                                                                                                                                                                                                            else
                                                                                                                                                                                                              (pure none)) with
                                                                                                                                                                                                          | .some result =>
                                                                                                                                                                                                            (pure result)
                                                                                                                                                                                                          | none =>
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              match (← do
                                                                                                                                                                                                                let v__120 :=
                                                                                                                                                                                                                  head_exp_
                                                                                                                                                                                                                if (((let mapping144_ : (BitVec 5) :=
                                                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                                                         v__120
                                                                                                                                                                                                                         11
                                                                                                                                                                                                                         7)
                                                                                                                                                                                                                     let mapping143_ : (BitVec 5) :=
                                                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                                                         v__120
                                                                                                                                                                                                                         19
                                                                                                                                                                                                                         15)
                                                                                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                                                                                         mapping143_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                         mapping144_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                           v__120
                                                                                                                                                                                                                           31
                                                                                                                                                                                                                           20) == (0x605#12 : (BitVec 12))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                             v__120
                                                                                                                                                                                                                             14
                                                                                                                                                                                                                             12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                             v__120
                                                                                                                                                                                                                             6
                                                                                                                                                                                                                             0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                                then
                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                    let mapping144_ : (BitVec 5) :=
                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                        v__120
                                                                                                                                                                                                                        11
                                                                                                                                                                                                                        7)
                                                                                                                                                                                                                    let mapping143_ : (BitVec 5) :=
                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                        v__120
                                                                                                                                                                                                                        19
                                                                                                                                                                                                                        15)
                                                                                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                                                                                        mapping143_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                        mapping144_))) with
                                                                                                                                                                                                                    | (rs1, rd) =>
                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                        if ((← (currentlyEnabled
                                                                                                                                                                                                                               Ext_Zbb)) : Bool)
                                                                                                                                                                                                                        then
                                                                                                                                                                                                                          (pure (some
                                                                                                                                                                                                                              (ZBB_EXTOP
                                                                                                                                                                                                                                (rs1, rd, SEXTH))))
                                                                                                                                                                                                                        else
                                                                                                                                                                                                                          (pure none)))
                                                                                                                                                                                                                else
                                                                                                                                                                                                                  (pure none)) with
                                                                                                                                                                                                              | .some result =>
                                                                                                                                                                                                                (pure result)
                                                                                                                                                                                                              | none =>
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  match (← do
                                                                                                                                                                                                                    let v__115 :=
                                                                                                                                                                                                                      head_exp_
                                                                                                                                                                                                                    if (((let mapping146_ : (BitVec 5) :=
                                                                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                                                                             v__115
                                                                                                                                                                                                                             11
                                                                                                                                                                                                                             7)
                                                                                                                                                                                                                         let mapping145_ : (BitVec 5) :=
                                                                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                                                                             v__115
                                                                                                                                                                                                                             19
                                                                                                                                                                                                                             15)
                                                                                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                                                                                             mapping145_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                             mapping146_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                               v__115
                                                                                                                                                                                                                               31
                                                                                                                                                                                                                               20) == (0x080#12 : (BitVec 12))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                 v__115
                                                                                                                                                                                                                                 14
                                                                                                                                                                                                                                 12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                 v__115
                                                                                                                                                                                                                                 6
                                                                                                                                                                                                                                 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                                    then
                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                        let mapping146_ : (BitVec 5) :=
                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                            v__115
                                                                                                                                                                                                                            11
                                                                                                                                                                                                                            7)
                                                                                                                                                                                                                        let mapping145_ : (BitVec 5) :=
                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                            v__115
                                                                                                                                                                                                                            19
                                                                                                                                                                                                                            15)
                                                                                                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                                                                                                            mapping145_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                            mapping146_))) with
                                                                                                                                                                                                                        | (rs1, rd) =>
                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                            if (((← (currentlyEnabled
                                                                                                                                                                                                                                     Ext_Zbb)) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                            then
                                                                                                                                                                                                                              (pure (some
                                                                                                                                                                                                                                  (ZBB_EXTOP
                                                                                                                                                                                                                                    (rs1, rd, ZEXTH))))
                                                                                                                                                                                                                            else
                                                                                                                                                                                                                              (pure none)))
                                                                                                                                                                                                                    else
                                                                                                                                                                                                                      (pure none)) with
                                                                                                                                                                                                                  | .some result =>
                                                                                                                                                                                                                    (pure result)
                                                                                                                                                                                                                  | none =>
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      match (← do
                                                                                                                                                                                                                        let v__110 :=
                                                                                                                                                                                                                          head_exp_
                                                                                                                                                                                                                        if (((let mapping148_ : (BitVec 5) :=
                                                                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                 v__110
                                                                                                                                                                                                                                 11
                                                                                                                                                                                                                                 7)
                                                                                                                                                                                                                             let mapping147_ : (BitVec 5) :=
                                                                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                 v__110
                                                                                                                                                                                                                                 19
                                                                                                                                                                                                                                 15)
                                                                                                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                                                                                                 mapping147_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                                 mapping148_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                   v__110
                                                                                                                                                                                                                                   31
                                                                                                                                                                                                                                   20) == (0x080#12 : (BitVec 12))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                     v__110
                                                                                                                                                                                                                                     14
                                                                                                                                                                                                                                     12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                     v__110
                                                                                                                                                                                                                                     6
                                                                                                                                                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                                        then
                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                            let mapping148_ : (BitVec 5) :=
                                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                v__110
                                                                                                                                                                                                                                11
                                                                                                                                                                                                                                7)
                                                                                                                                                                                                                            let mapping147_ : (BitVec 5) :=
                                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                v__110
                                                                                                                                                                                                                                19
                                                                                                                                                                                                                                15)
                                                                                                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                                                                                                mapping147_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                                mapping148_))) with
                                                                                                                                                                                                                            | (rs1, rd) =>
                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                if (((← (currentlyEnabled
                                                                                                                                                                                                                                         Ext_Zbb)) && (xlen == 64)) : Bool)
                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                  (pure (some
                                                                                                                                                                                                                                      (ZBB_EXTOP
                                                                                                                                                                                                                                        (rs1, rd, ZEXTH))))
                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                  (pure none)))
                                                                                                                                                                                                                        else
                                                                                                                                                                                                                          (pure none)) with
                                                                                                                                                                                                                      | .some result =>
                                                                                                                                                                                                                        (pure result)
                                                                                                                                                                                                                      | none =>
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          match (← do
                                                                                                                                                                                                                            let v__106 :=
                                                                                                                                                                                                                              head_exp_
                                                                                                                                                                                                                            if (((let mapping150_ : (BitVec 5) :=
                                                                                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                     v__106
                                                                                                                                                                                                                                     11
                                                                                                                                                                                                                                     7)
                                                                                                                                                                                                                                 let mapping149_ : (BitVec 5) :=
                                                                                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                     v__106
                                                                                                                                                                                                                                     19
                                                                                                                                                                                                                                     15)
                                                                                                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                                                                                                     mapping149_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                                     mapping150_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                       v__106
                                                                                                                                                                                                                                       31
                                                                                                                                                                                                                                       20) == (0x698#12 : (BitVec 12))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                         v__106
                                                                                                                                                                                                                                         14
                                                                                                                                                                                                                                         12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                         v__106
                                                                                                                                                                                                                                         6
                                                                                                                                                                                                                                         0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                                            then
                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                let mapping150_ : (BitVec 5) :=
                                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                    v__106
                                                                                                                                                                                                                                    11
                                                                                                                                                                                                                                    7)
                                                                                                                                                                                                                                let mapping149_ : (BitVec 5) :=
                                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                    v__106
                                                                                                                                                                                                                                    19
                                                                                                                                                                                                                                    15)
                                                                                                                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                                                                                                                    mapping149_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                                    mapping150_))) with
                                                                                                                                                                                                                                | (rs1, rd) =>
                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                    if ((((← (currentlyEnabled
                                                                                                                                                                                                                                               Ext_Zbb)) || (← (currentlyEnabled
                                                                                                                                                                                                                                               Ext_Zbkb))) && (xlen == 32)) : Bool)
                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                      (pure (some
                                                                                                                                                                                                                                          (REV8
                                                                                                                                                                                                                                            (rs1, rd))))
                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                      (pure none)))
                                                                                                                                                                                                                            else
                                                                                                                                                                                                                              (pure none)) with
                                                                                                                                                                                                                          | .some result =>
                                                                                                                                                                                                                            (pure result)
                                                                                                                                                                                                                          | none =>
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              match (← do
                                                                                                                                                                                                                                let v__102 :=
                                                                                                                                                                                                                                  head_exp_
                                                                                                                                                                                                                                if (((let mapping152_ : (BitVec 5) :=
                                                                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                         v__102
                                                                                                                                                                                                                                         11
                                                                                                                                                                                                                                         7)
                                                                                                                                                                                                                                     let mapping151_ : (BitVec 5) :=
                                                                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                         v__102
                                                                                                                                                                                                                                         19
                                                                                                                                                                                                                                         15)
                                                                                                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                                                                                                         mapping151_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                                         mapping152_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                           v__102
                                                                                                                                                                                                                                           31
                                                                                                                                                                                                                                           20) == (0x6B8#12 : (BitVec 12))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                             v__102
                                                                                                                                                                                                                                             14
                                                                                                                                                                                                                                             12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                             v__102
                                                                                                                                                                                                                                             6
                                                                                                                                                                                                                                             0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                    let mapping152_ : (BitVec 5) :=
                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                        v__102
                                                                                                                                                                                                                                        11
                                                                                                                                                                                                                                        7)
                                                                                                                                                                                                                                    let mapping151_ : (BitVec 5) :=
                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                        v__102
                                                                                                                                                                                                                                        19
                                                                                                                                                                                                                                        15)
                                                                                                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                                                                                                        mapping151_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                                        mapping152_))) with
                                                                                                                                                                                                                                    | (rs1, rd) =>
                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                        if ((((← (currentlyEnabled
                                                                                                                                                                                                                                                   Ext_Zbb)) || (← (currentlyEnabled
                                                                                                                                                                                                                                                   Ext_Zbkb))) && (xlen == 64)) : Bool)
                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                          (pure (some
                                                                                                                                                                                                                                              (REV8
                                                                                                                                                                                                                                                (rs1, rd))))
                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                          (pure none)))
                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                  (pure none)) with
                                                                                                                                                                                                                              | .some result =>
                                                                                                                                                                                                                                (pure result)
                                                                                                                                                                                                                              | none =>
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  match (← do
                                                                                                                                                                                                                                    let v__98 :=
                                                                                                                                                                                                                                      head_exp_
                                                                                                                                                                                                                                    if (((let mapping154_ : (BitVec 5) :=
                                                                                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                             v__98
                                                                                                                                                                                                                                             11
                                                                                                                                                                                                                                             7)
                                                                                                                                                                                                                                         let mapping153_ : (BitVec 5) :=
                                                                                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                             v__98
                                                                                                                                                                                                                                             19
                                                                                                                                                                                                                                             15)
                                                                                                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                                                                                                             mapping153_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                                             mapping154_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                               v__98
                                                                                                                                                                                                                                               31
                                                                                                                                                                                                                                               20) == (0x287#12 : (BitVec 12))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                 v__98
                                                                                                                                                                                                                                                 14
                                                                                                                                                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                 v__98
                                                                                                                                                                                                                                                 6
                                                                                                                                                                                                                                                 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                        let mapping154_ : (BitVec 5) :=
                                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                            v__98
                                                                                                                                                                                                                                            11
                                                                                                                                                                                                                                            7)
                                                                                                                                                                                                                                        let mapping153_ : (BitVec 5) :=
                                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                            v__98
                                                                                                                                                                                                                                            19
                                                                                                                                                                                                                                            15)
                                                                                                                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                                                                                                                            mapping153_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                                            mapping154_))) with
                                                                                                                                                                                                                                        | (rs1, rd) =>
                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                            if ((← (currentlyEnabled
                                                                                                                                                                                                                                                   Ext_Zbb)) : Bool)
                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                              (pure (some
                                                                                                                                                                                                                                                  (ORCB
                                                                                                                                                                                                                                                    (rs1, rd))))
                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                              (pure none)))
                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                      (pure none)) with
                                                                                                                                                                                                                                  | .some result =>
                                                                                                                                                                                                                                    (pure result)
                                                                                                                                                                                                                                  | none =>
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      match (← do
                                                                                                                                                                                                                                        let v__93 :=
                                                                                                                                                                                                                                          head_exp_
                                                                                                                                                                                                                                        if (((let mapping156_ : (BitVec 5) :=
                                                                                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                 v__93
                                                                                                                                                                                                                                                 11
                                                                                                                                                                                                                                                 7)
                                                                                                                                                                                                                                             let mapping155_ : (BitVec 5) :=
                                                                                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                 v__93
                                                                                                                                                                                                                                                 19
                                                                                                                                                                                                                                                 15)
                                                                                                                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                                                                                                                 mapping155_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                                                 mapping156_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                   v__93
                                                                                                                                                                                                                                                   31
                                                                                                                                                                                                                                                   20) == (0x602#12 : (BitVec 12))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                     v__93
                                                                                                                                                                                                                                                     14
                                                                                                                                                                                                                                                     12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                     v__93
                                                                                                                                                                                                                                                     6
                                                                                                                                                                                                                                                     0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                            let mapping156_ : (BitVec 5) :=
                                                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                v__93
                                                                                                                                                                                                                                                11
                                                                                                                                                                                                                                                7)
                                                                                                                                                                                                                                            let mapping155_ : (BitVec 5) :=
                                                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                v__93
                                                                                                                                                                                                                                                19
                                                                                                                                                                                                                                                15)
                                                                                                                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                                                                                                                mapping155_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                                                mapping156_))) with
                                                                                                                                                                                                                                            | (rs1, rd) =>
                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                if ((← (currentlyEnabled
                                                                                                                                                                                                                                                       Ext_Zbb)) : Bool)
                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                  (pure (some
                                                                                                                                                                                                                                                      (CPOP
                                                                                                                                                                                                                                                        (rs1, rd))))
                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                  (pure none)))
                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                          (pure none)) with
                                                                                                                                                                                                                                      | .some result =>
                                                                                                                                                                                                                                        (pure result)
                                                                                                                                                                                                                                      | none =>
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          match (← do
                                                                                                                                                                                                                                            let v__88 :=
                                                                                                                                                                                                                                              head_exp_
                                                                                                                                                                                                                                            if (((let mapping158_ : (BitVec 5) :=
                                                                                                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                     v__88
                                                                                                                                                                                                                                                     11
                                                                                                                                                                                                                                                     7)
                                                                                                                                                                                                                                                 let mapping157_ : (BitVec 5) :=
                                                                                                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                     v__88
                                                                                                                                                                                                                                                     19
                                                                                                                                                                                                                                                     15)
                                                                                                                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                                                                                                                     mapping157_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                                                     mapping158_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                       v__88
                                                                                                                                                                                                                                                       31
                                                                                                                                                                                                                                                       20) == (0x602#12 : (BitVec 12))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                         v__88
                                                                                                                                                                                                                                                         14
                                                                                                                                                                                                                                                         12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                         v__88
                                                                                                                                                                                                                                                         6
                                                                                                                                                                                                                                                         0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                let mapping158_ : (BitVec 5) :=
                                                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                    v__88
                                                                                                                                                                                                                                                    11
                                                                                                                                                                                                                                                    7)
                                                                                                                                                                                                                                                let mapping157_ : (BitVec 5) :=
                                                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                    v__88
                                                                                                                                                                                                                                                    19
                                                                                                                                                                                                                                                    15)
                                                                                                                                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                                                                                                                                    mapping157_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                                                    mapping158_))) with
                                                                                                                                                                                                                                                | (rs1, rd) =>
                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                    if (((← (currentlyEnabled
                                                                                                                                                                                                                                                             Ext_Zbb)) && (xlen == 64)) : Bool)
                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                      (pure (some
                                                                                                                                                                                                                                                          (CPOPW
                                                                                                                                                                                                                                                            (rs1, rd))))
                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                      (pure none)))
                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                              (pure none)) with
                                                                                                                                                                                                                                          | .some result =>
                                                                                                                                                                                                                                            (pure result)
                                                                                                                                                                                                                                          | none =>
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              match (← do
                                                                                                                                                                                                                                                let v__83 :=
                                                                                                                                                                                                                                                  head_exp_
                                                                                                                                                                                                                                                if (((let mapping160_ : (BitVec 5) :=
                                                                                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                         v__83
                                                                                                                                                                                                                                                         11
                                                                                                                                                                                                                                                         7)
                                                                                                                                                                                                                                                     let mapping159_ : (BitVec 5) :=
                                                                                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                         v__83
                                                                                                                                                                                                                                                         19
                                                                                                                                                                                                                                                         15)
                                                                                                                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                                                                                                                         mapping159_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                                                         mapping160_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                           v__83
                                                                                                                                                                                                                                                           31
                                                                                                                                                                                                                                                           20) == (0x600#12 : (BitVec 12))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                             v__83
                                                                                                                                                                                                                                                             14
                                                                                                                                                                                                                                                             12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                             v__83
                                                                                                                                                                                                                                                             6
                                                                                                                                                                                                                                                             0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                    let mapping160_ : (BitVec 5) :=
                                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                        v__83
                                                                                                                                                                                                                                                        11
                                                                                                                                                                                                                                                        7)
                                                                                                                                                                                                                                                    let mapping159_ : (BitVec 5) :=
                                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                        v__83
                                                                                                                                                                                                                                                        19
                                                                                                                                                                                                                                                        15)
                                                                                                                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                                                                                                                        mapping159_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                                                        mapping160_))) with
                                                                                                                                                                                                                                                    | (rs1, rd) =>
                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                        if ((← (currentlyEnabled
                                                                                                                                                                                                                                                               Ext_Zbb)) : Bool)
                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                          (pure (some
                                                                                                                                                                                                                                                              (CLZ
                                                                                                                                                                                                                                                                (rs1, rd))))
                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                          (pure none)))
                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                  (pure none)) with
                                                                                                                                                                                                                                              | .some result =>
                                                                                                                                                                                                                                                (pure result)
                                                                                                                                                                                                                                              | none =>
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  match (← do
                                                                                                                                                                                                                                                    let v__78 :=
                                                                                                                                                                                                                                                      head_exp_
                                                                                                                                                                                                                                                    if (((let mapping162_ : (BitVec 5) :=
                                                                                                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                             v__78
                                                                                                                                                                                                                                                             11
                                                                                                                                                                                                                                                             7)
                                                                                                                                                                                                                                                         let mapping161_ : (BitVec 5) :=
                                                                                                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                             v__78
                                                                                                                                                                                                                                                             19
                                                                                                                                                                                                                                                             15)
                                                                                                                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                                                                                                                             mapping161_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                                                             mapping162_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                               v__78
                                                                                                                                                                                                                                                               31
                                                                                                                                                                                                                                                               20) == (0x600#12 : (BitVec 12))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                 v__78
                                                                                                                                                                                                                                                                 14
                                                                                                                                                                                                                                                                 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                 v__78
                                                                                                                                                                                                                                                                 6
                                                                                                                                                                                                                                                                 0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                        let mapping162_ : (BitVec 5) :=
                                                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                            v__78
                                                                                                                                                                                                                                                            11
                                                                                                                                                                                                                                                            7)
                                                                                                                                                                                                                                                        let mapping161_ : (BitVec 5) :=
                                                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                            v__78
                                                                                                                                                                                                                                                            19
                                                                                                                                                                                                                                                            15)
                                                                                                                                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                                                                                                                                            mapping161_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                                                            mapping162_))) with
                                                                                                                                                                                                                                                        | (rs1, rd) =>
                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                            if (((← (currentlyEnabled
                                                                                                                                                                                                                                                                     Ext_Zbb)) && (xlen == 64)) : Bool)
                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                              (pure (some
                                                                                                                                                                                                                                                                  (CLZW
                                                                                                                                                                                                                                                                    (rs1, rd))))
                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                              (pure none)))
                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                      (pure none)) with
                                                                                                                                                                                                                                                  | .some result =>
                                                                                                                                                                                                                                                    (pure result)
                                                                                                                                                                                                                                                  | none =>
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      match (← do
                                                                                                                                                                                                                                                        let v__73 :=
                                                                                                                                                                                                                                                          head_exp_
                                                                                                                                                                                                                                                        if (((let mapping164_ : (BitVec 5) :=
                                                                                                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                 v__73
                                                                                                                                                                                                                                                                 11
                                                                                                                                                                                                                                                                 7)
                                                                                                                                                                                                                                                             let mapping163_ : (BitVec 5) :=
                                                                                                                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                 v__73
                                                                                                                                                                                                                                                                 19
                                                                                                                                                                                                                                                                 15)
                                                                                                                                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                                                                                                                                 mapping163_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                                                                 mapping164_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                   v__73
                                                                                                                                                                                                                                                                   31
                                                                                                                                                                                                                                                                   20) == (0x601#12 : (BitVec 12))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                     v__73
                                                                                                                                                                                                                                                                     14
                                                                                                                                                                                                                                                                     12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                     v__73
                                                                                                                                                                                                                                                                     6
                                                                                                                                                                                                                                                                     0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                            let mapping164_ : (BitVec 5) :=
                                                                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                v__73
                                                                                                                                                                                                                                                                11
                                                                                                                                                                                                                                                                7)
                                                                                                                                                                                                                                                            let mapping163_ : (BitVec 5) :=
                                                                                                                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                v__73
                                                                                                                                                                                                                                                                19
                                                                                                                                                                                                                                                                15)
                                                                                                                                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                                                                                                                                mapping163_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                                                                mapping164_))) with
                                                                                                                                                                                                                                                            | (rs1, rd) =>
                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                if ((← (currentlyEnabled
                                                                                                                                                                                                                                                                       Ext_Zbb)) : Bool)
                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                  (pure (some
                                                                                                                                                                                                                                                                      (CTZ
                                                                                                                                                                                                                                                                        (rs1, rd))))
                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                  (pure none)))
                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                          (pure none)) with
                                                                                                                                                                                                                                                      | .some result =>
                                                                                                                                                                                                                                                        (pure result)
                                                                                                                                                                                                                                                      | none =>
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          match (← do
                                                                                                                                                                                                                                                            let v__68 :=
                                                                                                                                                                                                                                                              head_exp_
                                                                                                                                                                                                                                                            if (((let mapping166_ : (BitVec 5) :=
                                                                                                                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                     v__68
                                                                                                                                                                                                                                                                     11
                                                                                                                                                                                                                                                                     7)
                                                                                                                                                                                                                                                                 let mapping165_ : (BitVec 5) :=
                                                                                                                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                     v__68
                                                                                                                                                                                                                                                                     19
                                                                                                                                                                                                                                                                     15)
                                                                                                                                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                                                                                                                                     mapping165_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                                                                     mapping166_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                       v__68
                                                                                                                                                                                                                                                                       31
                                                                                                                                                                                                                                                                       20) == (0x601#12 : (BitVec 12))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                         v__68
                                                                                                                                                                                                                                                                         14
                                                                                                                                                                                                                                                                         12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                         v__68
                                                                                                                                                                                                                                                                         6
                                                                                                                                                                                                                                                                         0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                let mapping166_ : (BitVec 5) :=
                                                                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                    v__68
                                                                                                                                                                                                                                                                    11
                                                                                                                                                                                                                                                                    7)
                                                                                                                                                                                                                                                                let mapping165_ : (BitVec 5) :=
                                                                                                                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                    v__68
                                                                                                                                                                                                                                                                    19
                                                                                                                                                                                                                                                                    15)
                                                                                                                                                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                                                                                                                                                    mapping165_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                                                                    mapping166_))) with
                                                                                                                                                                                                                                                                | (rs1, rd) =>
                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                    if (((← (currentlyEnabled
                                                                                                                                                                                                                                                                             Ext_Zbb)) && (xlen == 64)) : Bool)
                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                      (pure (some
                                                                                                                                                                                                                                                                          (CTZW
                                                                                                                                                                                                                                                                            (rs1, rd))))
                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                      (pure none)))
                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                              (pure none)) with
                                                                                                                                                                                                                                                          | .some result =>
                                                                                                                                                                                                                                                            (pure result)
                                                                                                                                                                                                                                                          | none =>
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              match (← do
                                                                                                                                                                                                                                                                let v__65 :=
                                                                                                                                                                                                                                                                  head_exp_
                                                                                                                                                                                                                                                                if (((let mapping169_ : (BitVec 5) :=
                                                                                                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                         v__65
                                                                                                                                                                                                                                                                         11
                                                                                                                                                                                                                                                                         7)
                                                                                                                                                                                                                                                                     let mapping168_ : (BitVec 2) :=
                                                                                                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                         v__65
                                                                                                                                                                                                                                                                         13
                                                                                                                                                                                                                                                                         12)
                                                                                                                                                                                                                                                                     let mapping167_ : (BitVec 5) :=
                                                                                                                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                         v__65
                                                                                                                                                                                                                                                                         19
                                                                                                                                                                                                                                                                         15)
                                                                                                                                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                                                                                                                                         mapping167_) && ((encdec_csrop_backwards_matches
                                                                                                                                                                                                                                                                           mapping168_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                                                                           mapping169_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                           v__65
                                                                                                                                                                                                                                                                           14
                                                                                                                                                                                                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                           v__65
                                                                                                                                                                                                                                                                           6
                                                                                                                                                                                                                                                                           0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                    let csr : (BitVec 12) :=
                                                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                        v__65
                                                                                                                                                                                                                                                                        31
                                                                                                                                                                                                                                                                        20)
                                                                                                                                                                                                                                                                    let mapping169_ : (BitVec 5) :=
                                                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                        v__65
                                                                                                                                                                                                                                                                        11
                                                                                                                                                                                                                                                                        7)
                                                                                                                                                                                                                                                                    let mapping168_ : (BitVec 2) :=
                                                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                        v__65
                                                                                                                                                                                                                                                                        13
                                                                                                                                                                                                                                                                        12)
                                                                                                                                                                                                                                                                    let mapping167_ : (BitVec 5) :=
                                                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                        v__65
                                                                                                                                                                                                                                                                        19
                                                                                                                                                                                                                                                                        15)
                                                                                                                                                                                                                                                                    let csr : (BitVec 12) :=
                                                                                                                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                        v__65
                                                                                                                                                                                                                                                                        31
                                                                                                                                                                                                                                                                        20)
                                                                                                                                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                                                                                                                                        mapping167_)), (← (encdec_csrop_backwards
                                                                                                                                                                                                                                                                        mapping168_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                                                                        mapping169_))) with
                                                                                                                                                                                                                                                                    | (rs1, op, rd) =>
                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                        if ((← (currentlyEnabled
                                                                                                                                                                                                                                                                               Ext_Zicsr)) : Bool)
                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                          (pure (some
                                                                                                                                                                                                                                                                              (CSRReg
                                                                                                                                                                                                                                                                                (csr, rs1, rd, op))))
                                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                                          (pure none)))
                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                  (pure none)) with
                                                                                                                                                                                                                                                              | .some result =>
                                                                                                                                                                                                                                                                (pure result)
                                                                                                                                                                                                                                                              | none =>
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  match (← do
                                                                                                                                                                                                                                                                    let v__62 :=
                                                                                                                                                                                                                                                                      head_exp_
                                                                                                                                                                                                                                                                    if (((let mapping171_ : (BitVec 5) :=
                                                                                                                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                             v__62
                                                                                                                                                                                                                                                                             11
                                                                                                                                                                                                                                                                             7)
                                                                                                                                                                                                                                                                         let mapping170_ : (BitVec 2) :=
                                                                                                                                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                             v__62
                                                                                                                                                                                                                                                                             13
                                                                                                                                                                                                                                                                             12)
                                                                                                                                                                                                                                                                         ((encdec_csrop_backwards_matches
                                                                                                                                                                                                                                                                             mapping170_) && (encdec_reg_backwards_matches
                                                                                                                                                                                                                                                                             mapping171_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                               v__62
                                                                                                                                                                                                                                                                               14
                                                                                                                                                                                                                                                                               14) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                               v__62
                                                                                                                                                                                                                                                                               6
                                                                                                                                                                                                                                                                               0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                        let csr : (BitVec 12) :=
                                                                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                            v__62
                                                                                                                                                                                                                                                                            31
                                                                                                                                                                                                                                                                            20)
                                                                                                                                                                                                                                                                        let mapping171_ : (BitVec 5) :=
                                                                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                            v__62
                                                                                                                                                                                                                                                                            11
                                                                                                                                                                                                                                                                            7)
                                                                                                                                                                                                                                                                        let mapping170_ : (BitVec 2) :=
                                                                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                            v__62
                                                                                                                                                                                                                                                                            13
                                                                                                                                                                                                                                                                            12)
                                                                                                                                                                                                                                                                        let imm : (BitVec 5) :=
                                                                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                            v__62
                                                                                                                                                                                                                                                                            19
                                                                                                                                                                                                                                                                            15)
                                                                                                                                                                                                                                                                        let csr : (BitVec 12) :=
                                                                                                                                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                            v__62
                                                                                                                                                                                                                                                                            31
                                                                                                                                                                                                                                                                            20)
                                                                                                                                                                                                                                                                        match ((← (encdec_csrop_backwards
                                                                                                                                                                                                                                                                            mapping170_)), (← (encdec_reg_backwards
                                                                                                                                                                                                                                                                            mapping171_))) with
                                                                                                                                                                                                                                                                        | (op, rd) =>
                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                            if ((← (currentlyEnabled
                                                                                                                                                                                                                                                                                   Ext_Zicsr)) : Bool)
                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                              (pure (some
                                                                                                                                                                                                                                                                                  (CSRImm
                                                                                                                                                                                                                                                                                    (csr, imm, rd, op))))
                                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                                              (pure none)))
                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                      (pure none)) with
                                                                                                                                                                                                                                                                  | .some result =>
                                                                                                                                                                                                                                                                    (pure result)
                                                                                                                                                                                                                                                                  | _ =>
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      assert false "Pattern match failure at unknown location"
                                                                                                                                                                                                                                                                      throw Error.Exit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def execute_UTYPE (imm : (BitVec 20)) (rd : regidx) (op : uop) : SailM ExecutionResult := do
  let off : xlenbits := (sign_extend (m := 32) (imm +++ 0x000#12))
  (wX_bits rd
    (← do
      match op with
      | .LUI => (pure off)
      | .AUIPC => (pure ((← (get_arch_pc ())) + off))))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: width : Nat, List.elem width [1, 2, 4, 8] -/
def execute_STORE (imm : (BitVec 12)) (rs2 : regidx) (rs1 : regidx) (width : Nat) : SailM ExecutionResult := do
  let offset : xlenbits := (sign_extend (m := 32) imm)
  assert (width ≤b xlen_bytes) "/private/tmp/airbender-sail-integration/model/model/extensions/I/base_insts.sail:320.28-320.29"
  let data ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) ((width *i 8) -i 1) 0))
  match (← (vmem_write rs1 offset width data (Store Data) false false false)) with
  | .Ok _ => (pure RETIRE_SUCCESS)
  | .Err e => (pure e)

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

/-- Type quantifiers: k_ex436588_ : Bool -/
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

/-- Type quantifiers: width : Nat, k_ex436589_ : Bool, List.elem width [1, 2, 4, 8] -/
def execute_LOAD (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) (width : Nat) : SailM ExecutionResult := do
  let offset : xlenbits := (sign_extend (m := 32) imm)
  assert (width ≤b xlen_bytes) "/private/tmp/airbender-sail-integration/model/model/extensions/I/base_insts.sail:289.28-289.29"
  match (← (vmem_read rs1 offset width (Load Data) false false false)) with
  | .Ok data =>
    (do
      (wX_bits rd (extend_value is_unsigned data))
      (pure RETIRE_SUCCESS))
  | .Err e => (pure e)

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

/-- Type quantifiers: k_ex436592_ : Bool -/
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
