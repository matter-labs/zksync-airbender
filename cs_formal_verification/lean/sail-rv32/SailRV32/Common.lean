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

def fp_eflag_none : fp_exception_flags := 0b00000#5

def fp_eflag_invalid : fp_exception_flags := 0b00001#5

def fp_eflag_divide_by_zero : fp_exception_flags := 0b00010#5

def fp_eflag_oveflow : fp_exception_flags := 0b00100#5

def fp_eflag_underflow : fp_exception_flags := 0b01000#5

def fp_eflag_inexact : fp_exception_flags := 0b10000#5

def fp_eflag_overflow_and_inexact : fp_exception_flags := (fp_eflag_oveflow ||| fp_eflag_inexact)

def fp_rounding_rne : fp_rounding_modes := 0b00001#5

def fp_rounding_rna : fp_rounding_modes := 0b00010#5

def fp_rounding_rdn : fp_rounding_modes := 0b00011#5

def fp_rounding_rup : fp_rounding_modes := 0b00100#5

def fp_rounding_rtz : fp_rounding_modes := 0b00101#5

def fp_rounding_default : fp_rounding_modes := fp_rounding_rne

/-- Type quantifiers: atom_n : Int -/
def undefined_float_bits (atom_n : Int) : SailM (float_bits atom_n) := do
  (pure { sign := ← (undefined_bitvector 1)
          exp := ← (undefined_bitvector
              (if ((atom_n == 16) : Bool)
              then 5
              else
                (if ((atom_n == 32) : Bool)
                then 8
                else
                  (if ((atom_n == 64) : Bool)
                  then 11
                  else 15))))
          mantissa := ← (undefined_bitvector
              (if ((atom_n == 16) : Bool)
              then 10
              else
                (if ((atom_n == 32) : Bool)
                then 23
                else
                  (if ((atom_n == 64) : Bool)
                  then 52
                  else 112)))) })

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, (is_fp_bits k_n) -/
def float_decompose (op : (BitVec k_n)) : (float_bits k_n) :=
  match (Sail.BitVec.length op) with
  | 16 =>
    { sign := (Sail.BitVec.extractLsb op 15 15)
      exp := (Sail.BitVec.extractLsb op 14 10)
      mantissa := (Sail.BitVec.extractLsb op 9 0) }
  | 32 =>
    { sign := (Sail.BitVec.extractLsb op 31 31)
      exp := (Sail.BitVec.extractLsb op 30 23)
      mantissa := (Sail.BitVec.extractLsb op 22 0) }
  | 64 =>
    { sign := (Sail.BitVec.extractLsb op 63 63)
      exp := (Sail.BitVec.extractLsb op 62 52)
      mantissa := (Sail.BitVec.extractLsb op 51 0) }
  | _ =>
    { sign := (Sail.BitVec.extractLsb op 127 127)
      exp := (Sail.BitVec.extractLsb op 126 112)
      mantissa := (Sail.BitVec.extractLsb op 111 0) }

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, (is_fp_bits k_n) -/
def float_compose (op : (float_bits k_n)) : (BitVec k_n) :=
  (op.sign +++ (op.exp +++ op.mantissa))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, (is_fp_bits k_n) -/
def float_has_max_exp (op : (BitVec k_n)) : Bool :=
  let fp := (float_decompose op)
  let bitsize := (Sail.BitVec.length op)
  let one := (Sail.BitVec.zeroExtend (1#1 : (BitVec 1)) bitsize)
  let two := (one <<< 1)
  let max_exp := ((one <<< (Sail.BitVec.length fp.exp)) - two)
  (max_exp == (Sail.BitVec.zeroExtend fp.exp bitsize))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, 0 < k_n -/
def is_lowest_one (op : (BitVec k_n)) : Bool :=
  ((BitVec.access op 0) == 1#1)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, 0 < k_n -/
def is_highest_one (op : (BitVec k_n)) : Bool :=
  ((BitVec.access op ((Sail.BitVec.length op) -i 1)) == 1#1)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, 0 < k_n -/
def is_all_ones (op : (BitVec k_n)) : Bool :=
  (op == (sail_ones (Sail.BitVec.length op)))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, 0 < k_n -/
def is_lowest_zero (op : (BitVec k_n)) : Bool :=
  ((BitVec.access op 0) == 0#1)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, 0 < k_n -/
def is_highest_zero (op : (BitVec k_n)) : Bool :=
  ((BitVec.access op ((Sail.BitVec.length op) -i 1)) == 0#1)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, 0 < k_n -/
def is_all_zeros (op : (BitVec k_n)) : Bool :=
  (op == (BitVec.zero (Sail.BitVec.length op)))

