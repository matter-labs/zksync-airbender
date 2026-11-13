import SailRV32.Flow
import SailRV32.Prelude
import SailRV32.Xlen
import SailRV32.Types
import SailRV32.MemUtils

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
  «assert» (width == (num_accesses *i bytes_per_access)) "sys/split_access_utils.sail:53.49-53.50"
  (pure (num_accesses, bytes_per_access))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def prop_split_access (addr : (BitVec 16)) (width : Nat) : SailM Bool := do
  let (splits, split_width) ← do (split_access addr width)
  (pure ((splits *i split_width) == width))

def sys_misaligned_byte_by_byte : Bool := false

def undefined_Splittability (_ : Unit) : SailM Splittability := do
  (internal_pick [CanSplit, CannotSplit])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def Splittability_of_num (arg_ : Nat) : Splittability :=
  match arg_ with
  | 0 => CanSplit
  | _ => CannotSplit

def num_of_Splittability (arg_ : Splittability) : Int :=
  match arg_ with
  | .CanSplit => 0
  | .CannotSplit => 1

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
      «assert» (nbytes_to_boundary <b width) "sys/split_access_utils.sail:111.37-111.38"
      (pure (nbytes_to_boundary, (width -i nbytes_to_boundary))))

/-- Type quantifiers: width : Nat, (is_mem_width width) -/
def prop_access_in_same_page (addr : (BitVec 16)) (width : Nat) : SailM Bool := do
  let (p, q) ← do (split_on_page_boundary addr width)
  let page_mask : (BitVec 16) := 0xF000#16
  (pure ((zopz0zJzJzK (q == 0)
        ((addr &&& page_mask) == ((BitVec.subInt (BitVec.addInt addr width) 1) &&& page_mask))) && (zopz0zJzJzK
        ((addr &&& page_mask) == ((BitVec.subInt (BitVec.addInt addr width) 1) &&& page_mask))
        (q == 0))))

/-- Type quantifiers: width : Nat, (is_mem_width width) -/
def prop_access_across_page_boundary (addr : (BitVec 16)) (width : Nat) : SailM Bool := do
  let (p, q) ← do (split_on_page_boundary addr width)
  let page_mask : (BitVec 16) := 0xF000#16
  (pure ((zopz0zJzJzK (q != 0)
        ((addr &&& page_mask) != ((BitVec.subInt (BitVec.addInt addr width) 1) &&& page_mask))) && (zopz0zJzJzK
        ((addr &&& page_mask) != ((BitVec.subInt (BitVec.addInt addr width) 1) &&& page_mask))
        (q != 0))))

