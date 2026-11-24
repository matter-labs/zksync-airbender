import Sail
import SailRV32.Defs
import SailRV32.SpecializationArchSem
import SailRV32.FakeReal
import SailRV32.RiscvExtrasExecutable

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

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def hex_bits_forwards (bv : (BitVec k_n)) : (Nat × String) :=
  ((Sail.BitVec.length bv), (Int.toHex (BitVec.toNatInt bv)))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def hex_bits_forwards_matches (x_0 : (BitVec k_n)) : Bool :=
  true

/-- Type quantifiers: tuple_0.1 : Nat, tuple_0.1 ≥ 0, tuple_0.1 > 0 -/
def hex_bits_backwards (tuple_0 : (Nat × String)) : (BitVec tuple_0.1) :=
  let (n, str) := tuple_0
  (parse_hex_bits n str)

/-- Type quantifiers: tuple_0.1 : Nat, tuple_0.1 ≥ 0, tuple_0.1 > 0 -/
def hex_bits_backwards_matches (tuple_0 : (Nat × String)) : Bool :=
  let (n, str) := tuple_0
  (valid_hex_bits n str)

def hex_bits_1_forwards (arg_ : (BitVec 1)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (1, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_1_backwards (arg_ : String) : SailM (BitVec 1) := do
  let s := arg_
  if ((hex_bits_backwards_matches (1, s)) : Bool)
  then (pure (hex_bits_backwards (1, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_1_forwards_matches (arg_ : (BitVec 1)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (1, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_1_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (1, s)) : Bool)
  then true
  else false

def hex_bits_2_forwards (arg_ : (BitVec 2)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (2, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_2_backwards (arg_ : String) : SailM (BitVec 2) := do
  let s := arg_
  if ((hex_bits_backwards_matches (2, s)) : Bool)
  then (pure (hex_bits_backwards (2, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_2_forwards_matches (arg_ : (BitVec 2)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (2, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_2_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (2, s)) : Bool)
  then true
  else false

def hex_bits_3_forwards (arg_ : (BitVec 3)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (3, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_3_backwards (arg_ : String) : SailM (BitVec 3) := do
  let s := arg_
  if ((hex_bits_backwards_matches (3, s)) : Bool)
  then (pure (hex_bits_backwards (3, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_3_forwards_matches (arg_ : (BitVec 3)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (3, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_3_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (3, s)) : Bool)
  then true
  else false

def hex_bits_4_forwards (arg_ : (BitVec 4)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (4, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_4_backwards (arg_ : String) : SailM (BitVec 4) := do
  let s := arg_
  if ((hex_bits_backwards_matches (4, s)) : Bool)
  then (pure (hex_bits_backwards (4, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_4_forwards_matches (arg_ : (BitVec 4)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (4, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_4_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (4, s)) : Bool)
  then true
  else false

def hex_bits_5_forwards (arg_ : (BitVec 5)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (5, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_5_backwards (arg_ : String) : SailM (BitVec 5) := do
  let s := arg_
  if ((hex_bits_backwards_matches (5, s)) : Bool)
  then (pure (hex_bits_backwards (5, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_5_forwards_matches (arg_ : (BitVec 5)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (5, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_5_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (5, s)) : Bool)
  then true
  else false

def hex_bits_6_forwards (arg_ : (BitVec 6)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (6, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_6_backwards (arg_ : String) : SailM (BitVec 6) := do
  let s := arg_
  if ((hex_bits_backwards_matches (6, s)) : Bool)
  then (pure (hex_bits_backwards (6, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_6_forwards_matches (arg_ : (BitVec 6)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (6, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_6_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (6, s)) : Bool)
  then true
  else false

def hex_bits_7_forwards (arg_ : (BitVec 7)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (7, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_7_backwards (arg_ : String) : SailM (BitVec 7) := do
  let s := arg_
  if ((hex_bits_backwards_matches (7, s)) : Bool)
  then (pure (hex_bits_backwards (7, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_7_forwards_matches (arg_ : (BitVec 7)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (7, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_7_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (7, s)) : Bool)
  then true
  else false

def hex_bits_8_forwards (arg_ : (BitVec 8)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (8, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_8_backwards (arg_ : String) : SailM (BitVec 8) := do
  let s := arg_
  if ((hex_bits_backwards_matches (8, s)) : Bool)
  then (pure (hex_bits_backwards (8, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_8_forwards_matches (arg_ : (BitVec 8)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (8, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_8_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (8, s)) : Bool)
  then true
  else false

def hex_bits_9_forwards (arg_ : (BitVec 9)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (9, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_9_backwards (arg_ : String) : SailM (BitVec 9) := do
  let s := arg_
  if ((hex_bits_backwards_matches (9, s)) : Bool)
  then (pure (hex_bits_backwards (9, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_9_forwards_matches (arg_ : (BitVec 9)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (9, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_9_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (9, s)) : Bool)
  then true
  else false

def hex_bits_10_forwards (arg_ : (BitVec 10)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (10, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_10_backwards (arg_ : String) : SailM (BitVec 10) := do
  let s := arg_
  if ((hex_bits_backwards_matches (10, s)) : Bool)
  then (pure (hex_bits_backwards (10, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_10_forwards_matches (arg_ : (BitVec 10)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (10, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_10_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (10, s)) : Bool)
  then true
  else false

def hex_bits_11_forwards (arg_ : (BitVec 11)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (11, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_11_backwards (arg_ : String) : SailM (BitVec 11) := do
  let s := arg_
  if ((hex_bits_backwards_matches (11, s)) : Bool)
  then (pure (hex_bits_backwards (11, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_11_forwards_matches (arg_ : (BitVec 11)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (11, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_11_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (11, s)) : Bool)
  then true
  else false

def hex_bits_12_forwards (arg_ : (BitVec 12)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (12, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_12_backwards (arg_ : String) : SailM (BitVec 12) := do
  let s := arg_
  if ((hex_bits_backwards_matches (12, s)) : Bool)
  then (pure (hex_bits_backwards (12, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_12_forwards_matches (arg_ : (BitVec 12)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (12, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_12_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (12, s)) : Bool)
  then true
  else false

def hex_bits_13_forwards (arg_ : (BitVec 13)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (13, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_13_backwards (arg_ : String) : SailM (BitVec 13) := do
  let s := arg_
  if ((hex_bits_backwards_matches (13, s)) : Bool)
  then (pure (hex_bits_backwards (13, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_13_forwards_matches (arg_ : (BitVec 13)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (13, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_13_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (13, s)) : Bool)
  then true
  else false

def hex_bits_14_forwards (arg_ : (BitVec 14)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (14, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_14_backwards (arg_ : String) : SailM (BitVec 14) := do
  let s := arg_
  if ((hex_bits_backwards_matches (14, s)) : Bool)
  then (pure (hex_bits_backwards (14, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_14_forwards_matches (arg_ : (BitVec 14)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (14, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_14_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (14, s)) : Bool)
  then true
  else false

def hex_bits_15_forwards (arg_ : (BitVec 15)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (15, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_15_backwards (arg_ : String) : SailM (BitVec 15) := do
  let s := arg_
  if ((hex_bits_backwards_matches (15, s)) : Bool)
  then (pure (hex_bits_backwards (15, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_15_forwards_matches (arg_ : (BitVec 15)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (15, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_15_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (15, s)) : Bool)
  then true
  else false

def hex_bits_16_forwards (arg_ : (BitVec 16)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (16, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_16_backwards (arg_ : String) : SailM (BitVec 16) := do
  let s := arg_
  if ((hex_bits_backwards_matches (16, s)) : Bool)
  then (pure (hex_bits_backwards (16, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_16_forwards_matches (arg_ : (BitVec 16)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (16, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_16_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (16, s)) : Bool)
  then true
  else false

def hex_bits_17_forwards (arg_ : (BitVec 17)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (17, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_17_backwards (arg_ : String) : SailM (BitVec 17) := do
  let s := arg_
  if ((hex_bits_backwards_matches (17, s)) : Bool)
  then (pure (hex_bits_backwards (17, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_17_forwards_matches (arg_ : (BitVec 17)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (17, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_17_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (17, s)) : Bool)
  then true
  else false

def hex_bits_18_forwards (arg_ : (BitVec 18)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (18, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_18_backwards (arg_ : String) : SailM (BitVec 18) := do
  let s := arg_
  if ((hex_bits_backwards_matches (18, s)) : Bool)
  then (pure (hex_bits_backwards (18, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_18_forwards_matches (arg_ : (BitVec 18)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (18, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_18_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (18, s)) : Bool)
  then true
  else false

def hex_bits_19_forwards (arg_ : (BitVec 19)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (19, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_19_backwards (arg_ : String) : SailM (BitVec 19) := do
  let s := arg_
  if ((hex_bits_backwards_matches (19, s)) : Bool)
  then (pure (hex_bits_backwards (19, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_19_forwards_matches (arg_ : (BitVec 19)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (19, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_19_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (19, s)) : Bool)
  then true
  else false

def hex_bits_20_forwards (arg_ : (BitVec 20)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (20, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_20_backwards (arg_ : String) : SailM (BitVec 20) := do
  let s := arg_
  if ((hex_bits_backwards_matches (20, s)) : Bool)
  then (pure (hex_bits_backwards (20, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_20_forwards_matches (arg_ : (BitVec 20)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (20, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_20_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (20, s)) : Bool)
  then true
  else false

def hex_bits_21_forwards (arg_ : (BitVec 21)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (21, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_21_backwards (arg_ : String) : SailM (BitVec 21) := do
  let s := arg_
  if ((hex_bits_backwards_matches (21, s)) : Bool)
  then (pure (hex_bits_backwards (21, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_21_forwards_matches (arg_ : (BitVec 21)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (21, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_21_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (21, s)) : Bool)
  then true
  else false

def hex_bits_22_forwards (arg_ : (BitVec 22)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (22, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_22_backwards (arg_ : String) : SailM (BitVec 22) := do
  let s := arg_
  if ((hex_bits_backwards_matches (22, s)) : Bool)
  then (pure (hex_bits_backwards (22, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_22_forwards_matches (arg_ : (BitVec 22)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (22, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_22_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (22, s)) : Bool)
  then true
  else false

def hex_bits_23_forwards (arg_ : (BitVec 23)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (23, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_23_backwards (arg_ : String) : SailM (BitVec 23) := do
  let s := arg_
  if ((hex_bits_backwards_matches (23, s)) : Bool)
  then (pure (hex_bits_backwards (23, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_23_forwards_matches (arg_ : (BitVec 23)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (23, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_23_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (23, s)) : Bool)
  then true
  else false

def hex_bits_24_forwards (arg_ : (BitVec 24)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (24, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_24_backwards (arg_ : String) : SailM (BitVec 24) := do
  let s := arg_
  if ((hex_bits_backwards_matches (24, s)) : Bool)
  then (pure (hex_bits_backwards (24, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_24_forwards_matches (arg_ : (BitVec 24)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (24, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_24_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (24, s)) : Bool)
  then true
  else false

def hex_bits_25_forwards (arg_ : (BitVec 25)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (25, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_25_backwards (arg_ : String) : SailM (BitVec 25) := do
  let s := arg_
  if ((hex_bits_backwards_matches (25, s)) : Bool)
  then (pure (hex_bits_backwards (25, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_25_forwards_matches (arg_ : (BitVec 25)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (25, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_25_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (25, s)) : Bool)
  then true
  else false

def hex_bits_26_forwards (arg_ : (BitVec 26)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (26, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_26_backwards (arg_ : String) : SailM (BitVec 26) := do
  let s := arg_
  if ((hex_bits_backwards_matches (26, s)) : Bool)
  then (pure (hex_bits_backwards (26, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_26_forwards_matches (arg_ : (BitVec 26)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (26, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_26_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (26, s)) : Bool)
  then true
  else false

def hex_bits_27_forwards (arg_ : (BitVec 27)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (27, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_27_backwards (arg_ : String) : SailM (BitVec 27) := do
  let s := arg_
  if ((hex_bits_backwards_matches (27, s)) : Bool)
  then (pure (hex_bits_backwards (27, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_27_forwards_matches (arg_ : (BitVec 27)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (27, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_27_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (27, s)) : Bool)
  then true
  else false

def hex_bits_28_forwards (arg_ : (BitVec 28)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (28, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_28_backwards (arg_ : String) : SailM (BitVec 28) := do
  let s := arg_
  if ((hex_bits_backwards_matches (28, s)) : Bool)
  then (pure (hex_bits_backwards (28, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_28_forwards_matches (arg_ : (BitVec 28)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (28, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_28_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (28, s)) : Bool)
  then true
  else false

def hex_bits_29_forwards (arg_ : (BitVec 29)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (29, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_29_backwards (arg_ : String) : SailM (BitVec 29) := do
  let s := arg_
  if ((hex_bits_backwards_matches (29, s)) : Bool)
  then (pure (hex_bits_backwards (29, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_29_forwards_matches (arg_ : (BitVec 29)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (29, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_29_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (29, s)) : Bool)
  then true
  else false

def hex_bits_30_forwards (arg_ : (BitVec 30)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (30, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_30_backwards (arg_ : String) : SailM (BitVec 30) := do
  let s := arg_
  if ((hex_bits_backwards_matches (30, s)) : Bool)
  then (pure (hex_bits_backwards (30, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_30_forwards_matches (arg_ : (BitVec 30)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (30, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_30_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (30, s)) : Bool)
  then true
  else false

def hex_bits_31_forwards (arg_ : (BitVec 31)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (31, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_31_backwards (arg_ : String) : SailM (BitVec 31) := do
  let s := arg_
  if ((hex_bits_backwards_matches (31, s)) : Bool)
  then (pure (hex_bits_backwards (31, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_31_forwards_matches (arg_ : (BitVec 31)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (31, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_31_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (31, s)) : Bool)
  then true
  else false

def hex_bits_32_forwards (arg_ : (BitVec 32)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (32, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_32_backwards (arg_ : String) : SailM (BitVec 32) := do
  let s := arg_
  if ((hex_bits_backwards_matches (32, s)) : Bool)
  then (pure (hex_bits_backwards (32, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_32_forwards_matches (arg_ : (BitVec 32)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (32, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_32_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (32, s)) : Bool)
  then true
  else false

def hex_bits_33_forwards (arg_ : (BitVec 33)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (33, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_33_backwards (arg_ : String) : SailM (BitVec 33) := do
  let s := arg_
  if ((hex_bits_backwards_matches (33, s)) : Bool)
  then (pure (hex_bits_backwards (33, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_33_forwards_matches (arg_ : (BitVec 33)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (33, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_33_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (33, s)) : Bool)
  then true
  else false

def hex_bits_34_forwards (arg_ : (BitVec 34)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (34, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_34_backwards (arg_ : String) : SailM (BitVec 34) := do
  let s := arg_
  if ((hex_bits_backwards_matches (34, s)) : Bool)
  then (pure (hex_bits_backwards (34, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_34_forwards_matches (arg_ : (BitVec 34)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (34, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_34_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (34, s)) : Bool)
  then true
  else false

def hex_bits_35_forwards (arg_ : (BitVec 35)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (35, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_35_backwards (arg_ : String) : SailM (BitVec 35) := do
  let s := arg_
  if ((hex_bits_backwards_matches (35, s)) : Bool)
  then (pure (hex_bits_backwards (35, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_35_forwards_matches (arg_ : (BitVec 35)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (35, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_35_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (35, s)) : Bool)
  then true
  else false

def hex_bits_36_forwards (arg_ : (BitVec 36)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (36, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_36_backwards (arg_ : String) : SailM (BitVec 36) := do
  let s := arg_
  if ((hex_bits_backwards_matches (36, s)) : Bool)
  then (pure (hex_bits_backwards (36, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_36_forwards_matches (arg_ : (BitVec 36)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (36, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_36_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (36, s)) : Bool)
  then true
  else false

def hex_bits_37_forwards (arg_ : (BitVec 37)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (37, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_37_backwards (arg_ : String) : SailM (BitVec 37) := do
  let s := arg_
  if ((hex_bits_backwards_matches (37, s)) : Bool)
  then (pure (hex_bits_backwards (37, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_37_forwards_matches (arg_ : (BitVec 37)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (37, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_37_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (37, s)) : Bool)
  then true
  else false

def hex_bits_38_forwards (arg_ : (BitVec 38)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (38, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_38_backwards (arg_ : String) : SailM (BitVec 38) := do
  let s := arg_
  if ((hex_bits_backwards_matches (38, s)) : Bool)
  then (pure (hex_bits_backwards (38, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_38_forwards_matches (arg_ : (BitVec 38)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (38, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_38_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (38, s)) : Bool)
  then true
  else false

def hex_bits_39_forwards (arg_ : (BitVec 39)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (39, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_39_backwards (arg_ : String) : SailM (BitVec 39) := do
  let s := arg_
  if ((hex_bits_backwards_matches (39, s)) : Bool)
  then (pure (hex_bits_backwards (39, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_39_forwards_matches (arg_ : (BitVec 39)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (39, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_39_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (39, s)) : Bool)
  then true
  else false

def hex_bits_40_forwards (arg_ : (BitVec 40)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (40, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_40_backwards (arg_ : String) : SailM (BitVec 40) := do
  let s := arg_
  if ((hex_bits_backwards_matches (40, s)) : Bool)
  then (pure (hex_bits_backwards (40, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_40_forwards_matches (arg_ : (BitVec 40)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (40, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_40_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (40, s)) : Bool)
  then true
  else false

def hex_bits_41_forwards (arg_ : (BitVec 41)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (41, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_41_backwards (arg_ : String) : SailM (BitVec 41) := do
  let s := arg_
  if ((hex_bits_backwards_matches (41, s)) : Bool)
  then (pure (hex_bits_backwards (41, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_41_forwards_matches (arg_ : (BitVec 41)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (41, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_41_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (41, s)) : Bool)
  then true
  else false

def hex_bits_42_forwards (arg_ : (BitVec 42)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (42, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_42_backwards (arg_ : String) : SailM (BitVec 42) := do
  let s := arg_
  if ((hex_bits_backwards_matches (42, s)) : Bool)
  then (pure (hex_bits_backwards (42, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_42_forwards_matches (arg_ : (BitVec 42)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (42, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_42_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (42, s)) : Bool)
  then true
  else false

def hex_bits_43_forwards (arg_ : (BitVec 43)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (43, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_43_backwards (arg_ : String) : SailM (BitVec 43) := do
  let s := arg_
  if ((hex_bits_backwards_matches (43, s)) : Bool)
  then (pure (hex_bits_backwards (43, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_43_forwards_matches (arg_ : (BitVec 43)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (43, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_43_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (43, s)) : Bool)
  then true
  else false

def hex_bits_44_forwards (arg_ : (BitVec 44)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (44, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_44_backwards (arg_ : String) : SailM (BitVec 44) := do
  let s := arg_
  if ((hex_bits_backwards_matches (44, s)) : Bool)
  then (pure (hex_bits_backwards (44, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_44_forwards_matches (arg_ : (BitVec 44)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (44, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_44_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (44, s)) : Bool)
  then true
  else false

def hex_bits_45_forwards (arg_ : (BitVec 45)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (45, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_45_backwards (arg_ : String) : SailM (BitVec 45) := do
  let s := arg_
  if ((hex_bits_backwards_matches (45, s)) : Bool)
  then (pure (hex_bits_backwards (45, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_45_forwards_matches (arg_ : (BitVec 45)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (45, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_45_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (45, s)) : Bool)
  then true
  else false

def hex_bits_46_forwards (arg_ : (BitVec 46)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (46, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_46_backwards (arg_ : String) : SailM (BitVec 46) := do
  let s := arg_
  if ((hex_bits_backwards_matches (46, s)) : Bool)
  then (pure (hex_bits_backwards (46, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_46_forwards_matches (arg_ : (BitVec 46)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (46, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_46_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (46, s)) : Bool)
  then true
  else false

def hex_bits_47_forwards (arg_ : (BitVec 47)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (47, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_47_backwards (arg_ : String) : SailM (BitVec 47) := do
  let s := arg_
  if ((hex_bits_backwards_matches (47, s)) : Bool)
  then (pure (hex_bits_backwards (47, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_47_forwards_matches (arg_ : (BitVec 47)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (47, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_47_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (47, s)) : Bool)
  then true
  else false

def hex_bits_48_forwards (arg_ : (BitVec 48)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (48, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_48_backwards (arg_ : String) : SailM (BitVec 48) := do
  let s := arg_
  if ((hex_bits_backwards_matches (48, s)) : Bool)
  then (pure (hex_bits_backwards (48, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_48_forwards_matches (arg_ : (BitVec 48)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (48, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_48_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (48, s)) : Bool)
  then true
  else false

def hex_bits_49_forwards (arg_ : (BitVec 49)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (49, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_49_backwards (arg_ : String) : SailM (BitVec 49) := do
  let s := arg_
  if ((hex_bits_backwards_matches (49, s)) : Bool)
  then (pure (hex_bits_backwards (49, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_49_forwards_matches (arg_ : (BitVec 49)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (49, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_49_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (49, s)) : Bool)
  then true
  else false

def hex_bits_50_forwards (arg_ : (BitVec 50)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (50, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_50_backwards (arg_ : String) : SailM (BitVec 50) := do
  let s := arg_
  if ((hex_bits_backwards_matches (50, s)) : Bool)
  then (pure (hex_bits_backwards (50, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_50_forwards_matches (arg_ : (BitVec 50)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (50, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_50_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (50, s)) : Bool)
  then true
  else false

def hex_bits_51_forwards (arg_ : (BitVec 51)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (51, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_51_backwards (arg_ : String) : SailM (BitVec 51) := do
  let s := arg_
  if ((hex_bits_backwards_matches (51, s)) : Bool)
  then (pure (hex_bits_backwards (51, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_51_forwards_matches (arg_ : (BitVec 51)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (51, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_51_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (51, s)) : Bool)
  then true
  else false

def hex_bits_52_forwards (arg_ : (BitVec 52)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (52, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_52_backwards (arg_ : String) : SailM (BitVec 52) := do
  let s := arg_
  if ((hex_bits_backwards_matches (52, s)) : Bool)
  then (pure (hex_bits_backwards (52, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_52_forwards_matches (arg_ : (BitVec 52)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (52, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_52_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (52, s)) : Bool)
  then true
  else false

def hex_bits_53_forwards (arg_ : (BitVec 53)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (53, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_53_backwards (arg_ : String) : SailM (BitVec 53) := do
  let s := arg_
  if ((hex_bits_backwards_matches (53, s)) : Bool)
  then (pure (hex_bits_backwards (53, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_53_forwards_matches (arg_ : (BitVec 53)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (53, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_53_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (53, s)) : Bool)
  then true
  else false

def hex_bits_54_forwards (arg_ : (BitVec 54)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (54, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_54_backwards (arg_ : String) : SailM (BitVec 54) := do
  let s := arg_
  if ((hex_bits_backwards_matches (54, s)) : Bool)
  then (pure (hex_bits_backwards (54, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_54_forwards_matches (arg_ : (BitVec 54)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (54, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_54_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (54, s)) : Bool)
  then true
  else false

def hex_bits_55_forwards (arg_ : (BitVec 55)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (55, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_55_backwards (arg_ : String) : SailM (BitVec 55) := do
  let s := arg_
  if ((hex_bits_backwards_matches (55, s)) : Bool)
  then (pure (hex_bits_backwards (55, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_55_forwards_matches (arg_ : (BitVec 55)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (55, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_55_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (55, s)) : Bool)
  then true
  else false

def hex_bits_56_forwards (arg_ : (BitVec 56)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (56, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_56_backwards (arg_ : String) : SailM (BitVec 56) := do
  let s := arg_
  if ((hex_bits_backwards_matches (56, s)) : Bool)
  then (pure (hex_bits_backwards (56, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_56_forwards_matches (arg_ : (BitVec 56)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (56, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_56_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (56, s)) : Bool)
  then true
  else false

def hex_bits_57_forwards (arg_ : (BitVec 57)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (57, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_57_backwards (arg_ : String) : SailM (BitVec 57) := do
  let s := arg_
  if ((hex_bits_backwards_matches (57, s)) : Bool)
  then (pure (hex_bits_backwards (57, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_57_forwards_matches (arg_ : (BitVec 57)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (57, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_57_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (57, s)) : Bool)
  then true
  else false

def hex_bits_58_forwards (arg_ : (BitVec 58)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (58, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_58_backwards (arg_ : String) : SailM (BitVec 58) := do
  let s := arg_
  if ((hex_bits_backwards_matches (58, s)) : Bool)
  then (pure (hex_bits_backwards (58, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_58_forwards_matches (arg_ : (BitVec 58)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (58, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_58_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (58, s)) : Bool)
  then true
  else false

def hex_bits_59_forwards (arg_ : (BitVec 59)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (59, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_59_backwards (arg_ : String) : SailM (BitVec 59) := do
  let s := arg_
  if ((hex_bits_backwards_matches (59, s)) : Bool)
  then (pure (hex_bits_backwards (59, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_59_forwards_matches (arg_ : (BitVec 59)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (59, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_59_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (59, s)) : Bool)
  then true
  else false

def hex_bits_60_forwards (arg_ : (BitVec 60)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (60, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_60_backwards (arg_ : String) : SailM (BitVec 60) := do
  let s := arg_
  if ((hex_bits_backwards_matches (60, s)) : Bool)
  then (pure (hex_bits_backwards (60, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_60_forwards_matches (arg_ : (BitVec 60)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (60, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_60_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (60, s)) : Bool)
  then true
  else false

def hex_bits_61_forwards (arg_ : (BitVec 61)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (61, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_61_backwards (arg_ : String) : SailM (BitVec 61) := do
  let s := arg_
  if ((hex_bits_backwards_matches (61, s)) : Bool)
  then (pure (hex_bits_backwards (61, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_61_forwards_matches (arg_ : (BitVec 61)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (61, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_61_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (61, s)) : Bool)
  then true
  else false

def hex_bits_62_forwards (arg_ : (BitVec 62)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (62, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_62_backwards (arg_ : String) : SailM (BitVec 62) := do
  let s := arg_
  if ((hex_bits_backwards_matches (62, s)) : Bool)
  then (pure (hex_bits_backwards (62, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_62_forwards_matches (arg_ : (BitVec 62)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (62, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_62_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (62, s)) : Bool)
  then true
  else false

def hex_bits_63_forwards (arg_ : (BitVec 63)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (63, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_63_backwards (arg_ : String) : SailM (BitVec 63) := do
  let s := arg_
  if ((hex_bits_backwards_matches (63, s)) : Bool)
  then (pure (hex_bits_backwards (63, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_63_forwards_matches (arg_ : (BitVec 63)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (63, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_63_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (63, s)) : Bool)
  then true
  else false

def hex_bits_64_forwards (arg_ : (BitVec 64)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (64, s) => (some s)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_64_backwards (arg_ : String) : SailM (BitVec 64) := do
  let s := arg_
  if ((hex_bits_backwards_matches (64, s)) : Bool)
  then (pure (hex_bits_backwards (64, s)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_64_forwards_matches (arg_ : (BitVec 64)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (if ((hex_bits_forwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_forwards mapping0_) with
      | (64, s) => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_64_backwards_matches (arg_ : String) : Bool :=
  let s := arg_
  if ((hex_bits_backwards_matches (64, s)) : Bool)
  then true
  else false

