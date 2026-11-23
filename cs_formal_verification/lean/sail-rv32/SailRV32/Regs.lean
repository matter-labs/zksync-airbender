import SailRV32.Flow
import SailRV32.Arith
import SailRV32.Prelude
import SailRV32.Xlen
import SailRV32.PlatformConfig
import SailRV32.Callbacks
import SailRV32.RegType

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

def encdec_reg_backwards_matches (arg_ : (BitVec 5)) : Bool :=
  let r := arg_
  if (((not base_E_enabled) || ((BitVec.access r 4) == 0#1)) : Bool)
  then true
  else false

def encdec_creg_forwards (arg_ : cregidx) : (BitVec 3) :=
  match arg_ with
  | .Cregidx r => r

def encdec_creg_backwards (arg_ : (BitVec 3)) : cregidx :=
  match arg_ with
  | r => (Cregidx r)

def encdec_creg_forwards_matches (arg_ : cregidx) : Bool :=
  match arg_ with
  | .Cregidx r => true

def encdec_creg_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match arg_ with
  | r => true

def reg_abi_name_raw_backwards (arg_ : String) : SailM (BitVec 5) := do
  match arg_ with
  | "zero" => (pure 0b00000#5)
  | "ra" => (pure 0b00001#5)
  | "sp" => (pure 0b00010#5)
  | "gp" => (pure 0b00011#5)
  | "tp" => (pure 0b00100#5)
  | "t0" => (pure 0b00101#5)
  | "t1" => (pure 0b00110#5)
  | "t2" => (pure 0b00111#5)
  | "s0" => (pure 0b01000#5)
  | "fp" => (pure 0b01000#5)
  | "s1" => (pure 0b01001#5)
  | "a0" => (pure 0b01010#5)
  | "a1" => (pure 0b01011#5)
  | "a2" => (pure 0b01100#5)
  | "a3" => (pure 0b01101#5)
  | "a4" => (pure 0b01110#5)
  | "a5" => (pure 0b01111#5)
  | "a6" => (pure 0b10000#5)
  | "a7" => (pure 0b10001#5)
  | "s2" => (pure 0b10010#5)
  | "s3" => (pure 0b10011#5)
  | "s4" => (pure 0b10100#5)
  | "s5" => (pure 0b10101#5)
  | "s6" => (pure 0b10110#5)
  | "s7" => (pure 0b10111#5)
  | "s8" => (pure 0b11000#5)
  | "s9" => (pure 0b11001#5)
  | "s10" => (pure 0b11010#5)
  | "s11" => (pure 0b11011#5)
  | "t3" => (pure 0b11100#5)
  | "t4" => (pure 0b11101#5)
  | "t5" => (pure 0b11110#5)
  | "t6" => (pure 0b11111#5)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def reg_abi_name_raw_forwards_matches (arg_ : (BitVec 5)) : Bool :=
  match arg_ with
  | 0b00000 => true
  | 0b00001 => true
  | 0b00010 => true
  | 0b00011 => true
  | 0b00100 => true
  | 0b00101 => true
  | 0b00110 => true
  | 0b00111 => true
  | 0b01000 => true
  | 0b01000 => true
  | 0b01001 => true
  | 0b01010 => true
  | 0b01011 => true
  | 0b01100 => true
  | 0b01101 => true
  | 0b01110 => true
  | 0b01111 => true
  | 0b10000 => true
  | 0b10001 => true
  | 0b10010 => true
  | 0b10011 => true
  | 0b10100 => true
  | 0b10101 => true
  | 0b10110 => true
  | 0b10111 => true
  | 0b11000 => true
  | 0b11001 => true
  | 0b11010 => true
  | 0b11011 => true
  | 0b11100 => true
  | 0b11101 => true
  | 0b11110 => true
  | 0b11111 => true
  | _ => false

def reg_abi_name_raw_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "zero" => true
  | "ra" => true
  | "sp" => true
  | "gp" => true
  | "tp" => true
  | "t0" => true
  | "t1" => true
  | "t2" => true
  | "s0" => true
  | "fp" => true
  | "s1" => true
  | "a0" => true
  | "a1" => true
  | "a2" => true
  | "a3" => true
  | "a4" => true
  | "a5" => true
  | "a6" => true
  | "a7" => true
  | "s2" => true
  | "s3" => true
  | "s4" => true
  | "s5" => true
  | "s6" => true
  | "s7" => true
  | "s8" => true
  | "s9" => true
  | "s10" => true
  | "s11" => true
  | "t3" => true
  | "t4" => true
  | "t5" => true
  | "t6" => true
  | _ => false

def reg_arch_name_raw_backwards (arg_ : String) : SailM (BitVec 5) := do
  match arg_ with
  | "x0" => (pure 0b00000#5)
  | "x1" => (pure 0b00001#5)
  | "x2" => (pure 0b00010#5)
  | "x3" => (pure 0b00011#5)
  | "x4" => (pure 0b00100#5)
  | "x5" => (pure 0b00101#5)
  | "x6" => (pure 0b00110#5)
  | "x7" => (pure 0b00111#5)
  | "x8" => (pure 0b01000#5)
  | "x9" => (pure 0b01001#5)
  | "x10" => (pure 0b01010#5)
  | "x11" => (pure 0b01011#5)
  | "x12" => (pure 0b01100#5)
  | "x13" => (pure 0b01101#5)
  | "x14" => (pure 0b01110#5)
  | "x15" => (pure 0b01111#5)
  | "x16" => (pure 0b10000#5)
  | "x17" => (pure 0b10001#5)
  | "x18" => (pure 0b10010#5)
  | "x19" => (pure 0b10011#5)
  | "x20" => (pure 0b10100#5)
  | "x21" => (pure 0b10101#5)
  | "x22" => (pure 0b10110#5)
  | "x23" => (pure 0b10111#5)
  | "x24" => (pure 0b11000#5)
  | "x25" => (pure 0b11001#5)
  | "x26" => (pure 0b11010#5)
  | "x27" => (pure 0b11011#5)
  | "x28" => (pure 0b11100#5)
  | "x29" => (pure 0b11101#5)
  | "x30" => (pure 0b11110#5)
  | "x31" => (pure 0b11111#5)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def reg_arch_name_raw_forwards_matches (arg_ : (BitVec 5)) : Bool :=
  match arg_ with
  | 0b00000 => true
  | 0b00001 => true
  | 0b00010 => true
  | 0b00011 => true
  | 0b00100 => true
  | 0b00101 => true
  | 0b00110 => true
  | 0b00111 => true
  | 0b01000 => true
  | 0b01001 => true
  | 0b01010 => true
  | 0b01011 => true
  | 0b01100 => true
  | 0b01101 => true
  | 0b01110 => true
  | 0b01111 => true
  | 0b10000 => true
  | 0b10001 => true
  | 0b10010 => true
  | 0b10011 => true
  | 0b10100 => true
  | 0b10101 => true
  | 0b10110 => true
  | 0b10111 => true
  | 0b11000 => true
  | 0b11001 => true
  | 0b11010 => true
  | 0b11011 => true
  | 0b11100 => true
  | 0b11101 => true
  | 0b11110 => true
  | 0b11111 => true
  | _ => false

def reg_arch_name_raw_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "x0" => true
  | "x1" => true
  | "x2" => true
  | "x3" => true
  | "x4" => true
  | "x5" => true
  | "x6" => true
  | "x7" => true
  | "x8" => true
  | "x9" => true
  | "x10" => true
  | "x11" => true
  | "x12" => true
  | "x13" => true
  | "x14" => true
  | "x15" => true
  | "x16" => true
  | "x17" => true
  | "x18" => true
  | "x19" => true
  | "x20" => true
  | "x21" => true
  | "x22" => true
  | "x23" => true
  | "x24" => true
  | "x25" => true
  | "x26" => true
  | "x27" => true
  | "x28" => true
  | "x29" => true
  | "x30" => true
  | "x31" => true
  | _ => false

def reg_name_backwards (arg_ : String) : SailM regidx := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    if ((reg_abi_name_raw_backwards_matches mapping0_) : Bool)
    then
      (do
        match (← (reg_abi_name_raw_backwards mapping0_)) with
        | i => (pure (some (← (encdec_reg_backwards i)))))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let mapping1_ := head_exp_
        if ((reg_arch_name_raw_backwards_matches mapping1_) : Bool)
        then
          (do
            match (← (reg_arch_name_raw_backwards mapping1_)) with
            | i => (pure (some (← (encdec_reg_backwards i)))))
        else (pure none)) with
      | .some result => (pure result)
      | _ =>
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))

def reg_name_forwards_matches (arg_ : regidx) : Bool :=
  let head_exp_ := arg_
  match (let mapping0_ := head_exp_
  if ((encdec_reg_forwards_matches mapping0_) : Bool)
  then
    (let i := (encdec_reg_forwards mapping0_)
    if ((get_config_use_abi_names ()) : Bool)
    then (some true)
    else none)
  else none) with
  | .some result => result
  | none =>
    (match (let mapping1_ := head_exp_
    if ((encdec_reg_forwards_matches mapping1_) : Bool)
    then
      (let i := (encdec_reg_forwards mapping1_)
      if ((not (get_config_use_abi_names ())) : Bool)
      then (some true)
      else none)
    else none) with
    | .some result => result
    | none =>
      (match head_exp_ with
      | _ => false))

def reg_name_backwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    if ((reg_abi_name_raw_backwards_matches mapping0_) : Bool)
    then
      (do
        match (← (reg_abi_name_raw_backwards mapping0_)) with
        | i => (pure (some true)))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let mapping1_ := head_exp_
        if ((reg_arch_name_raw_backwards_matches mapping1_) : Bool)
        then
          (do
            match (← (reg_arch_name_raw_backwards mapping1_)) with
            | i => (pure (some true)))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (match head_exp_ with
        | _ => (pure false)))

def sp_reg_name_backwards (arg_ : String) : SailM Unit := do
  match arg_ with
  | "sp" => (pure ())
  | "x2" => (pure ())
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def sp_reg_name_forwards_matches (arg_ : Unit) : Bool :=
  match arg_ with
  | () =>
    (if ((get_config_use_abi_names ()) : Bool)
    then true
    else
      (if ((not (get_config_use_abi_names ())) : Bool)
      then true
      else false))

def sp_reg_name_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "sp" => true
  | "x2" => true
  | _ => false

def creg_name_backwards (arg_ : String) : SailM cregidx := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    if ((← (reg_name_backwards_matches mapping0_)) : Bool)
    then
      (do
        let head_exp_ ← do (reg_name_backwards mapping0_)
        match (let mapping1_ := head_exp_
        if ((encdec_reg_forwards_matches mapping1_) : Bool)
        then
          (let v__0 := (encdec_reg_forwards mapping1_)
          if (((Sail.BitVec.extractLsb v__0 4 3) == (0b01#2 : (BitVec 2))) : Bool)
          then
            (let i : (BitVec 3) := (Sail.BitVec.extractLsb v__0 2 0)
            (some (some (Cregidx i))))
          else none)
        else none) with
        | .some result => (pure result)
        | none =>
          (match head_exp_ with
          | _ => (pure none)))
    else (pure none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def creg_name_forwards_matches (arg_ : cregidx) : Bool :=
  match arg_ with
  | .Cregidx i => true

def creg_name_backwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    if ((← (reg_name_backwards_matches mapping0_)) : Bool)
    then
      (do
        let head_exp_ ← do (reg_name_backwards mapping0_)
        match (let mapping1_ := head_exp_
        if ((encdec_reg_forwards_matches mapping1_) : Bool)
        then
          (let v__2 := (encdec_reg_forwards mapping1_)
          if (((Sail.BitVec.extractLsb v__2 4 3) == (0b01#2 : (BitVec 2))) : Bool)
          then (some (some true))
          else none)
        else none) with
        | .some result => (pure result)
        | none =>
          (match head_exp_ with
          | _ => (pure none)))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def rX_pair_bits (i : regidx) : SailM (BitVec (32 * 2)) := do
  if ((bne i zreg) : Bool)
  then (pure ((← (rX_bits (regidx_offset_range i 1))) +++ (← (rX_bits i))))
  else (pure (zeros (n := (32 *i 2))))

def wX_pair_bits (i : regidx) (data : (BitVec (32 * 2))) : SailM Unit := do
  if ((bne i zreg) : Bool)
  then
    (do
      (wX_bits i (Sail.BitVec.extractLsb data (xlen -i 1) 0))
      (wX_bits (regidx_offset_range i 1) (Sail.BitVec.extractLsb data ((xlen *i 2) -i 1) xlen)))
  else (pure ())

