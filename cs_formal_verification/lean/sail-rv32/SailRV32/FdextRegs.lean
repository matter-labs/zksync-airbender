import SailRV32.SailRV32
import SailRV32.Flow
import SailRV32.Arith
import SailRV32.Prelude
import SailRV32.Xlen
import SailRV32.Flen
import SailRV32.PlatformConfig
import SailRV32.Types
import SailRV32.Callbacks
import SailRV32.Regs
import SailRV32.SysRegs
import SailRV32.FregType

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

/-- Type quantifiers: n : Nat, n ≥ 0, List.elem n [16, 32, 64, 128] -/
def canonical_NaN {n : _} : (BitVec n) :=
  match n with
  | 16 => (0#1 +++ ((ones (n := 5)) +++ (1#1 +++ (zeros (n := 9)))))
  | 32 => (0#1 +++ ((ones (n := 8)) +++ (1#1 +++ (zeros (n := 22)))))
  | 64 => (0#1 +++ ((ones (n := 11)) +++ (1#1 +++ (zeros (n := 51)))))
  | _ => (0#1 +++ ((ones (n := 15)) +++ (1#1 +++ (zeros (n := 111)))))

def canonical_NaN_BF16 : (BitVec 16) := 0x7FC0#16

def canonical_NaN_H (_ : Unit) : (BitVec 16) :=
  (canonical_NaN (n := 16))

def canonical_NaN_S (_ : Unit) : (BitVec 32) :=
  (canonical_NaN (n := 32))

def canonical_NaN_D (_ : Unit) : (BitVec 64) :=
  (canonical_NaN (n := 64))

def canonical_NaN_Q (_ : Unit) : (BitVec 128) :=
  (canonical_NaN (n := 128))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, n : Nat, n ≥ 0, k_n ≤ n -/
def nan_box {n : _} (x : (BitVec k_n)) : (BitVec n) :=
  ((ones (n := (n -i (Sail.BitVec.length x)))) +++ x)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, m : Nat, m ≥ 0, List.elem m [16, 32, 64, 128] ∧
  k_n ≥ m -/
def nan_unbox {m : _} (x : (BitVec k_n)) : (BitVec m) :=
  if (((Sail.BitVec.length x) == m) : Bool)
  then x
  else
    (if (((Sail.BitVec.extractLsb x ((Sail.BitVec.length x) -i 1) m) == (ones
           (n := ((((Sail.BitVec.length x) -i 1) -i m) +i 1)))) : Bool)
    then (Sail.BitVec.extractLsb x (m -i 1) 0)
    else (canonical_NaN (n := m)))

def cfregidx_to_fregidx (app_0 : cfregidx) : fregidx :=
  let .Cfregidx b := app_0
  (Fregidx (0b01#2 +++ b))

def encdec_cfreg_forwards (arg_ : cfregidx) : (BitVec 3) :=
  match arg_ with
  | .Cfregidx r => r

def encdec_cfreg_backwards (arg_ : (BitVec 3)) : cfregidx :=
  match arg_ with
  | r => (Cfregidx r)

def encdec_cfreg_forwards_matches (arg_ : cfregidx) : Bool :=
  match arg_ with
  | .Cfregidx r => true

def encdec_cfreg_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match arg_ with
  | r => true

def encdec_freg_backwards (arg_ : (BitVec 5)) : fregidx :=
  match arg_ with
  | r => (Fregidx r)

def encdec_freg_forwards_matches (arg_ : fregidx) : Bool :=
  match arg_ with
  | .Fregidx r => true

def encdec_freg_backwards_matches (arg_ : (BitVec 5)) : Bool :=
  match arg_ with
  | r => true

def freg_write_callback (x_0 : fregidx) (x_1 : (BitVec (if ( true  : Bool) then 8 else 4 * 8))) : Unit :=
  ()

def dirty_fd_context (_ : Unit) : SailM Unit := do
  «assert» (hartSupports Ext_F) "extensions/FD/fdext_regs.sail:111.28-111.29"
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 14 13
    (extStatus_map_forwards Dirty))
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) (32 -i 1) (32 -i 1) 1#1)
  (long_csr_write_callback "mstatus" "mstatush" (← (read_mstatus ())))
  if ((← (inVirtualPrivilege ())) : Bool)
  then
    (do
      writeReg vsstatus (Sail.BitVec.updateSubrange (← readReg vsstatus) 14 13
        (extStatus_map_forwards Dirty))
      writeReg vsstatus (Sail.BitVec.updateSubrange (← readReg vsstatus) (32 -i 1) (32 -i 1) 1#1)
      (csr_name_write_callback "vsstatus"
        (Sail.BitVec.extractLsb (← readReg vsstatus) (xlen -i 1) 0)))
  else (pure ())

def dirty_fd_context_if_present (_ : Unit) : SailM Unit := do
  «assert» (neq_bool (hartSupports Ext_F) (hartSupports Ext_Zfinx)) "extensions/FD/fdext_regs.sail:125.55-125.56"
  if ((hartSupports Ext_F) : Bool)
  then (dirty_fd_context ())
  else (pure ())

def rF (app_0 : fregno) : SailM (BitVec (if ( true  : Bool) then 8 else 4 * 8)) := do
  let .Fregno r := app_0
  «assert» (hartSupports Ext_F) "extensions/FD/fdext_regs.sail:130.28-130.29"
  let v ← (( do
    match r with
    | 0 => readReg f0
    | 1 => readReg f1
    | 2 => readReg f2
    | 3 => readReg f3
    | 4 => readReg f4
    | 5 => readReg f5
    | 6 => readReg f6
    | 7 => readReg f7
    | 8 => readReg f8
    | 9 => readReg f9
    | 10 => readReg f10
    | 11 => readReg f11
    | 12 => readReg f12
    | 13 => readReg f13
    | 14 => readReg f14
    | 15 => readReg f15
    | 16 => readReg f16
    | 17 => readReg f17
    | 18 => readReg f18
    | 19 => readReg f19
    | 20 => readReg f20
    | 21 => readReg f21
    | 22 => readReg f22
    | 23 => readReg f23
    | 24 => readReg f24
    | 25 => readReg f25
    | 26 => readReg f26
    | 27 => readReg f27
    | 28 => readReg f28
    | 29 => readReg f29
    | 30 => readReg f30
    | 31 => readReg f31
    | _ =>
      (do
        «assert» false "invalid floating point register number"
        throw Error.Exit) ) : SailM fregtype )
  (pure (fregval_from_freg v))

def wF (typ_0 : fregno) (in_v : (BitVec (if ( true  : Bool) then 8 else 4 * 8))) : SailM Unit := do
  let .Fregno r : fregno := typ_0
  «assert» (hartSupports Ext_F) "extensions/FD/fdext_regs.sail:171.28-171.29"
  let v := (fregval_into_freg in_v)
  match r with
  | 0 => writeReg f0 v
  | 1 => writeReg f1 v
  | 2 => writeReg f2 v
  | 3 => writeReg f3 v
  | 4 => writeReg f4 v
  | 5 => writeReg f5 v
  | 6 => writeReg f6 v
  | 7 => writeReg f7 v
  | 8 => writeReg f8 v
  | 9 => writeReg f9 v
  | 10 => writeReg f10 v
  | 11 => writeReg f11 v
  | 12 => writeReg f12 v
  | 13 => writeReg f13 v
  | 14 => writeReg f14 v
  | 15 => writeReg f15 v
  | 16 => writeReg f16 v
  | 17 => writeReg f17 v
  | 18 => writeReg f18 v
  | 19 => writeReg f19 v
  | 20 => writeReg f20 v
  | 21 => writeReg f21 v
  | 22 => writeReg f22 v
  | 23 => writeReg f23 v
  | 24 => writeReg f24 v
  | 25 => writeReg f25 v
  | 26 => writeReg f26 v
  | 27 => writeReg f27 v
  | 28 => writeReg f28 v
  | 29 => writeReg f29 v
  | 30 => writeReg f30 v
  | _ => writeReg f31 v
  let _ : Unit := (freg_write_callback (Fregidx (to_bits (l := 5) r)) in_v)
  (dirty_fd_context ())

def rF_bits (app_0 : fregidx) : SailM (BitVec (if ( true  : Bool) then 8 else 4 * 8)) := do
  let .Fregidx i := app_0
  (rF (Fregno (BitVec.toNatInt i)))

def wF_bits (typ_0 : fregidx) (data : (BitVec (if ( true  : Bool) then 8 else 4 * 8))) : SailM Unit := do
  let .Fregidx i : fregidx := typ_0
  (wF (Fregno (BitVec.toNatInt i)) data)

def rF_BF16 (i : fregidx) : SailM (BitVec 16) := do
  let v ← do (rF_bits i)
  if (((Sail.BitVec.extractLsb v (flen -i 1) 16) == (ones (n := ((((8 *i 8) -i 1) -i 16) +i 1)))) : Bool)
  then (pure (Sail.BitVec.extractLsb v 15 0))
  else (pure canonical_NaN_BF16)

def wF_BF16 (i : fregidx) (data : (BitVec 16)) : SailM Unit := do
  (wF_bits i (nan_box (n := (8 *i 8)) data))

def rF_H (i : fregidx) : SailM (BitVec 16) := do
  «assert» (flen ≥b 16) "extensions/FD/fdext_regs.sail:234.19-234.20"
  «assert» ((hartSupports Ext_F) && (not (hartSupports Ext_Zfinx))) "extensions/FD/fdext_regs.sail:235.59-235.60"
  (pure (nan_unbox (m := 16) (← (rF_bits i))))

def wF_H (i : fregidx) (data : (BitVec 16)) : SailM Unit := do
  «assert» (flen ≥b 16) "extensions/FD/fdext_regs.sail:240.19-240.20"
  «assert» ((hartSupports Ext_F) && (not (hartSupports Ext_Zfinx))) "extensions/FD/fdext_regs.sail:241.59-241.60"
  (wF_bits i (nan_box (n := (8 *i 8)) data))

def rF_S (i : fregidx) : SailM (BitVec 32) := do
  «assert» (flen ≥b 32) "extensions/FD/fdext_regs.sail:246.19-246.20"
  «assert» ((hartSupports Ext_F) && (not (hartSupports Ext_Zfinx))) "extensions/FD/fdext_regs.sail:247.59-247.60"
  (pure (nan_unbox (m := 32) (← (rF_bits i))))

def wF_S (i : fregidx) (data : (BitVec 32)) : SailM Unit := do
  «assert» (flen ≥b 32) "extensions/FD/fdext_regs.sail:252.19-252.20"
  «assert» ((hartSupports Ext_F) && (not (hartSupports Ext_Zfinx))) "extensions/FD/fdext_regs.sail:253.59-253.60"
  (wF_bits i (nan_box (n := (8 *i 8)) data))

def rF_D (i : fregidx) : SailM (BitVec 64) := do
  «assert» (flen ≥b 64) "extensions/FD/fdext_regs.sail:258.19-258.20"
  «assert» ((hartSupports Ext_F) && (not (hartSupports Ext_Zfinx))) "extensions/FD/fdext_regs.sail:259.59-259.60"
  (rF_bits i)

def wF_D (i : fregidx) (data : (BitVec 64)) : SailM Unit := do
  «assert» (flen ≥b 64) "extensions/FD/fdext_regs.sail:264.19-264.20"
  «assert» ((hartSupports Ext_F) && (not (hartSupports Ext_Zfinx))) "extensions/FD/fdext_regs.sail:265.59-265.60"
  (wF_bits i data)

def rF_or_X_H (i : fregidx) : SailM (BitVec 16) := do
  «assert» (flen ≥b 16) "extensions/FD/fdext_regs.sail:275.19-275.20"
  «assert» (neq_bool (hartSupports Ext_F) (hartSupports Ext_Zfinx)) "extensions/FD/fdext_regs.sail:276.55-276.56"
  if ((hartSupports Ext_F) : Bool)
  then (rF_H i)
  else (pure (Sail.BitVec.extractLsb (← (rX_bits (fregidx_to_regidx i))) 15 0))

def rF_or_X_S (i : fregidx) : SailM (BitVec 32) := do
  «assert» (flen ≥b 32) "extensions/FD/fdext_regs.sail:283.19-283.20"
  «assert» (neq_bool (hartSupports Ext_F) (hartSupports Ext_Zfinx)) "extensions/FD/fdext_regs.sail:284.55-284.56"
  if ((hartSupports Ext_F) : Bool)
  then (rF_S i)
  else (pure (Sail.BitVec.extractLsb (← (rX_bits (fregidx_to_regidx i))) 31 0))

def rF_or_X_D (i : fregidx) : SailM (BitVec 64) := do
  «assert» (flen ≥b 64) "extensions/FD/fdext_regs.sail:291.19-291.20"
  «assert» (neq_bool (hartSupports Ext_F) (hartSupports Ext_Zfinx)) "extensions/FD/fdext_regs.sail:292.55-292.56"
  if ((hartSupports Ext_F) : Bool)
  then (rF_D i)
  else
    (do
      let ridx := (fregidx_to_regidx i)
      «assert» ((BitVec.access (regidx_bits ridx) 0) == 0#1) "extensions/FD/fdext_regs.sail:299.38-299.39"
      if ((ridx == zreg) : Bool)
      then (pure (zeros (n := 64)))
      else (pure ((← (rX_bits (regidx_offset_range ridx 1))) +++ (← (rX_bits ridx)))))

def wF_or_X_H (i : fregidx) (data : (BitVec 16)) : SailM Unit := do
  «assert» (flen ≥b 16) "extensions/FD/fdext_regs.sail:305.19-305.20"
  «assert» (neq_bool (hartSupports Ext_F) (hartSupports Ext_Zfinx)) "extensions/FD/fdext_regs.sail:306.55-306.56"
  if ((hartSupports Ext_F) : Bool)
  then (wF_H i data)
  else (wX_bits (fregidx_to_regidx i) (sign_extend (m := 32) data))

def wF_or_X_S (i : fregidx) (data : (BitVec 32)) : SailM Unit := do
  «assert» (flen ≥b 32) "extensions/FD/fdext_regs.sail:313.19-313.20"
  «assert» (neq_bool (hartSupports Ext_F) (hartSupports Ext_Zfinx)) "extensions/FD/fdext_regs.sail:314.55-314.56"
  if ((hartSupports Ext_F) : Bool)
  then (wF_S i data)
  else (wX_bits (fregidx_to_regidx i) (sign_extend (m := 32) data))

def wF_or_X_D (i : fregidx) (data : (BitVec 64)) : SailM Unit := do
  «assert» (flen ≥b 64) "extensions/FD/fdext_regs.sail:321.20-321.21"
  «assert» (neq_bool (hartSupports Ext_F) (hartSupports Ext_Zfinx)) "extensions/FD/fdext_regs.sail:322.55-322.56"
  if ((hartSupports Ext_F) : Bool)
  then (wF_D i data)
  else
    (do
      let ridx := (fregidx_to_regidx i)
      «assert» ((BitVec.access (regidx_bits ridx) 0) == 0#1) "extensions/FD/fdext_regs.sail:329.39-329.40"
      if ((bne ridx zreg) : Bool)
      then
        (do
          (wX_bits ridx (Sail.BitVec.extractLsb data 31 0))
          (wX_bits (regidx_offset_range ridx 1) (Sail.BitVec.extractLsb data 63 32)))
      else (pure ()))

def freg_abi_name_raw_backwards (arg_ : String) : SailM (BitVec 5) := do
  match arg_ with
  | "ft0" => (pure 0b00000#5)
  | "ft1" => (pure 0b00001#5)
  | "ft2" => (pure 0b00010#5)
  | "ft3" => (pure 0b00011#5)
  | "ft4" => (pure 0b00100#5)
  | "ft5" => (pure 0b00101#5)
  | "ft6" => (pure 0b00110#5)
  | "ft7" => (pure 0b00111#5)
  | "fs0" => (pure 0b01000#5)
  | "fs1" => (pure 0b01001#5)
  | "fa0" => (pure 0b01010#5)
  | "fa1" => (pure 0b01011#5)
  | "fa2" => (pure 0b01100#5)
  | "fa3" => (pure 0b01101#5)
  | "fa4" => (pure 0b01110#5)
  | "fa5" => (pure 0b01111#5)
  | "fa6" => (pure 0b10000#5)
  | "fa7" => (pure 0b10001#5)
  | "fs2" => (pure 0b10010#5)
  | "fs3" => (pure 0b10011#5)
  | "fs4" => (pure 0b10100#5)
  | "fs5" => (pure 0b10101#5)
  | "fs6" => (pure 0b10110#5)
  | "fs7" => (pure 0b10111#5)
  | "fs8" => (pure 0b11000#5)
  | "fs9" => (pure 0b11001#5)
  | "fs10" => (pure 0b11010#5)
  | "fs11" => (pure 0b11011#5)
  | "ft8" => (pure 0b11100#5)
  | "ft9" => (pure 0b11101#5)
  | "ft10" => (pure 0b11110#5)
  | "ft11" => (pure 0b11111#5)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def freg_abi_name_raw_forwards_matches (arg_ : (BitVec 5)) : Bool :=
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

def freg_abi_name_raw_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "ft0" => true
  | "ft1" => true
  | "ft2" => true
  | "ft3" => true
  | "ft4" => true
  | "ft5" => true
  | "ft6" => true
  | "ft7" => true
  | "fs0" => true
  | "fs1" => true
  | "fa0" => true
  | "fa1" => true
  | "fa2" => true
  | "fa3" => true
  | "fa4" => true
  | "fa5" => true
  | "fa6" => true
  | "fa7" => true
  | "fs2" => true
  | "fs3" => true
  | "fs4" => true
  | "fs5" => true
  | "fs6" => true
  | "fs7" => true
  | "fs8" => true
  | "fs9" => true
  | "fs10" => true
  | "fs11" => true
  | "ft8" => true
  | "ft9" => true
  | "ft10" => true
  | "ft11" => true
  | _ => false

def freg_arch_name_raw_backwards (arg_ : String) : SailM (BitVec 5) := do
  match arg_ with
  | "f0" => (pure 0b00000#5)
  | "f1" => (pure 0b00001#5)
  | "f2" => (pure 0b00010#5)
  | "f3" => (pure 0b00011#5)
  | "f4" => (pure 0b00100#5)
  | "f5" => (pure 0b00101#5)
  | "f6" => (pure 0b00110#5)
  | "f7" => (pure 0b00111#5)
  | "f8" => (pure 0b01000#5)
  | "f9" => (pure 0b01001#5)
  | "f10" => (pure 0b01010#5)
  | "f11" => (pure 0b01011#5)
  | "f12" => (pure 0b01100#5)
  | "f13" => (pure 0b01101#5)
  | "f14" => (pure 0b01110#5)
  | "f15" => (pure 0b01111#5)
  | "f16" => (pure 0b10000#5)
  | "f17" => (pure 0b10001#5)
  | "f18" => (pure 0b10010#5)
  | "f19" => (pure 0b10011#5)
  | "f20" => (pure 0b10100#5)
  | "f21" => (pure 0b10101#5)
  | "f22" => (pure 0b10110#5)
  | "f23" => (pure 0b10111#5)
  | "f24" => (pure 0b11000#5)
  | "f25" => (pure 0b11001#5)
  | "f26" => (pure 0b11010#5)
  | "f27" => (pure 0b11011#5)
  | "f28" => (pure 0b11100#5)
  | "f29" => (pure 0b11101#5)
  | "f30" => (pure 0b11110#5)
  | "f31" => (pure 0b11111#5)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def freg_arch_name_raw_forwards_matches (arg_ : (BitVec 5)) : Bool :=
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

def freg_arch_name_raw_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "f0" => true
  | "f1" => true
  | "f2" => true
  | "f3" => true
  | "f4" => true
  | "f5" => true
  | "f6" => true
  | "f7" => true
  | "f8" => true
  | "f9" => true
  | "f10" => true
  | "f11" => true
  | "f12" => true
  | "f13" => true
  | "f14" => true
  | "f15" => true
  | "f16" => true
  | "f17" => true
  | "f18" => true
  | "f19" => true
  | "f20" => true
  | "f21" => true
  | "f22" => true
  | "f23" => true
  | "f24" => true
  | "f25" => true
  | "f26" => true
  | "f27" => true
  | "f28" => true
  | "f29" => true
  | "f30" => true
  | "f31" => true
  | _ => false

def freg_name_backwards (arg_ : String) : SailM fregidx := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    if ((freg_abi_name_raw_backwards_matches mapping0_) : Bool)
    then
      (do
        match (← (freg_abi_name_raw_backwards mapping0_)) with
        | i => (pure (some (Fregidx i))))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let mapping1_ := head_exp_
        if ((freg_arch_name_raw_backwards_matches mapping1_) : Bool)
        then
          (do
            match (← (freg_arch_name_raw_backwards mapping1_)) with
            | i => (pure (some (Fregidx i))))
        else (pure none)) with
      | .some result => (pure result)
      | _ =>
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))

def freg_name_forwards_matches (arg_ : fregidx) : Bool :=
  match arg_ with
  | .Fregidx i =>
    (if ((get_config_use_abi_names ()) : Bool)
    then true
    else
      (if ((not (get_config_use_abi_names ())) : Bool)
      then true
      else false))

def freg_name_backwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    if ((freg_abi_name_raw_backwards_matches mapping0_) : Bool)
    then
      (do
        match (← (freg_abi_name_raw_backwards mapping0_)) with
        | i => (pure (some true)))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let mapping1_ := head_exp_
        if ((freg_arch_name_raw_backwards_matches mapping1_) : Bool)
        then
          (do
            match (← (freg_arch_name_raw_backwards mapping1_)) with
            | i => (pure (some true)))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (match head_exp_ with
        | _ => (pure false)))

def freg_or_reg_name_backwards (arg_ : String) : SailM fregidx := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    if ((← (reg_name_backwards_matches mapping0_)) : Bool)
    then
      (do
        match (← (reg_name_backwards mapping0_)) with
        | .Regidx i =>
          (if ((hartSupports Ext_Zfinx) : Bool)
          then (pure (some (Fregidx (zero_extend (m := 5) i))))
          else (pure none)))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let mapping1_ := head_exp_
        if ((← (freg_name_backwards_matches mapping1_)) : Bool)
        then
          (do
            match (← (freg_name_backwards mapping1_)) with
            | f => (pure (some f)))
        else (pure none)) with
      | .some result => (pure result)
      | _ =>
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))

def freg_or_reg_name_forwards_matches (arg_ : fregidx) : Bool :=
  let f := arg_
  if ((hartSupports Ext_Zfinx) : Bool)
  then true
  else true

def freg_or_reg_name_backwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    if ((← (reg_name_backwards_matches mapping0_)) : Bool)
    then
      (do
        match (← (reg_name_backwards mapping0_)) with
        | .Regidx i =>
          (if ((hartSupports Ext_Zfinx) : Bool)
          then (pure (some true))
          else (pure none)))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let mapping1_ := head_exp_
        if ((← (freg_name_backwards_matches mapping1_)) : Bool)
        then
          (do
            match (← (freg_name_backwards mapping1_)) with
            | f => (pure (some true)))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (match head_exp_ with
        | _ => (pure false)))

def cfreg_name_backwards (arg_ : String) : SailM cfregidx := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    if ((← (freg_name_backwards_matches mapping0_)) : Bool)
    then
      (do
        match (← (freg_name_backwards mapping0_)) with
        | .Fregidx v__4 =>
          (if (((Sail.BitVec.extractLsb v__4 4 3) == (0b01#2 : (BitVec 2))) : Bool)
          then
            (let i : (BitVec 3) := (Sail.BitVec.extractLsb v__4 2 0)
            (pure (some (Cfregidx i))))
          else (pure none)))
    else (pure none)) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def cfreg_name_forwards_matches (arg_ : cfregidx) : Bool :=
  match arg_ with
  | .Cfregidx i => true

def cfreg_name_backwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    if ((← (freg_name_backwards_matches mapping0_)) : Bool)
    then
      (do
        match (← (freg_name_backwards mapping0_)) with
        | .Fregidx v__6 =>
          (if (((Sail.BitVec.extractLsb v__6 4 3) == (0b01#2 : (BitVec 2))) : Bool)
          then (pure (some true))
          else (pure none)))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def undefined_Fcsr (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Fcsr (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_Fcsr_FFLAGS (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _update_Fcsr_FFLAGS (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _set_Fcsr_FFLAGS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Fcsr_FFLAGS r v)

def _get_Fcsr_FRM (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 7 5)

def _update_Fcsr_FRM (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 5 x)

def _set_Fcsr_FRM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Fcsr_FRM r v)

def write_fcsr (frm : (BitVec 3)) (fflags : (BitVec 5)) : SailM Unit := do
  writeReg fcsr (Sail.BitVec.updateSubrange (← readReg fcsr) 7 5 frm)
  writeReg fcsr (Sail.BitVec.updateSubrange (← readReg fcsr) 4 0 fflags)
  (dirty_fd_context_if_present ())

def accrue_fflags (flags : (BitVec 5)) : SailM Unit := do
  let new_fflags ← do (pure ((_get_Fcsr_FFLAGS (← readReg fcsr)) ||| flags))
  let fflags_changed ← do (pure ((_get_Fcsr_FFLAGS (← readReg fcsr)) != new_fflags))
  let set_dirty : Bool :=
    match fflags_dirty_policy with
    | .Fflags_Dirty_Precise => fflags_changed
    | .Fflags_Dirty_Flag => (flags != (zeros (n := 5)))
    | .Fflags_Dirty_Instruction => true
  writeReg fcsr (Sail.BitVec.updateSubrange (← readReg fcsr) 4 0 new_fflags)
  if (set_dirty : Bool)
  then (dirty_fd_context_if_present ())
  else (pure ())
  (csr_name_write_callback "fflags" (zero_extend (m := 32) (_get_Fcsr_FFLAGS (← readReg fcsr))))
  (csr_name_write_callback "fcsr" (zero_extend (m := 32) (← readReg fcsr)))

