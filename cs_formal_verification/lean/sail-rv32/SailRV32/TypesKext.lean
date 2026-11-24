import SailRV32.Prelude
import SailRV32.Errors

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

def xt2 (x : (BitVec 8)) : (BitVec 8) :=
  ((x <<< 1) ^^^ (if ((bit_to_bool (BitVec.access x 7)) : Bool)
    then 0x1B#8
    else 0x00#8))

def xt3 (x : (BitVec 8)) : (BitVec 8) :=
  (x ^^^ (xt2 x))

def gfmul (x : (BitVec 8)) (y : (BitVec 4)) : (BitVec 8) :=
  ((if ((bit_to_bool (BitVec.access y 0)) : Bool)
    then x
    else 0x00#8) ^^^ ((if ((bit_to_bool (BitVec.access y 1)) : Bool)
      then (xt2 x)
      else 0x00#8) ^^^ ((if ((bit_to_bool (BitVec.access y 2)) : Bool)
        then (xt2 (xt2 x))
        else 0x00#8) ^^^ (if ((bit_to_bool (BitVec.access y 3)) : Bool)
        then (xt2 (xt2 (xt2 x)))
        else 0x00#8))))

def aes_mixcolumn_byte_fwd (so : (BitVec 8)) : (BitVec 32) :=
  ((gfmul so 0x3#4) +++ (so +++ (so +++ (gfmul so 0x2#4))))

def aes_mixcolumn_byte_inv (so : (BitVec 8)) : (BitVec 32) :=
  ((gfmul so 0xB#4) +++ ((gfmul so 0xD#4) +++ ((gfmul so 0x9#4) +++ (gfmul so 0xE#4))))

def aes_mixcolumn_fwd (x : (BitVec 32)) : (BitVec 32) :=
  let s0 : (BitVec 8) := (Sail.BitVec.extractLsb x 7 0)
  let s1 : (BitVec 8) := (Sail.BitVec.extractLsb x 15 8)
  let s2 : (BitVec 8) := (Sail.BitVec.extractLsb x 23 16)
  let s3 : (BitVec 8) := (Sail.BitVec.extractLsb x 31 24)
  let b0 : (BitVec 8) := ((xt2 s0) ^^^ ((xt3 s1) ^^^ (s2 ^^^ s3)))
  let b1 : (BitVec 8) := (s0 ^^^ ((xt2 s1) ^^^ ((xt3 s2) ^^^ s3)))
  let b2 : (BitVec 8) := (s0 ^^^ (s1 ^^^ ((xt2 s2) ^^^ (xt3 s3))))
  let b3 : (BitVec 8) := ((xt3 s0) ^^^ (s1 ^^^ (s2 ^^^ (xt2 s3))))
  (b3 +++ (b2 +++ (b1 +++ b0)))

def aes_mixcolumn_inv (x : (BitVec 32)) : (BitVec 32) :=
  let s0 : (BitVec 8) := (Sail.BitVec.extractLsb x 7 0)
  let s1 : (BitVec 8) := (Sail.BitVec.extractLsb x 15 8)
  let s2 : (BitVec 8) := (Sail.BitVec.extractLsb x 23 16)
  let s3 : (BitVec 8) := (Sail.BitVec.extractLsb x 31 24)
  let b0 : (BitVec 8) :=
    ((gfmul s0 0xE#4) ^^^ ((gfmul s1 0xB#4) ^^^ ((gfmul s2 0xD#4) ^^^ (gfmul s3 0x9#4))))
  let b1 : (BitVec 8) :=
    ((gfmul s0 0x9#4) ^^^ ((gfmul s1 0xE#4) ^^^ ((gfmul s2 0xB#4) ^^^ (gfmul s3 0xD#4))))
  let b2 : (BitVec 8) :=
    ((gfmul s0 0xD#4) ^^^ ((gfmul s1 0x9#4) ^^^ ((gfmul s2 0xE#4) ^^^ (gfmul s3 0xB#4))))
  let b3 : (BitVec 8) :=
    ((gfmul s0 0xB#4) ^^^ ((gfmul s1 0xD#4) ^^^ ((gfmul s2 0x9#4) ^^^ (gfmul s3 0xE#4))))
  (b3 +++ (b2 +++ (b1 +++ b0)))

def aes_decode_rcon (r : (BitVec 4)) : SailM (BitVec 32) := do
  «assert» (zopz0zI_u r 0xA#4) "extensions/K/types_kext.sail:77.18-77.19"
  match r with
  | 0x0 => (pure 0x00000001#32)
  | 0x1 => (pure 0x00000002#32)
  | 0x2 => (pure 0x00000004#32)
  | 0x3 => (pure 0x00000008#32)
  | 0x4 => (pure 0x00000010#32)
  | 0x5 => (pure 0x00000020#32)
  | 0x6 => (pure 0x00000040#32)
  | 0x7 => (pure 0x00000080#32)
  | 0x8 => (pure 0x0000001B#32)
  | 0x9 => (pure 0x00000036#32)
  | _ => (internal_error "extensions/K/types_kext.sail" 89 "Unexpected AES r")

def sm4_sbox_table : (Vector (BitVec 8) 256) :=
  #v[0x48#8, 0x39#8, 0xCB#8, 0xD7#8, 0x3E#8, 0x5F#8, 0xEE#8, 0x79#8, 0x20#8, 0x4D#8, 0xDC#8, 0x3A#8, 0xEC#8, 0x7D#8, 0xF0#8, 0x18#8, 0x84#8, 0xC6#8, 0x6E#8, 0xC5#8, 0x09#8, 0xF1#8, 0xB9#8, 0x65#8, 0x7E#8, 0x77#8, 0x96#8, 0x0C#8, 0x4A#8, 0x97#8, 0x69#8, 0x89#8, 0xB0#8, 0xB4#8, 0xE5#8, 0xB8#8, 0x12#8, 0xD0#8, 0x74#8, 0x2D#8, 0xBD#8, 0x7B#8, 0xCD#8, 0xA5#8, 0x88#8, 0x31#8, 0xC1#8, 0x0A#8, 0xD8#8, 0x5A#8, 0x10#8, 0x1F#8, 0x41#8, 0x5C#8, 0xD9#8, 0x11#8, 0x7F#8, 0xBC#8, 0xDD#8, 0xBB#8, 0x92#8, 0xAF#8, 0x1B#8, 0x8D#8, 0x51#8, 0x5B#8, 0x6C#8, 0x6D#8, 0x72#8, 0x6A#8, 0xFF#8, 0x03#8, 0x2F#8, 0x8E#8, 0xFD#8, 0xDE#8, 0x45#8, 0x37#8, 0xDB#8, 0xD5#8, 0x6F#8, 0x4E#8, 0x53#8, 0x0D#8, 0xAB#8, 0x23#8, 0x29#8, 0xC0#8, 0x60#8, 0xCA#8, 0x66#8, 0x82#8, 0x2E#8, 0xE2#8, 0xF6#8, 0x1D#8, 0xE3#8, 0xB1#8, 0x8C#8, 0xF5#8, 0x30#8, 0x32#8, 0x93#8, 0xAD#8, 0x55#8, 0x1A#8, 0x34#8, 0x9B#8, 0xA4#8, 0x5D#8, 0xAE#8, 0xE0#8, 0xA1#8, 0x15#8, 0x61#8, 0xF9#8, 0xCE#8, 0xF2#8, 0xF7#8, 0xA3#8, 0xB5#8, 0x38#8, 0xC7#8, 0x40#8, 0xD2#8, 0x8A#8, 0xBF#8, 0xEA#8, 0x9E#8, 0xC8#8, 0xC4#8, 0xA0#8, 0xE7#8, 0x02#8, 0x36#8, 0x4C#8, 0x52#8, 0x27#8, 0xD3#8, 0x9F#8, 0x57#8, 0x46#8, 0x00#8, 0xD4#8, 0x87#8, 0x78#8, 0x21#8, 0x01#8, 0x3B#8, 0x7C#8, 0x22#8, 0x25#8, 0xA2#8, 0xD1#8, 0x58#8, 0x63#8, 0x5E#8, 0x0E#8, 0x24#8, 0x1E#8, 0x35#8, 0x9D#8, 0x56#8, 0x70#8, 0x4B#8, 0x0F#8, 0xEB#8, 0xF8#8, 0x8B#8, 0xDA#8, 0x64#8, 0x71#8, 0xB2#8, 0x81#8, 0x6B#8, 0x68#8, 0xA8#8, 0x4F#8, 0x85#8, 0xE6#8, 0x19#8, 0x3C#8, 0x59#8, 0x83#8, 0xBA#8, 0x17#8, 0x73#8, 0xF3#8, 0xFC#8, 0xA7#8, 0x07#8, 0x47#8, 0xA6#8, 0x3F#8, 0x8F#8, 0x75#8, 0xFA#8, 0x94#8, 0xDF#8, 0x80#8, 0x95#8, 0xE8#8, 0x08#8, 0xC9#8, 0xA9#8, 0x1C#8, 0xB3#8, 0xE4#8, 0x62#8, 0xAC#8, 0xCF#8, 0xED#8, 0x43#8, 0x0B#8, 0x54#8, 0x33#8, 0x7A#8, 0x98#8, 0xEF#8, 0x91#8, 0xF4#8, 0x50#8, 0x42#8, 0x9C#8, 0x99#8, 0x06#8, 0x86#8, 0x49#8, 0x26#8, 0x13#8, 0x44#8, 0xAA#8, 0xC3#8, 0x04#8, 0xBE#8, 0x2A#8, 0x76#8, 0x9A#8, 0x67#8, 0x2B#8, 0x05#8, 0x2C#8, 0xFB#8, 0x28#8, 0xC2#8, 0x14#8, 0xB6#8, 0x16#8, 0xB7#8, 0x3D#8, 0xE1#8, 0xCC#8, 0xFE#8, 0xE9#8, 0x90#8, 0xD6#8]

def aes_sbox_fwd_table : (Vector (BitVec 8) 256) :=
  #v[0x16#8, 0xBB#8, 0x54#8, 0xB0#8, 0x0F#8, 0x2D#8, 0x99#8, 0x41#8, 0x68#8, 0x42#8, 0xE6#8, 0xBF#8, 0x0D#8, 0x89#8, 0xA1#8, 0x8C#8, 0xDF#8, 0x28#8, 0x55#8, 0xCE#8, 0xE9#8, 0x87#8, 0x1E#8, 0x9B#8, 0x94#8, 0x8E#8, 0xD9#8, 0x69#8, 0x11#8, 0x98#8, 0xF8#8, 0xE1#8, 0x9E#8, 0x1D#8, 0xC1#8, 0x86#8, 0xB9#8, 0x57#8, 0x35#8, 0x61#8, 0x0E#8, 0xF6#8, 0x03#8, 0x48#8, 0x66#8, 0xB5#8, 0x3E#8, 0x70#8, 0x8A#8, 0x8B#8, 0xBD#8, 0x4B#8, 0x1F#8, 0x74#8, 0xDD#8, 0xE8#8, 0xC6#8, 0xB4#8, 0xA6#8, 0x1C#8, 0x2E#8, 0x25#8, 0x78#8, 0xBA#8, 0x08#8, 0xAE#8, 0x7A#8, 0x65#8, 0xEA#8, 0xF4#8, 0x56#8, 0x6C#8, 0xA9#8, 0x4E#8, 0xD5#8, 0x8D#8, 0x6D#8, 0x37#8, 0xC8#8, 0xE7#8, 0x79#8, 0xE4#8, 0x95#8, 0x91#8, 0x62#8, 0xAC#8, 0xD3#8, 0xC2#8, 0x5C#8, 0x24#8, 0x06#8, 0x49#8, 0x0A#8, 0x3A#8, 0x32#8, 0xE0#8, 0xDB#8, 0x0B#8, 0x5E#8, 0xDE#8, 0x14#8, 0xB8#8, 0xEE#8, 0x46#8, 0x88#8, 0x90#8, 0x2A#8, 0x22#8, 0xDC#8, 0x4F#8, 0x81#8, 0x60#8, 0x73#8, 0x19#8, 0x5D#8, 0x64#8, 0x3D#8, 0x7E#8, 0xA7#8, 0xC4#8, 0x17#8, 0x44#8, 0x97#8, 0x5F#8, 0xEC#8, 0x13#8, 0x0C#8, 0xCD#8, 0xD2#8, 0xF3#8, 0xFF#8, 0x10#8, 0x21#8, 0xDA#8, 0xB6#8, 0xBC#8, 0xF5#8, 0x38#8, 0x9D#8, 0x92#8, 0x8F#8, 0x40#8, 0xA3#8, 0x51#8, 0xA8#8, 0x9F#8, 0x3C#8, 0x50#8, 0x7F#8, 0x02#8, 0xF9#8, 0x45#8, 0x85#8, 0x33#8, 0x4D#8, 0x43#8, 0xFB#8, 0xAA#8, 0xEF#8, 0xD0#8, 0xCF#8, 0x58#8, 0x4C#8, 0x4A#8, 0x39#8, 0xBE#8, 0xCB#8, 0x6A#8, 0x5B#8, 0xB1#8, 0xFC#8, 0x20#8, 0xED#8, 0x00#8, 0xD1#8, 0x53#8, 0x84#8, 0x2F#8, 0xE3#8, 0x29#8, 0xB3#8, 0xD6#8, 0x3B#8, 0x52#8, 0xA0#8, 0x5A#8, 0x6E#8, 0x1B#8, 0x1A#8, 0x2C#8, 0x83#8, 0x09#8, 0x75#8, 0xB2#8, 0x27#8, 0xEB#8, 0xE2#8, 0x80#8, 0x12#8, 0x07#8, 0x9A#8, 0x05#8, 0x96#8, 0x18#8, 0xC3#8, 0x23#8, 0xC7#8, 0x04#8, 0x15#8, 0x31#8, 0xD8#8, 0x71#8, 0xF1#8, 0xE5#8, 0xA5#8, 0x34#8, 0xCC#8, 0xF7#8, 0x3F#8, 0x36#8, 0x26#8, 0x93#8, 0xFD#8, 0xB7#8, 0xC0#8, 0x72#8, 0xA4#8, 0x9C#8, 0xAF#8, 0xA2#8, 0xD4#8, 0xAD#8, 0xF0#8, 0x47#8, 0x59#8, 0xFA#8, 0x7D#8, 0xC9#8, 0x82#8, 0xCA#8, 0x76#8, 0xAB#8, 0xD7#8, 0xFE#8, 0x2B#8, 0x67#8, 0x01#8, 0x30#8, 0xC5#8, 0x6F#8, 0x6B#8, 0xF2#8, 0x7B#8, 0x77#8, 0x7C#8, 0x63#8]

def aes_sbox_inv_table : (Vector (BitVec 8) 256) :=
  #v[0x7D#8, 0x0C#8, 0x21#8, 0x55#8, 0x63#8, 0x14#8, 0x69#8, 0xE1#8, 0x26#8, 0xD6#8, 0x77#8, 0xBA#8, 0x7E#8, 0x04#8, 0x2B#8, 0x17#8, 0x61#8, 0x99#8, 0x53#8, 0x83#8, 0x3C#8, 0xBB#8, 0xEB#8, 0xC8#8, 0xB0#8, 0xF5#8, 0x2A#8, 0xAE#8, 0x4D#8, 0x3B#8, 0xE0#8, 0xA0#8, 0xEF#8, 0x9C#8, 0xC9#8, 0x93#8, 0x9F#8, 0x7A#8, 0xE5#8, 0x2D#8, 0x0D#8, 0x4A#8, 0xB5#8, 0x19#8, 0xA9#8, 0x7F#8, 0x51#8, 0x60#8, 0x5F#8, 0xEC#8, 0x80#8, 0x27#8, 0x59#8, 0x10#8, 0x12#8, 0xB1#8, 0x31#8, 0xC7#8, 0x07#8, 0x88#8, 0x33#8, 0xA8#8, 0xDD#8, 0x1F#8, 0xF4#8, 0x5A#8, 0xCD#8, 0x78#8, 0xFE#8, 0xC0#8, 0xDB#8, 0x9A#8, 0x20#8, 0x79#8, 0xD2#8, 0xC6#8, 0x4B#8, 0x3E#8, 0x56#8, 0xFC#8, 0x1B#8, 0xBE#8, 0x18#8, 0xAA#8, 0x0E#8, 0x62#8, 0xB7#8, 0x6F#8, 0x89#8, 0xC5#8, 0x29#8, 0x1D#8, 0x71#8, 0x1A#8, 0xF1#8, 0x47#8, 0x6E#8, 0xDF#8, 0x75#8, 0x1C#8, 0xE8#8, 0x37#8, 0xF9#8, 0xE2#8, 0x85#8, 0x35#8, 0xAD#8, 0xE7#8, 0x22#8, 0x74#8, 0xAC#8, 0x96#8, 0x73#8, 0xE6#8, 0xB4#8, 0xF0#8, 0xCE#8, 0xCF#8, 0xF2#8, 0x97#8, 0xEA#8, 0xDC#8, 0x67#8, 0x4F#8, 0x41#8, 0x11#8, 0x91#8, 0x3A#8, 0x6B#8, 0x8A#8, 0x13#8, 0x01#8, 0x03#8, 0xBD#8, 0xAF#8, 0xC1#8, 0x02#8, 0x0F#8, 0x3F#8, 0xCA#8, 0x8F#8, 0x1E#8, 0x2C#8, 0xD0#8, 0x06#8, 0x45#8, 0xB3#8, 0xB8#8, 0x05#8, 0x58#8, 0xE4#8, 0xF7#8, 0x0A#8, 0xD3#8, 0xBC#8, 0x8C#8, 0x00#8, 0xAB#8, 0xD8#8, 0x90#8, 0x84#8, 0x9D#8, 0x8D#8, 0xA7#8, 0x57#8, 0x46#8, 0x15#8, 0x5E#8, 0xDA#8, 0xB9#8, 0xED#8, 0xFD#8, 0x50#8, 0x48#8, 0x70#8, 0x6C#8, 0x92#8, 0xB6#8, 0x65#8, 0x5D#8, 0xCC#8, 0x5C#8, 0xA4#8, 0xD4#8, 0x16#8, 0x98#8, 0x68#8, 0x86#8, 0x64#8, 0xF6#8, 0xF8#8, 0x72#8, 0x25#8, 0xD1#8, 0x8B#8, 0x6D#8, 0x49#8, 0xA2#8, 0x5B#8, 0x76#8, 0xB2#8, 0x24#8, 0xD9#8, 0x28#8, 0x66#8, 0xA1#8, 0x2E#8, 0x08#8, 0x4E#8, 0xC3#8, 0xFA#8, 0x42#8, 0x0B#8, 0x95#8, 0x4C#8, 0xEE#8, 0x3D#8, 0x23#8, 0xC2#8, 0xA6#8, 0x32#8, 0x94#8, 0x7B#8, 0x54#8, 0xCB#8, 0xE9#8, 0xDE#8, 0xC4#8, 0x44#8, 0x43#8, 0x8E#8, 0x34#8, 0x87#8, 0xFF#8, 0x2F#8, 0x9B#8, 0x82#8, 0x39#8, 0xE3#8, 0x7C#8, 0xFB#8, 0xD7#8, 0xF3#8, 0x81#8, 0x9E#8, 0xA3#8, 0x40#8, 0xBF#8, 0x38#8, 0xA5#8, 0x36#8, 0x30#8, 0xD5#8, 0x6A#8, 0x09#8, 0x52#8]

def sbox_lookup (x : (BitVec 8)) (table : (Vector (BitVec 8) 256)) : (BitVec 8) :=
  (GetElem?.getElem! table (255 -i (BitVec.toNatInt x)))

def aes_sbox_fwd (x : (BitVec 8)) : (BitVec 8) :=
  (sbox_lookup x aes_sbox_fwd_table)

def aes_sbox_inv (x : (BitVec 8)) : (BitVec 8) :=
  (sbox_lookup x aes_sbox_inv_table)

def aes_subword_fwd (x : (BitVec 32)) : (BitVec 32) :=
  ((aes_sbox_fwd (Sail.BitVec.extractLsb x 31 24)) +++ ((aes_sbox_fwd
        (Sail.BitVec.extractLsb x 23 16)) +++ ((aes_sbox_fwd (Sail.BitVec.extractLsb x 15 8)) +++ (aes_sbox_fwd
          (Sail.BitVec.extractLsb x 7 0)))))

def aes_subword_inv (x : (BitVec 32)) : (BitVec 32) :=
  ((aes_sbox_inv (Sail.BitVec.extractLsb x 31 24)) +++ ((aes_sbox_inv
        (Sail.BitVec.extractLsb x 23 16)) +++ ((aes_sbox_inv (Sail.BitVec.extractLsb x 15 8)) +++ (aes_sbox_inv
          (Sail.BitVec.extractLsb x 7 0)))))

def sm4_sbox (x : (BitVec 8)) : (BitVec 8) :=
  (sbox_lookup x sm4_sbox_table)

/-- Type quantifiers: c : Nat, 0 ≤ c ∧ c ≤ 3 -/
def aes_get_column (state : (BitVec 128)) (c : Nat) : (BitVec 32) :=
  (Sail.BitVec.extractLsb state ((32 *i c) +i 31) (32 *i c))

def aes_apply_fwd_sbox_to_each_byte (x : (BitVec 64)) : (BitVec 64) :=
  ((aes_sbox_fwd (Sail.BitVec.extractLsb x 63 56)) +++ ((aes_sbox_fwd
        (Sail.BitVec.extractLsb x 55 48)) +++ ((aes_sbox_fwd (Sail.BitVec.extractLsb x 47 40)) +++ ((aes_sbox_fwd
            (Sail.BitVec.extractLsb x 39 32)) +++ ((aes_sbox_fwd (Sail.BitVec.extractLsb x 31 24)) +++ ((aes_sbox_fwd
                (Sail.BitVec.extractLsb x 23 16)) +++ ((aes_sbox_fwd (Sail.BitVec.extractLsb x 15 8)) +++ (aes_sbox_fwd
                  (Sail.BitVec.extractLsb x 7 0)))))))))

def aes_apply_inv_sbox_to_each_byte (x : (BitVec 64)) : (BitVec 64) :=
  ((aes_sbox_inv (Sail.BitVec.extractLsb x 63 56)) +++ ((aes_sbox_inv
        (Sail.BitVec.extractLsb x 55 48)) +++ ((aes_sbox_inv (Sail.BitVec.extractLsb x 47 40)) +++ ((aes_sbox_inv
            (Sail.BitVec.extractLsb x 39 32)) +++ ((aes_sbox_inv (Sail.BitVec.extractLsb x 31 24)) +++ ((aes_sbox_inv
                (Sail.BitVec.extractLsb x 23 16)) +++ ((aes_sbox_inv (Sail.BitVec.extractLsb x 15 8)) +++ (aes_sbox_inv
                  (Sail.BitVec.extractLsb x 7 0)))))))))

/-- Type quantifiers: i : Nat, 0 ≤ i ∧ i ≤ 7 -/
def getbyte (x : (BitVec 64)) (i : Nat) : (BitVec 8) :=
  (Sail.BitVec.extractLsb x ((8 *i i) +i 7) (8 *i i))

def aes_rv64_shiftrows_fwd (rs2 : (BitVec 64)) (rs1 : (BitVec 64)) : (BitVec 64) :=
  ((getbyte rs1 3) +++ ((getbyte rs2 6) +++ ((getbyte rs2 1) +++ ((getbyte rs1 4) +++ ((getbyte rs2
              7) +++ ((getbyte rs2 2) +++ ((getbyte rs1 5) +++ (getbyte rs1 0))))))))

def aes_rv64_shiftrows_inv (rs2 : (BitVec 64)) (rs1 : (BitVec 64)) : (BitVec 64) :=
  ((getbyte rs2 3) +++ ((getbyte rs2 6) +++ ((getbyte rs1 1) +++ ((getbyte rs1 4) +++ ((getbyte rs1
              7) +++ ((getbyte rs2 2) +++ ((getbyte rs2 5) +++ (getbyte rs1 0))))))))

def aes_shift_rows_fwd (x : (BitVec 128)) : (BitVec 128) :=
  let ic3 : (BitVec 32) := (aes_get_column x 3)
  let ic2 : (BitVec 32) := (aes_get_column x 2)
  let ic1 : (BitVec 32) := (aes_get_column x 1)
  let ic0 : (BitVec 32) := (aes_get_column x 0)
  let oc0 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic3 31 24) +++ ((Sail.BitVec.extractLsb ic2 23 16) +++ ((Sail.BitVec.extractLsb
            ic1 15 8) +++ (Sail.BitVec.extractLsb ic0 7 0))))
  let oc1 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic0 31 24) +++ ((Sail.BitVec.extractLsb ic3 23 16) +++ ((Sail.BitVec.extractLsb
            ic2 15 8) +++ (Sail.BitVec.extractLsb ic1 7 0))))
  let oc2 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic1 31 24) +++ ((Sail.BitVec.extractLsb ic0 23 16) +++ ((Sail.BitVec.extractLsb
            ic3 15 8) +++ (Sail.BitVec.extractLsb ic2 7 0))))
  let oc3 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic2 31 24) +++ ((Sail.BitVec.extractLsb ic1 23 16) +++ ((Sail.BitVec.extractLsb
            ic0 15 8) +++ (Sail.BitVec.extractLsb ic3 7 0))))
  (oc3 +++ (oc2 +++ (oc1 +++ oc0)))

def aes_shift_rows_inv (x : (BitVec 128)) : (BitVec 128) :=
  let ic3 : (BitVec 32) := (aes_get_column x 3)
  let ic2 : (BitVec 32) := (aes_get_column x 2)
  let ic1 : (BitVec 32) := (aes_get_column x 1)
  let ic0 : (BitVec 32) := (aes_get_column x 0)
  let oc0 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic1 31 24) +++ ((Sail.BitVec.extractLsb ic2 23 16) +++ ((Sail.BitVec.extractLsb
            ic3 15 8) +++ (Sail.BitVec.extractLsb ic0 7 0))))
  let oc1 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic2 31 24) +++ ((Sail.BitVec.extractLsb ic3 23 16) +++ ((Sail.BitVec.extractLsb
            ic0 15 8) +++ (Sail.BitVec.extractLsb ic1 7 0))))
  let oc2 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic3 31 24) +++ ((Sail.BitVec.extractLsb ic0 23 16) +++ ((Sail.BitVec.extractLsb
            ic1 15 8) +++ (Sail.BitVec.extractLsb ic2 7 0))))
  let oc3 : (BitVec 32) :=
    ((Sail.BitVec.extractLsb ic0 31 24) +++ ((Sail.BitVec.extractLsb ic1 23 16) +++ ((Sail.BitVec.extractLsb
            ic2 15 8) +++ (Sail.BitVec.extractLsb ic3 7 0))))
  (oc3 +++ (oc2 +++ (oc1 +++ oc0)))

def aes_subbytes_fwd (x : (BitVec 128)) : (BitVec 128) :=
  let oc0 : (BitVec 32) := (aes_subword_fwd (aes_get_column x 0))
  let oc1 : (BitVec 32) := (aes_subword_fwd (aes_get_column x 1))
  let oc2 : (BitVec 32) := (aes_subword_fwd (aes_get_column x 2))
  let oc3 : (BitVec 32) := (aes_subword_fwd (aes_get_column x 3))
  (oc3 +++ (oc2 +++ (oc1 +++ oc0)))

def aes_subbytes_inv (x : (BitVec 128)) : (BitVec 128) :=
  let oc0 : (BitVec 32) := (aes_subword_inv (aes_get_column x 0))
  let oc1 : (BitVec 32) := (aes_subword_inv (aes_get_column x 1))
  let oc2 : (BitVec 32) := (aes_subword_inv (aes_get_column x 2))
  let oc3 : (BitVec 32) := (aes_subword_inv (aes_get_column x 3))
  (oc3 +++ (oc2 +++ (oc1 +++ oc0)))

def aes_mixcolumns_fwd (x : (BitVec 128)) : (BitVec 128) :=
  let oc0 : (BitVec 32) := (aes_mixcolumn_fwd (aes_get_column x 0))
  let oc1 : (BitVec 32) := (aes_mixcolumn_fwd (aes_get_column x 1))
  let oc2 : (BitVec 32) := (aes_mixcolumn_fwd (aes_get_column x 2))
  let oc3 : (BitVec 32) := (aes_mixcolumn_fwd (aes_get_column x 3))
  (oc3 +++ (oc2 +++ (oc1 +++ oc0)))

def aes_mixcolumns_inv (x : (BitVec 128)) : (BitVec 128) :=
  let oc0 : (BitVec 32) := (aes_mixcolumn_inv (aes_get_column x 0))
  let oc1 : (BitVec 32) := (aes_mixcolumn_inv (aes_get_column x 1))
  let oc2 : (BitVec 32) := (aes_mixcolumn_inv (aes_get_column x 2))
  let oc3 : (BitVec 32) := (aes_mixcolumn_inv (aes_get_column x 3))
  (oc3 +++ (oc2 +++ (oc1 +++ oc0)))

