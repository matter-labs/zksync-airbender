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

def extensionName_forwards (arg_ : extension) : String :=
  match arg_ with
  | .Ext_M => "m"
  | .Ext_A => "a"
  | .Ext_F => "f"
  | .Ext_D => "d"
  | .Ext_B => "b"
  | .Ext_V => "v"
  | .Ext_S => "s"
  | .Ext_U => "u"
  | .Ext_H => "h"
  | .Ext_Sha => "sha"
  | .Ext_Shcounterenw => "shcounterenw"
  | .Ext_Shgatpa => "shgatpa"
  | .Ext_Shtvala => "shtvala"
  | .Ext_Shvsatpa => "shvsatpa"
  | .Ext_Shvstvala => "shvstvala"
  | .Ext_Shvstvecd => "shvstvecd"
  | .Ext_Zibi => "zibi"
  | .Ext_Zic64b => "zic64b"
  | .Ext_Zicbom => "zicbom"
  | .Ext_Zicbop => "zicbop"
  | .Ext_Zicboz => "zicboz"
  | .Ext_Zicfilp => "zicfilp"
  | .Ext_Zicfiss => "zicfiss"
  | .Ext_Zicntr => "zicntr"
  | .Ext_Zicond => "zicond"
  | .Ext_Zicsr => "zicsr"
  | .Ext_Zifencei => "zifencei"
  | .Ext_Zihintntl => "zihintntl"
  | .Ext_Zihintpause => "zihintpause"
  | .Ext_Zihpm => "zihpm"
  | .Ext_Zilx => "zilx"
  | .Ext_Zimop => "zimop"
  | .Ext_Zmmul => "zmmul"
  | .Ext_Zaamo => "zaamo"
  | .Ext_Zabha => "zabha"
  | .Ext_Zacas => "zacas"
  | .Ext_Zalrsc => "zalrsc"
  | .Ext_Zama16b => "zama16b"
  | .Ext_Zawrs => "zawrs"
  | .Ext_Za64rs => "za64rs"
  | .Ext_Za128rs => "za128rs"
  | .Ext_Zfa => "zfa"
  | .Ext_Zfbfmin => "zfbfmin"
  | .Ext_Zfh => "zfh"
  | .Ext_Zfhmin => "zfhmin"
  | .Ext_Zfinx => "zfinx"
  | .Ext_Zdinx => "zdinx"
  | .Ext_Zca => "zca"
  | .Ext_Zcb => "zcb"
  | .Ext_Zcd => "zcd"
  | .Ext_Zcf => "zcf"
  | .Ext_Zcmop => "zcmop"
  | .Ext_C => "c"
  | .Ext_Zba => "zba"
  | .Ext_Zbb => "zbb"
  | .Ext_Zbc => "zbc"
  | .Ext_Zbkb => "zbkb"
  | .Ext_Zbkc => "zbkc"
  | .Ext_Zbkx => "zbkx"
  | .Ext_Zbs => "zbs"
  | .Ext_Ziccamoa => "ziccamoa"
  | .Ext_Ziccamoc => "ziccamoc"
  | .Ext_Ziccif => "ziccif"
  | .Ext_Zicclsm => "zicclsm"
  | .Ext_Ziccrse => "ziccrse"
  | .Ext_Zknd => "zknd"
  | .Ext_Zkne => "zkne"
  | .Ext_Zknh => "zknh"
  | .Ext_Zkr => "zkr"
  | .Ext_Zksed => "zksed"
  | .Ext_Zksh => "zksh"
  | .Ext_Zkt => "zkt"
  | .Ext_Zhinx => "zhinx"
  | .Ext_Zhinxmin => "zhinxmin"
  | .Ext_Zvl32b => "zvl32b"
  | .Ext_Zvl64b => "zvl64b"
  | .Ext_Zvl128b => "zvl128b"
  | .Ext_Zvl256b => "zvl256b"
  | .Ext_Zvl512b => "zvl512b"
  | .Ext_Zvl1024b => "zvl1024b"
  | .Ext_Zve32f => "zve32f"
  | .Ext_Zve32x => "zve32x"
  | .Ext_Zve64d => "zve64d"
  | .Ext_Zve64f => "zve64f"
  | .Ext_Zve64x => "zve64x"
  | .Ext_Zvabd => "zvabd"
  | .Ext_Zvfbfmin => "zvfbfmin"
  | .Ext_Zvfbfwma => "zvfbfwma"
  | .Ext_Zvfh => "zvfh"
  | .Ext_Zvfhmin => "zvfhmin"
  | .Ext_Zvbb => "zvbb"
  | .Ext_Zvbc => "zvbc"
  | .Ext_Zvkb => "zvkb"
  | .Ext_Zvkg => "zvkg"
  | .Ext_Zvkned => "zvkned"
  | .Ext_Zvknha => "zvknha"
  | .Ext_Zvknhb => "zvknhb"
  | .Ext_Zvksed => "zvksed"
  | .Ext_Zvksh => "zvksh"
  | .Ext_Zvkt => "zvkt"
  | .Ext_Zvkn => "zvkn"
  | .Ext_Zvknc => "zvknc"
  | .Ext_Zvkng => "zvkng"
  | .Ext_Zvks => "zvks"
  | .Ext_Zvksc => "zvksc"
  | .Ext_Zvksg => "zvksg"
  | .Ext_Ssccptr => "ssccptr"
  | .Ext_Sscofpmf => "sscofpmf"
  | .Ext_Sscounterenw => "sscounterenw"
  | .Ext_Ssdbltrp => "ssdbltrp"
  | .Ext_Ssnpm => "ssnpm"
  | .Ext_Ssstateen => "ssstateen"
  | .Ext_Ssstrict => "ssstrict"
  | .Ext_Sdtrig => "sdtrig"
  | .Ext_Sstc => "sstc"
  | .Ext_Sstvala => "sstvala"
  | .Ext_Sstvecd => "sstvecd"
  | .Ext_Ssu64xl => "ssu64xl"
  | .Ext_Svbare => "svbare"
  | .Ext_Sv32 => "sv32"
  | .Ext_Sv39 => "sv39"
  | .Ext_Sv48 => "sv48"
  | .Ext_Sv57 => "sv57"
  | .Ext_Svade => "svade"
  | .Ext_Svadu => "svadu"
  | .Ext_Svinval => "svinval"
  | .Ext_Svnapot => "svnapot"
  | .Ext_Svpbmt => "svpbmt"
  | .Ext_Svrsw60t59b => "svrsw60t59b"
  | .Ext_Svukte => "svukte"
  | .Ext_Svvptc => "svvptc"
  | .Ext_Smcntrpmf => "smcntrpmf"
  | .Ext_Smdbltrp => "smdbltrp"
  | .Ext_Smmpm => "smmpm"
  | .Ext_Smnpm => "smnpm"
  | .Ext_Smstateen => "smstateen"
  | .Ext_Ssqosid => "ssqosid"
  | .Ext_Sspm => "sspm"
  | .Ext_Supm => "supm"

def extensionName_backwards (arg_ : String) : SailM extension := do
  match arg_ with
  | "m" => (pure Ext_M)
  | "a" => (pure Ext_A)
  | "f" => (pure Ext_F)
  | "d" => (pure Ext_D)
  | "b" => (pure Ext_B)
  | "v" => (pure Ext_V)
  | "s" => (pure Ext_S)
  | "u" => (pure Ext_U)
  | "h" => (pure Ext_H)
  | "sha" => (pure Ext_Sha)
  | "shcounterenw" => (pure Ext_Shcounterenw)
  | "shgatpa" => (pure Ext_Shgatpa)
  | "shtvala" => (pure Ext_Shtvala)
  | "shvsatpa" => (pure Ext_Shvsatpa)
  | "shvstvala" => (pure Ext_Shvstvala)
  | "shvstvecd" => (pure Ext_Shvstvecd)
  | "zibi" => (pure Ext_Zibi)
  | "zic64b" => (pure Ext_Zic64b)
  | "zicbom" => (pure Ext_Zicbom)
  | "zicbop" => (pure Ext_Zicbop)
  | "zicboz" => (pure Ext_Zicboz)
  | "zicfilp" => (pure Ext_Zicfilp)
  | "zicfiss" => (pure Ext_Zicfiss)
  | "zicntr" => (pure Ext_Zicntr)
  | "zicond" => (pure Ext_Zicond)
  | "zicsr" => (pure Ext_Zicsr)
  | "zifencei" => (pure Ext_Zifencei)
  | "zihintntl" => (pure Ext_Zihintntl)
  | "zihintpause" => (pure Ext_Zihintpause)
  | "zihpm" => (pure Ext_Zihpm)
  | "zilx" => (pure Ext_Zilx)
  | "zimop" => (pure Ext_Zimop)
  | "zmmul" => (pure Ext_Zmmul)
  | "zaamo" => (pure Ext_Zaamo)
  | "zabha" => (pure Ext_Zabha)
  | "zacas" => (pure Ext_Zacas)
  | "zalrsc" => (pure Ext_Zalrsc)
  | "zama16b" => (pure Ext_Zama16b)
  | "zawrs" => (pure Ext_Zawrs)
  | "za64rs" => (pure Ext_Za64rs)
  | "za128rs" => (pure Ext_Za128rs)
  | "zfa" => (pure Ext_Zfa)
  | "zfbfmin" => (pure Ext_Zfbfmin)
  | "zfh" => (pure Ext_Zfh)
  | "zfhmin" => (pure Ext_Zfhmin)
  | "zfinx" => (pure Ext_Zfinx)
  | "zdinx" => (pure Ext_Zdinx)
  | "zca" => (pure Ext_Zca)
  | "zcb" => (pure Ext_Zcb)
  | "zcd" => (pure Ext_Zcd)
  | "zcf" => (pure Ext_Zcf)
  | "zcmop" => (pure Ext_Zcmop)
  | "c" => (pure Ext_C)
  | "zba" => (pure Ext_Zba)
  | "zbb" => (pure Ext_Zbb)
  | "zbc" => (pure Ext_Zbc)
  | "zbkb" => (pure Ext_Zbkb)
  | "zbkc" => (pure Ext_Zbkc)
  | "zbkx" => (pure Ext_Zbkx)
  | "zbs" => (pure Ext_Zbs)
  | "ziccamoa" => (pure Ext_Ziccamoa)
  | "ziccamoc" => (pure Ext_Ziccamoc)
  | "ziccif" => (pure Ext_Ziccif)
  | "zicclsm" => (pure Ext_Zicclsm)
  | "ziccrse" => (pure Ext_Ziccrse)
  | "zknd" => (pure Ext_Zknd)
  | "zkne" => (pure Ext_Zkne)
  | "zknh" => (pure Ext_Zknh)
  | "zkr" => (pure Ext_Zkr)
  | "zksed" => (pure Ext_Zksed)
  | "zksh" => (pure Ext_Zksh)
  | "zkt" => (pure Ext_Zkt)
  | "zhinx" => (pure Ext_Zhinx)
  | "zhinxmin" => (pure Ext_Zhinxmin)
  | "zvl32b" => (pure Ext_Zvl32b)
  | "zvl64b" => (pure Ext_Zvl64b)
  | "zvl128b" => (pure Ext_Zvl128b)
  | "zvl256b" => (pure Ext_Zvl256b)
  | "zvl512b" => (pure Ext_Zvl512b)
  | "zvl1024b" => (pure Ext_Zvl1024b)
  | "zve32f" => (pure Ext_Zve32f)
  | "zve32x" => (pure Ext_Zve32x)
  | "zve64d" => (pure Ext_Zve64d)
  | "zve64f" => (pure Ext_Zve64f)
  | "zve64x" => (pure Ext_Zve64x)
  | "zvabd" => (pure Ext_Zvabd)
  | "zvfbfmin" => (pure Ext_Zvfbfmin)
  | "zvfbfwma" => (pure Ext_Zvfbfwma)
  | "zvfh" => (pure Ext_Zvfh)
  | "zvfhmin" => (pure Ext_Zvfhmin)
  | "zvbb" => (pure Ext_Zvbb)
  | "zvbc" => (pure Ext_Zvbc)
  | "zvkb" => (pure Ext_Zvkb)
  | "zvkg" => (pure Ext_Zvkg)
  | "zvkned" => (pure Ext_Zvkned)
  | "zvknha" => (pure Ext_Zvknha)
  | "zvknhb" => (pure Ext_Zvknhb)
  | "zvksed" => (pure Ext_Zvksed)
  | "zvksh" => (pure Ext_Zvksh)
  | "zvkt" => (pure Ext_Zvkt)
  | "zvkn" => (pure Ext_Zvkn)
  | "zvknc" => (pure Ext_Zvknc)
  | "zvkng" => (pure Ext_Zvkng)
  | "zvks" => (pure Ext_Zvks)
  | "zvksc" => (pure Ext_Zvksc)
  | "zvksg" => (pure Ext_Zvksg)
  | "ssccptr" => (pure Ext_Ssccptr)
  | "sscofpmf" => (pure Ext_Sscofpmf)
  | "sscounterenw" => (pure Ext_Sscounterenw)
  | "ssdbltrp" => (pure Ext_Ssdbltrp)
  | "ssnpm" => (pure Ext_Ssnpm)
  | "ssstateen" => (pure Ext_Ssstateen)
  | "ssstrict" => (pure Ext_Ssstrict)
  | "sdtrig" => (pure Ext_Sdtrig)
  | "sstc" => (pure Ext_Sstc)
  | "sstvala" => (pure Ext_Sstvala)
  | "sstvecd" => (pure Ext_Sstvecd)
  | "ssu64xl" => (pure Ext_Ssu64xl)
  | "svbare" => (pure Ext_Svbare)
  | "sv32" => (pure Ext_Sv32)
  | "sv39" => (pure Ext_Sv39)
  | "sv48" => (pure Ext_Sv48)
  | "sv57" => (pure Ext_Sv57)
  | "svade" => (pure Ext_Svade)
  | "svadu" => (pure Ext_Svadu)
  | "svinval" => (pure Ext_Svinval)
  | "svnapot" => (pure Ext_Svnapot)
  | "svpbmt" => (pure Ext_Svpbmt)
  | "svrsw60t59b" => (pure Ext_Svrsw60t59b)
  | "svukte" => (pure Ext_Svukte)
  | "svvptc" => (pure Ext_Svvptc)
  | "smcntrpmf" => (pure Ext_Smcntrpmf)
  | "smdbltrp" => (pure Ext_Smdbltrp)
  | "smmpm" => (pure Ext_Smmpm)
  | "smnpm" => (pure Ext_Smnpm)
  | "smstateen" => (pure Ext_Smstateen)
  | "ssqosid" => (pure Ext_Ssqosid)
  | "sspm" => (pure Ext_Sspm)
  | "supm" => (pure Ext_Supm)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def extensionName_forwards_matches (arg_ : extension) : Bool :=
  match arg_ with
  | .Ext_M => true
  | .Ext_A => true
  | .Ext_F => true
  | .Ext_D => true
  | .Ext_B => true
  | .Ext_V => true
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
  | .Ext_Zibi => true
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
  | .Ext_Zilx => true
  | .Ext_Zimop => true
  | .Ext_Zmmul => true
  | .Ext_Zaamo => true
  | .Ext_Zabha => true
  | .Ext_Zacas => true
  | .Ext_Zalrsc => true
  | .Ext_Zama16b => true
  | .Ext_Zawrs => true
  | .Ext_Za64rs => true
  | .Ext_Za128rs => true
  | .Ext_Zfa => true
  | .Ext_Zfbfmin => true
  | .Ext_Zfh => true
  | .Ext_Zfhmin => true
  | .Ext_Zfinx => true
  | .Ext_Zdinx => true
  | .Ext_Zca => true
  | .Ext_Zcb => true
  | .Ext_Zcd => true
  | .Ext_Zcf => true
  | .Ext_Zcmop => true
  | .Ext_C => true
  | .Ext_Zba => true
  | .Ext_Zbb => true
  | .Ext_Zbc => true
  | .Ext_Zbkb => true
  | .Ext_Zbkc => true
  | .Ext_Zbkx => true
  | .Ext_Zbs => true
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
  | .Ext_Zhinx => true
  | .Ext_Zhinxmin => true
  | .Ext_Zvl32b => true
  | .Ext_Zvl64b => true
  | .Ext_Zvl128b => true
  | .Ext_Zvl256b => true
  | .Ext_Zvl512b => true
  | .Ext_Zvl1024b => true
  | .Ext_Zve32f => true
  | .Ext_Zve32x => true
  | .Ext_Zve64d => true
  | .Ext_Zve64f => true
  | .Ext_Zve64x => true
  | .Ext_Zvabd => true
  | .Ext_Zvfbfmin => true
  | .Ext_Zvfbfwma => true
  | .Ext_Zvfh => true
  | .Ext_Zvfhmin => true
  | .Ext_Zvbb => true
  | .Ext_Zvbc => true
  | .Ext_Zvkb => true
  | .Ext_Zvkg => true
  | .Ext_Zvkned => true
  | .Ext_Zvknha => true
  | .Ext_Zvknhb => true
  | .Ext_Zvksed => true
  | .Ext_Zvksh => true
  | .Ext_Zvkt => true
  | .Ext_Zvkn => true
  | .Ext_Zvknc => true
  | .Ext_Zvkng => true
  | .Ext_Zvks => true
  | .Ext_Zvksc => true
  | .Ext_Zvksg => true
  | .Ext_Ssccptr => true
  | .Ext_Sscofpmf => true
  | .Ext_Sscounterenw => true
  | .Ext_Ssdbltrp => true
  | .Ext_Ssnpm => true
  | .Ext_Ssstateen => true
  | .Ext_Ssstrict => true
  | .Ext_Sdtrig => true
  | .Ext_Sstc => true
  | .Ext_Sstvala => true
  | .Ext_Sstvecd => true
  | .Ext_Ssu64xl => true
  | .Ext_Svbare => true
  | .Ext_Sv32 => true
  | .Ext_Sv39 => true
  | .Ext_Sv48 => true
  | .Ext_Sv57 => true
  | .Ext_Svade => true
  | .Ext_Svadu => true
  | .Ext_Svinval => true
  | .Ext_Svnapot => true
  | .Ext_Svpbmt => true
  | .Ext_Svrsw60t59b => true
  | .Ext_Svukte => true
  | .Ext_Svvptc => true
  | .Ext_Smcntrpmf => true
  | .Ext_Smdbltrp => true
  | .Ext_Smmpm => true
  | .Ext_Smnpm => true
  | .Ext_Smstateen => true
  | .Ext_Ssqosid => true
  | .Ext_Sspm => true
  | .Ext_Supm => true

def extensionName_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "m" => true
  | "a" => true
  | "f" => true
  | "d" => true
  | "b" => true
  | "v" => true
  | "s" => true
  | "u" => true
  | "h" => true
  | "sha" => true
  | "shcounterenw" => true
  | "shgatpa" => true
  | "shtvala" => true
  | "shvsatpa" => true
  | "shvstvala" => true
  | "shvstvecd" => true
  | "zibi" => true
  | "zic64b" => true
  | "zicbom" => true
  | "zicbop" => true
  | "zicboz" => true
  | "zicfilp" => true
  | "zicfiss" => true
  | "zicntr" => true
  | "zicond" => true
  | "zicsr" => true
  | "zifencei" => true
  | "zihintntl" => true
  | "zihintpause" => true
  | "zihpm" => true
  | "zilx" => true
  | "zimop" => true
  | "zmmul" => true
  | "zaamo" => true
  | "zabha" => true
  | "zacas" => true
  | "zalrsc" => true
  | "zama16b" => true
  | "zawrs" => true
  | "za64rs" => true
  | "za128rs" => true
  | "zfa" => true
  | "zfbfmin" => true
  | "zfh" => true
  | "zfhmin" => true
  | "zfinx" => true
  | "zdinx" => true
  | "zca" => true
  | "zcb" => true
  | "zcd" => true
  | "zcf" => true
  | "zcmop" => true
  | "c" => true
  | "zba" => true
  | "zbb" => true
  | "zbc" => true
  | "zbkb" => true
  | "zbkc" => true
  | "zbkx" => true
  | "zbs" => true
  | "ziccamoa" => true
  | "ziccamoc" => true
  | "ziccif" => true
  | "zicclsm" => true
  | "ziccrse" => true
  | "zknd" => true
  | "zkne" => true
  | "zknh" => true
  | "zkr" => true
  | "zksed" => true
  | "zksh" => true
  | "zkt" => true
  | "zhinx" => true
  | "zhinxmin" => true
  | "zvl32b" => true
  | "zvl64b" => true
  | "zvl128b" => true
  | "zvl256b" => true
  | "zvl512b" => true
  | "zvl1024b" => true
  | "zve32f" => true
  | "zve32x" => true
  | "zve64d" => true
  | "zve64f" => true
  | "zve64x" => true
  | "zvabd" => true
  | "zvfbfmin" => true
  | "zvfbfwma" => true
  | "zvfh" => true
  | "zvfhmin" => true
  | "zvbb" => true
  | "zvbc" => true
  | "zvkb" => true
  | "zvkg" => true
  | "zvkned" => true
  | "zvknha" => true
  | "zvknhb" => true
  | "zvksed" => true
  | "zvksh" => true
  | "zvkt" => true
  | "zvkn" => true
  | "zvknc" => true
  | "zvkng" => true
  | "zvks" => true
  | "zvksc" => true
  | "zvksg" => true
  | "ssccptr" => true
  | "sscofpmf" => true
  | "sscounterenw" => true
  | "ssdbltrp" => true
  | "ssnpm" => true
  | "ssstateen" => true
  | "ssstrict" => true
  | "sdtrig" => true
  | "sstc" => true
  | "sstvala" => true
  | "sstvecd" => true
  | "ssu64xl" => true
  | "svbare" => true
  | "sv32" => true
  | "sv39" => true
  | "sv48" => true
  | "sv57" => true
  | "svade" => true
  | "svadu" => true
  | "svinval" => true
  | "svnapot" => true
  | "svpbmt" => true
  | "svrsw60t59b" => true
  | "svukte" => true
  | "svvptc" => true
  | "smcntrpmf" => true
  | "smdbltrp" => true
  | "smmpm" => true
  | "smnpm" => true
  | "smstateen" => true
  | "ssqosid" => true
  | "sspm" => true
  | "supm" => true
  | _ => false

def extensions_ordered_for_isa_string :=
  #v[Ext_Sdtrig, Ext_Smstateen, Ext_Smnpm, Ext_Smmpm, Ext_Smdbltrp, Ext_Smcntrpmf, Ext_Shvstvecd, Ext_Shvstvala, Ext_Shvsatpa, Ext_Shtvala, Ext_Shgatpa, Ext_Shcounterenw, Ext_Sha, Ext_Svvptc, Ext_Svukte, Ext_Svrsw60t59b, Ext_Svpbmt, Ext_Svnapot, Ext_Svinval, Ext_Svadu, Ext_Svade, Ext_Supm, Ext_Ssu64xl, Ext_Sstvecd, Ext_Sstvala, Ext_Sstc, Ext_Ssstrict, Ext_Ssstateen, Ext_Ssqosid, Ext_Sspm, Ext_Ssnpm, Ext_Ssdbltrp, Ext_Sscounterenw, Ext_Sscofpmf, Ext_Ssccptr, Ext_Zvl1024b, Ext_Zvl512b, Ext_Zvl256b, Ext_Zvl128b, Ext_Zvl64b, Ext_Zvl32b, Ext_Zvkt, Ext_Zvksh, Ext_Zvksg, Ext_Zvksed, Ext_Zvksc, Ext_Zvks, Ext_Zvknhb, Ext_Zvknha, Ext_Zvkng, Ext_Zvkned, Ext_Zvknc, Ext_Zvkn, Ext_Zvkg, Ext_Zvkb, Ext_Zvfhmin, Ext_Zvfh, Ext_Zvfbfwma, Ext_Zvfbfmin, Ext_Zve64x, Ext_Zve64f, Ext_Zve64d, Ext_Zve32x, Ext_Zve32f, Ext_Zvbc, Ext_Zvbb, Ext_Zvabd, Ext_Zkt, Ext_Zksh, Ext_Zksed, Ext_Zkr, Ext_Zknh, Ext_Zkne, Ext_Zknd, Ext_Zbs, Ext_Zbkx, Ext_Zbkc, Ext_Zbkb, Ext_Zbc, Ext_Zbb, Ext_Zba, Ext_Zcmop, Ext_Zcf, Ext_Zcd, Ext_Zcb, Ext_Zca, Ext_Zhinxmin, Ext_Zhinx, Ext_Zdinx, Ext_Zfinx, Ext_Zfhmin, Ext_Zfh, Ext_Zfbfmin, Ext_Zfa, Ext_Zawrs, Ext_Zama16b, Ext_Zalrsc, Ext_Zacas, Ext_Zabha, Ext_Zaamo, Ext_Za64rs, Ext_Za128rs, Ext_Zmmul, Ext_Zimop, Ext_Zilx, Ext_Zihpm, Ext_Zihintpause, Ext_Zihintntl, Ext_Zifencei, Ext_Zicsr, Ext_Zicond, Ext_Zicntr, Ext_Zicfiss, Ext_Zicfilp, Ext_Ziccrse, Ext_Zicclsm, Ext_Ziccif, Ext_Ziccamoc, Ext_Ziccamoa, Ext_Zicboz, Ext_Zicbop, Ext_Zicbom, Ext_Zibi, Ext_Zic64b, Ext_H, Ext_V, Ext_B, Ext_C, Ext_D, Ext_F, Ext_A, Ext_M]

