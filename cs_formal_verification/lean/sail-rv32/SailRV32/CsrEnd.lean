import SailRV32.HexBits

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

def csr_name_map_forwards_matches (arg_ : (BitVec 12)) : Bool :=
  match arg_ with
  | 0x301 => true
  | 0x300 => true
  | 0x310 => true
  | 0x600 => true
  | 0x747 => true
  | 0x757 => true
  | 0x30A => true
  | 0x31A => true
  | 0x10A => true
  | 0x60A => true
  | 0x61A => true
  | 0x342 => true
  | 0x343 => true
  | 0x340 => true
  | 0x106 => true
  | 0x606 => true
  | 0x306 => true
  | 0x320 => true
  | 0xF11 => true
  | 0xF12 => true
  | 0xF13 => true
  | 0xF14 => true
  | 0xF15 => true
  | 0x34A => true
  | 0x34B => true
  | 0x605 => true
  | 0x615 => true
  | 0x643 => true
  | 0x64A => true
  | 0x200 => true
  | 0x100 => true
  | 0x240 => true
  | 0x242 => true
  | 0x243 => true
  | 0x140 => true
  | 0x142 => true
  | 0x143 => true
  | 0x607 => true
  | 0xE12 => true
  | 0x304 => true
  | 0x344 => true
  | 0x302 => true
  | 0x312 => true
  | 0x303 => true
  | 0x645 => true
  | 0x604 => true
  | 0x644 => true
  | 0x602 => true
  | 0x603 => true
  | 0x612 => true
  | 0x144 => true
  | 0x104 => true
  | 0x204 => true
  | 0x244 => true
  | 0xB00 => true
  | 0xB02 => true
  | 0xB80 => true
  | 0xB82 => true
  | 0x323 => true
  | 0x324 => true
  | 0x325 => true
  | 0x326 => true
  | 0x327 => true
  | 0x328 => true
  | 0x329 => true
  | 0x32A => true
  | 0x32B => true
  | 0x32C => true
  | 0x32D => true
  | 0x32E => true
  | 0x32F => true
  | 0x330 => true
  | 0x331 => true
  | 0x332 => true
  | 0x333 => true
  | 0x334 => true
  | 0x335 => true
  | 0x336 => true
  | 0x337 => true
  | 0x338 => true
  | 0x339 => true
  | 0x33A => true
  | 0x33B => true
  | 0x33C => true
  | 0x33D => true
  | 0x33E => true
  | 0x33F => true
  | 0xB03 => true
  | 0xB04 => true
  | 0xB05 => true
  | 0xB06 => true
  | 0xB07 => true
  | 0xB08 => true
  | 0xB09 => true
  | 0xB0A => true
  | 0xB0B => true
  | 0xB0C => true
  | 0xB0D => true
  | 0xB0E => true
  | 0xB0F => true
  | 0xB10 => true
  | 0xB11 => true
  | 0xB12 => true
  | 0xB13 => true
  | 0xB14 => true
  | 0xB15 => true
  | 0xB16 => true
  | 0xB17 => true
  | 0xB18 => true
  | 0xB19 => true
  | 0xB1A => true
  | 0xB1B => true
  | 0xB1C => true
  | 0xB1D => true
  | 0xB1E => true
  | 0xB1F => true
  | 0xB83 => true
  | 0xB84 => true
  | 0xB85 => true
  | 0xB86 => true
  | 0xB87 => true
  | 0xB88 => true
  | 0xB89 => true
  | 0xB8A => true
  | 0xB8B => true
  | 0xB8C => true
  | 0xB8D => true
  | 0xB8E => true
  | 0xB8F => true
  | 0xB90 => true
  | 0xB91 => true
  | 0xB92 => true
  | 0xB93 => true
  | 0xB94 => true
  | 0xB95 => true
  | 0xB96 => true
  | 0xB97 => true
  | 0xB98 => true
  | 0xB99 => true
  | 0xB9A => true
  | 0xB9B => true
  | 0xB9C => true
  | 0xB9D => true
  | 0xB9E => true
  | 0xB9F => true
  | 0x205 => true
  | 0x241 => true
  | 0x105 => true
  | 0x141 => true
  | 0x305 => true
  | 0x341 => true
  | 0x3A0 => true
  | 0x3A1 => true
  | 0x3A2 => true
  | 0x3A3 => true
  | 0x3A4 => true
  | 0x3A5 => true
  | 0x3A6 => true
  | 0x3A7 => true
  | 0x3A8 => true
  | 0x3A9 => true
  | 0x3AA => true
  | 0x3AB => true
  | 0x3AC => true
  | 0x3AD => true
  | 0x3AE => true
  | 0x3AF => true
  | 0x3B0 => true
  | 0x3B1 => true
  | 0x3B2 => true
  | 0x3B3 => true
  | 0x3B4 => true
  | 0x3B5 => true
  | 0x3B6 => true
  | 0x3B7 => true
  | 0x3B8 => true
  | 0x3B9 => true
  | 0x3BA => true
  | 0x3BB => true
  | 0x3BC => true
  | 0x3BD => true
  | 0x3BE => true
  | 0x3BF => true
  | 0x3C0 => true
  | 0x3C1 => true
  | 0x3C2 => true
  | 0x3C3 => true
  | 0x3C4 => true
  | 0x3C5 => true
  | 0x3C6 => true
  | 0x3C7 => true
  | 0x3C8 => true
  | 0x3C9 => true
  | 0x3CA => true
  | 0x3CB => true
  | 0x3CC => true
  | 0x3CD => true
  | 0x3CE => true
  | 0x3CF => true
  | 0x3D0 => true
  | 0x3D1 => true
  | 0x3D2 => true
  | 0x3D3 => true
  | 0x3D4 => true
  | 0x3D5 => true
  | 0x3D6 => true
  | 0x3D7 => true
  | 0x3D8 => true
  | 0x3D9 => true
  | 0x3DA => true
  | 0x3DB => true
  | 0x3DC => true
  | 0x3DD => true
  | 0x3DE => true
  | 0x3DF => true
  | 0x3E0 => true
  | 0x3E1 => true
  | 0x3E2 => true
  | 0x3E3 => true
  | 0x3E4 => true
  | 0x3E5 => true
  | 0x3E6 => true
  | 0x3E7 => true
  | 0x3E8 => true
  | 0x3E9 => true
  | 0x3EA => true
  | 0x3EB => true
  | 0x3EC => true
  | 0x3ED => true
  | 0x3EE => true
  | 0x3EF => true
  | 0x001 => true
  | 0x002 => true
  | 0x003 => true
  | 0x008 => true
  | 0x009 => true
  | 0x00A => true
  | 0x00F => true
  | 0xC20 => true
  | 0xC21 => true
  | 0xC22 => true
  | 0x321 => true
  | 0x721 => true
  | 0x322 => true
  | 0x722 => true
  | 0x7A0 => true
  | 0x7A1 => true
  | 0x7A2 => true
  | 0x7A3 => true
  | 0x7A4 => true
  | 0x7A5 => true
  | 0x5A8 => true
  | 0x7A8 => true
  | 0x6A8 => true
  | 0x30C => true
  | 0x30D => true
  | 0x30E => true
  | 0x30F => true
  | 0x31C => true
  | 0x31D => true
  | 0x31E => true
  | 0x31F => true
  | 0x60C => true
  | 0x60D => true
  | 0x60E => true
  | 0x60F => true
  | 0x61C => true
  | 0x61D => true
  | 0x61E => true
  | 0x61F => true
  | 0x10C => true
  | 0x10D => true
  | 0x10E => true
  | 0x10F => true
  | 0x680 => true
  | 0x280 => true
  | 0x180 => true
  | 0x015 => true
  | 0xC03 => true
  | 0xC04 => true
  | 0xC05 => true
  | 0xC06 => true
  | 0xC07 => true
  | 0xC08 => true
  | 0xC09 => true
  | 0xC0A => true
  | 0xC0B => true
  | 0xC0C => true
  | 0xC0D => true
  | 0xC0E => true
  | 0xC0F => true
  | 0xC10 => true
  | 0xC11 => true
  | 0xC12 => true
  | 0xC13 => true
  | 0xC14 => true
  | 0xC15 => true
  | 0xC16 => true
  | 0xC17 => true
  | 0xC18 => true
  | 0xC19 => true
  | 0xC1A => true
  | 0xC1B => true
  | 0xC1C => true
  | 0xC1D => true
  | 0xC1E => true
  | 0xC1F => true
  | 0xC83 => true
  | 0xC84 => true
  | 0xC85 => true
  | 0xC86 => true
  | 0xC87 => true
  | 0xC88 => true
  | 0xC89 => true
  | 0xC8A => true
  | 0xC8B => true
  | 0xC8C => true
  | 0xC8D => true
  | 0xC8E => true
  | 0xC8F => true
  | 0xC90 => true
  | 0xC91 => true
  | 0xC92 => true
  | 0xC93 => true
  | 0xC94 => true
  | 0xC95 => true
  | 0xC96 => true
  | 0xC97 => true
  | 0xC98 => true
  | 0xC99 => true
  | 0xC9A => true
  | 0xC9B => true
  | 0xC9C => true
  | 0xC9D => true
  | 0xC9E => true
  | 0xC9F => true
  | 0x723 => true
  | 0x724 => true
  | 0x725 => true
  | 0x726 => true
  | 0x727 => true
  | 0x728 => true
  | 0x729 => true
  | 0x72A => true
  | 0x72B => true
  | 0x72C => true
  | 0x72D => true
  | 0x72E => true
  | 0x72F => true
  | 0x730 => true
  | 0x731 => true
  | 0x732 => true
  | 0x733 => true
  | 0x734 => true
  | 0x735 => true
  | 0x736 => true
  | 0x737 => true
  | 0x738 => true
  | 0x739 => true
  | 0x73A => true
  | 0x73B => true
  | 0x73C => true
  | 0x73D => true
  | 0x73E => true
  | 0x73F => true
  | 0xDA0 => true
  | 0x14D => true
  | 0x15D => true
  | 0x24D => true
  | 0x25D => true
  | 0x011 => true
  | 0xC00 => true
  | 0xC01 => true
  | 0xC02 => true
  | 0xC80 => true
  | 0xC81 => true
  | 0xC82 => true
  | 0x181 => true
  | reg => true

def csr_name_map_backwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    match head_exp_ with
    | "misa" => (pure (some true))
    | "mstatus" => (pure (some true))
    | "mstatush" => (pure (some true))
    | "hstatus" => (pure (some true))
    | "mseccfg" => (pure (some true))
    | "mseccfgh" => (pure (some true))
    | "menvcfg" => (pure (some true))
    | "menvcfgh" => (pure (some true))
    | "senvcfg" => (pure (some true))
    | "henvcfg" => (pure (some true))
    | "henvcfgh" => (pure (some true))
    | "mcause" => (pure (some true))
    | "mtval" => (pure (some true))
    | "mscratch" => (pure (some true))
    | "scounteren" => (pure (some true))
    | "hcounteren" => (pure (some true))
    | "mcounteren" => (pure (some true))
    | "mcountinhibit" => (pure (some true))
    | "mvendorid" => (pure (some true))
    | "marchid" => (pure (some true))
    | "mimpid" => (pure (some true))
    | "mhartid" => (pure (some true))
    | "mconfigptr" => (pure (some true))
    | "mtinst" => (pure (some true))
    | "mtval2" => (pure (some true))
    | "htimedelta" => (pure (some true))
    | "htimedeltah" => (pure (some true))
    | "htval" => (pure (some true))
    | "htinst" => (pure (some true))
    | "vsstatus" => (pure (some true))
    | "sstatus" => (pure (some true))
    | "vsscratch" => (pure (some true))
    | "vscause" => (pure (some true))
    | "vstval" => (pure (some true))
    | "sscratch" => (pure (some true))
    | "scause" => (pure (some true))
    | "stval" => (pure (some true))
    | "hgeie" => (pure (some true))
    | "hgeip" => (pure (some true))
    | "mie" => (pure (some true))
    | "mip" => (pure (some true))
    | "medeleg" => (pure (some true))
    | "medelegh" => (pure (some true))
    | "mideleg" => (pure (some true))
    | "hvip" => (pure (some true))
    | "hie" => (pure (some true))
    | "hip" => (pure (some true))
    | "hedeleg" => (pure (some true))
    | "hideleg" => (pure (some true))
    | "hedelegh" => (pure (some true))
    | "sip" => (pure (some true))
    | "sie" => (pure (some true))
    | "vsie" => (pure (some true))
    | "vsip" => (pure (some true))
    | "mcycle" => (pure (some true))
    | "minstret" => (pure (some true))
    | "mcycleh" => (pure (some true))
    | "minstreth" => (pure (some true))
    | "mhpmevent3" => (pure (some true))
    | "mhpmevent4" => (pure (some true))
    | "mhpmevent5" => (pure (some true))
    | "mhpmevent6" => (pure (some true))
    | "mhpmevent7" => (pure (some true))
    | "mhpmevent8" => (pure (some true))
    | "mhpmevent9" => (pure (some true))
    | "mhpmevent10" => (pure (some true))
    | "mhpmevent11" => (pure (some true))
    | "mhpmevent12" => (pure (some true))
    | "mhpmevent13" => (pure (some true))
    | "mhpmevent14" => (pure (some true))
    | "mhpmevent15" => (pure (some true))
    | "mhpmevent16" => (pure (some true))
    | "mhpmevent17" => (pure (some true))
    | "mhpmevent18" => (pure (some true))
    | "mhpmevent19" => (pure (some true))
    | "mhpmevent20" => (pure (some true))
    | "mhpmevent21" => (pure (some true))
    | "mhpmevent22" => (pure (some true))
    | "mhpmevent23" => (pure (some true))
    | "mhpmevent24" => (pure (some true))
    | "mhpmevent25" => (pure (some true))
    | "mhpmevent26" => (pure (some true))
    | "mhpmevent27" => (pure (some true))
    | "mhpmevent28" => (pure (some true))
    | "mhpmevent29" => (pure (some true))
    | "mhpmevent30" => (pure (some true))
    | "mhpmevent31" => (pure (some true))
    | "mhpmcounter3" => (pure (some true))
    | "mhpmcounter4" => (pure (some true))
    | "mhpmcounter5" => (pure (some true))
    | "mhpmcounter6" => (pure (some true))
    | "mhpmcounter7" => (pure (some true))
    | "mhpmcounter8" => (pure (some true))
    | "mhpmcounter9" => (pure (some true))
    | "mhpmcounter10" => (pure (some true))
    | "mhpmcounter11" => (pure (some true))
    | "mhpmcounter12" => (pure (some true))
    | "mhpmcounter13" => (pure (some true))
    | "mhpmcounter14" => (pure (some true))
    | "mhpmcounter15" => (pure (some true))
    | "mhpmcounter16" => (pure (some true))
    | "mhpmcounter17" => (pure (some true))
    | "mhpmcounter18" => (pure (some true))
    | "mhpmcounter19" => (pure (some true))
    | "mhpmcounter20" => (pure (some true))
    | "mhpmcounter21" => (pure (some true))
    | "mhpmcounter22" => (pure (some true))
    | "mhpmcounter23" => (pure (some true))
    | "mhpmcounter24" => (pure (some true))
    | "mhpmcounter25" => (pure (some true))
    | "mhpmcounter26" => (pure (some true))
    | "mhpmcounter27" => (pure (some true))
    | "mhpmcounter28" => (pure (some true))
    | "mhpmcounter29" => (pure (some true))
    | "mhpmcounter30" => (pure (some true))
    | "mhpmcounter31" => (pure (some true))
    | "mhpmcounter3h" => (pure (some true))
    | "mhpmcounter4h" => (pure (some true))
    | "mhpmcounter5h" => (pure (some true))
    | "mhpmcounter6h" => (pure (some true))
    | "mhpmcounter7h" => (pure (some true))
    | "mhpmcounter8h" => (pure (some true))
    | "mhpmcounter9h" => (pure (some true))
    | "mhpmcounter10h" => (pure (some true))
    | "mhpmcounter11h" => (pure (some true))
    | "mhpmcounter12h" => (pure (some true))
    | "mhpmcounter13h" => (pure (some true))
    | "mhpmcounter14h" => (pure (some true))
    | "mhpmcounter15h" => (pure (some true))
    | "mhpmcounter16h" => (pure (some true))
    | "mhpmcounter17h" => (pure (some true))
    | "mhpmcounter18h" => (pure (some true))
    | "mhpmcounter19h" => (pure (some true))
    | "mhpmcounter20h" => (pure (some true))
    | "mhpmcounter21h" => (pure (some true))
    | "mhpmcounter22h" => (pure (some true))
    | "mhpmcounter23h" => (pure (some true))
    | "mhpmcounter24h" => (pure (some true))
    | "mhpmcounter25h" => (pure (some true))
    | "mhpmcounter26h" => (pure (some true))
    | "mhpmcounter27h" => (pure (some true))
    | "mhpmcounter28h" => (pure (some true))
    | "mhpmcounter29h" => (pure (some true))
    | "mhpmcounter30h" => (pure (some true))
    | "mhpmcounter31h" => (pure (some true))
    | "vstvec" => (pure (some true))
    | "vsepc" => (pure (some true))
    | "stvec" => (pure (some true))
    | "sepc" => (pure (some true))
    | "mtvec" => (pure (some true))
    | "mepc" => (pure (some true))
    | "pmpcfg0" => (pure (some true))
    | "pmpcfg1" => (pure (some true))
    | "pmpcfg2" => (pure (some true))
    | "pmpcfg3" => (pure (some true))
    | "pmpcfg4" => (pure (some true))
    | "pmpcfg5" => (pure (some true))
    | "pmpcfg6" => (pure (some true))
    | "pmpcfg7" => (pure (some true))
    | "pmpcfg8" => (pure (some true))
    | "pmpcfg9" => (pure (some true))
    | "pmpcfg10" => (pure (some true))
    | "pmpcfg11" => (pure (some true))
    | "pmpcfg12" => (pure (some true))
    | "pmpcfg13" => (pure (some true))
    | "pmpcfg14" => (pure (some true))
    | "pmpcfg15" => (pure (some true))
    | "pmpaddr0" => (pure (some true))
    | "pmpaddr1" => (pure (some true))
    | "pmpaddr2" => (pure (some true))
    | "pmpaddr3" => (pure (some true))
    | "pmpaddr4" => (pure (some true))
    | "pmpaddr5" => (pure (some true))
    | "pmpaddr6" => (pure (some true))
    | "pmpaddr7" => (pure (some true))
    | "pmpaddr8" => (pure (some true))
    | "pmpaddr9" => (pure (some true))
    | "pmpaddr10" => (pure (some true))
    | "pmpaddr11" => (pure (some true))
    | "pmpaddr12" => (pure (some true))
    | "pmpaddr13" => (pure (some true))
    | "pmpaddr14" => (pure (some true))
    | "pmpaddr15" => (pure (some true))
    | "pmpaddr16" => (pure (some true))
    | "pmpaddr17" => (pure (some true))
    | "pmpaddr18" => (pure (some true))
    | "pmpaddr19" => (pure (some true))
    | "pmpaddr20" => (pure (some true))
    | "pmpaddr21" => (pure (some true))
    | "pmpaddr22" => (pure (some true))
    | "pmpaddr23" => (pure (some true))
    | "pmpaddr24" => (pure (some true))
    | "pmpaddr25" => (pure (some true))
    | "pmpaddr26" => (pure (some true))
    | "pmpaddr27" => (pure (some true))
    | "pmpaddr28" => (pure (some true))
    | "pmpaddr29" => (pure (some true))
    | "pmpaddr30" => (pure (some true))
    | "pmpaddr31" => (pure (some true))
    | "pmpaddr32" => (pure (some true))
    | "pmpaddr33" => (pure (some true))
    | "pmpaddr34" => (pure (some true))
    | "pmpaddr35" => (pure (some true))
    | "pmpaddr36" => (pure (some true))
    | "pmpaddr37" => (pure (some true))
    | "pmpaddr38" => (pure (some true))
    | "pmpaddr39" => (pure (some true))
    | "pmpaddr40" => (pure (some true))
    | "pmpaddr41" => (pure (some true))
    | "pmpaddr42" => (pure (some true))
    | "pmpaddr43" => (pure (some true))
    | "pmpaddr44" => (pure (some true))
    | "pmpaddr45" => (pure (some true))
    | "pmpaddr46" => (pure (some true))
    | "pmpaddr47" => (pure (some true))
    | "pmpaddr48" => (pure (some true))
    | "pmpaddr49" => (pure (some true))
    | "pmpaddr50" => (pure (some true))
    | "pmpaddr51" => (pure (some true))
    | "pmpaddr52" => (pure (some true))
    | "pmpaddr53" => (pure (some true))
    | "pmpaddr54" => (pure (some true))
    | "pmpaddr55" => (pure (some true))
    | "pmpaddr56" => (pure (some true))
    | "pmpaddr57" => (pure (some true))
    | "pmpaddr58" => (pure (some true))
    | "pmpaddr59" => (pure (some true))
    | "pmpaddr60" => (pure (some true))
    | "pmpaddr61" => (pure (some true))
    | "pmpaddr62" => (pure (some true))
    | "pmpaddr63" => (pure (some true))
    | "fflags" => (pure (some true))
    | "frm" => (pure (some true))
    | "fcsr" => (pure (some true))
    | "vstart" => (pure (some true))
    | "vxsat" => (pure (some true))
    | "vxrm" => (pure (some true))
    | "vcsr" => (pure (some true))
    | "vl" => (pure (some true))
    | "vtype" => (pure (some true))
    | "vlenb" => (pure (some true))
    | "mcyclecfg" => (pure (some true))
    | "mcyclecfgh" => (pure (some true))
    | "minstretcfg" => (pure (some true))
    | "minstretcfgh" => (pure (some true))
    | "tselect" => (pure (some true))
    | "tdata1" => (pure (some true))
    | "tdata2" => (pure (some true))
    | "tdata3" => (pure (some true))
    | "tinfo" => (pure (some true))
    | "tcontrol" => (pure (some true))
    | "scontext" => (pure (some true))
    | "mcontext" => (pure (some true))
    | "hcontext" => (pure (some true))
    | "mstateen0" => (pure (some true))
    | "mstateen1" => (pure (some true))
    | "mstateen2" => (pure (some true))
    | "mstateen3" => (pure (some true))
    | "mstateen0h" => (pure (some true))
    | "mstateen1h" => (pure (some true))
    | "mstateen2h" => (pure (some true))
    | "mstateen3h" => (pure (some true))
    | "hstateen0" => (pure (some true))
    | "hstateen1" => (pure (some true))
    | "hstateen2" => (pure (some true))
    | "hstateen3" => (pure (some true))
    | "hstateen0h" => (pure (some true))
    | "hstateen1h" => (pure (some true))
    | "hstateen2h" => (pure (some true))
    | "hstateen3h" => (pure (some true))
    | "sstateen0" => (pure (some true))
    | "sstateen1" => (pure (some true))
    | "sstateen2" => (pure (some true))
    | "sstateen3" => (pure (some true))
    | "hgatp" => (pure (some true))
    | "vsatp" => (pure (some true))
    | "satp" => (pure (some true))
    | "seed" => (pure (some true))
    | "hpmcounter3" => (pure (some true))
    | "hpmcounter4" => (pure (some true))
    | "hpmcounter5" => (pure (some true))
    | "hpmcounter6" => (pure (some true))
    | "hpmcounter7" => (pure (some true))
    | "hpmcounter8" => (pure (some true))
    | "hpmcounter9" => (pure (some true))
    | "hpmcounter10" => (pure (some true))
    | "hpmcounter11" => (pure (some true))
    | "hpmcounter12" => (pure (some true))
    | "hpmcounter13" => (pure (some true))
    | "hpmcounter14" => (pure (some true))
    | "hpmcounter15" => (pure (some true))
    | "hpmcounter16" => (pure (some true))
    | "hpmcounter17" => (pure (some true))
    | "hpmcounter18" => (pure (some true))
    | "hpmcounter19" => (pure (some true))
    | "hpmcounter20" => (pure (some true))
    | "hpmcounter21" => (pure (some true))
    | "hpmcounter22" => (pure (some true))
    | "hpmcounter23" => (pure (some true))
    | "hpmcounter24" => (pure (some true))
    | "hpmcounter25" => (pure (some true))
    | "hpmcounter26" => (pure (some true))
    | "hpmcounter27" => (pure (some true))
    | "hpmcounter28" => (pure (some true))
    | "hpmcounter29" => (pure (some true))
    | "hpmcounter30" => (pure (some true))
    | "hpmcounter31" => (pure (some true))
    | "hpmcounter3h" => (pure (some true))
    | "hpmcounter4h" => (pure (some true))
    | "hpmcounter5h" => (pure (some true))
    | "hpmcounter6h" => (pure (some true))
    | "hpmcounter7h" => (pure (some true))
    | "hpmcounter8h" => (pure (some true))
    | "hpmcounter9h" => (pure (some true))
    | "hpmcounter10h" => (pure (some true))
    | "hpmcounter11h" => (pure (some true))
    | "hpmcounter12h" => (pure (some true))
    | "hpmcounter13h" => (pure (some true))
    | "hpmcounter14h" => (pure (some true))
    | "hpmcounter15h" => (pure (some true))
    | "hpmcounter16h" => (pure (some true))
    | "hpmcounter17h" => (pure (some true))
    | "hpmcounter18h" => (pure (some true))
    | "hpmcounter19h" => (pure (some true))
    | "hpmcounter20h" => (pure (some true))
    | "hpmcounter21h" => (pure (some true))
    | "hpmcounter22h" => (pure (some true))
    | "hpmcounter23h" => (pure (some true))
    | "hpmcounter24h" => (pure (some true))
    | "hpmcounter25h" => (pure (some true))
    | "hpmcounter26h" => (pure (some true))
    | "hpmcounter27h" => (pure (some true))
    | "hpmcounter28h" => (pure (some true))
    | "hpmcounter29h" => (pure (some true))
    | "hpmcounter30h" => (pure (some true))
    | "hpmcounter31h" => (pure (some true))
    | "mhpmevent3h" => (pure (some true))
    | "mhpmevent4h" => (pure (some true))
    | "mhpmevent5h" => (pure (some true))
    | "mhpmevent6h" => (pure (some true))
    | "mhpmevent7h" => (pure (some true))
    | "mhpmevent8h" => (pure (some true))
    | "mhpmevent9h" => (pure (some true))
    | "mhpmevent10h" => (pure (some true))
    | "mhpmevent11h" => (pure (some true))
    | "mhpmevent12h" => (pure (some true))
    | "mhpmevent13h" => (pure (some true))
    | "mhpmevent14h" => (pure (some true))
    | "mhpmevent15h" => (pure (some true))
    | "mhpmevent16h" => (pure (some true))
    | "mhpmevent17h" => (pure (some true))
    | "mhpmevent18h" => (pure (some true))
    | "mhpmevent19h" => (pure (some true))
    | "mhpmevent20h" => (pure (some true))
    | "mhpmevent21h" => (pure (some true))
    | "mhpmevent22h" => (pure (some true))
    | "mhpmevent23h" => (pure (some true))
    | "mhpmevent24h" => (pure (some true))
    | "mhpmevent25h" => (pure (some true))
    | "mhpmevent26h" => (pure (some true))
    | "mhpmevent27h" => (pure (some true))
    | "mhpmevent28h" => (pure (some true))
    | "mhpmevent29h" => (pure (some true))
    | "mhpmevent30h" => (pure (some true))
    | "mhpmevent31h" => (pure (some true))
    | "scountovf" => (pure (some true))
    | "stimecmp" => (pure (some true))
    | "stimecmph" => (pure (some true))
    | "vstimecmp" => (pure (some true))
    | "vstimecmph" => (pure (some true))
    | "ssp" => (pure (some true))
    | "cycle" => (pure (some true))
    | "time" => (pure (some true))
    | "instret" => (pure (some true))
    | "cycleh" => (pure (some true))
    | "timeh" => (pure (some true))
    | "instreth" => (pure (some true))
    | "srmcfg" => (pure (some true))
    | mapping0_ =>
      (do
        if ((hex_bits_12_backwards_matches mapping0_) : Bool)
        then
          (do
            match (← (hex_bits_12_backwards mapping0_)) with
            | reg => (pure (some true)))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

