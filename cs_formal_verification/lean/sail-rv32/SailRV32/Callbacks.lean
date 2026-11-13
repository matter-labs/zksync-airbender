import SailRV32.HexBits
import SailRV32.Xlen
import SailRV32.PlatformConfig

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

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, List.elem k_n [16, 32] -/
def fetch_callback (x_0 : (BitVec k_n)) : Unit :=
  ()

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

def csr_full_read_callback (x_0 : String) (x_1 : (BitVec 12)) (x_2 : (BitVec 32)) : Unit :=
  ()

def redirect_callback (x_0 : (BitVec 32)) : Unit :=
  ()

/-- Type quantifiers: k_ex1821789_ : Bool -/
def trap_callback (x_0 : Bool) (x_1 : (BitVec 6)) : Unit :=
  ()

/-- Type quantifiers: k_ex1821790_ : Bool -/
def xret_callback (x_0 : Bool) : Unit :=
  ()

/-- Type quantifiers: x_0 : Nat, 0 ≤ x_0 -/
def trigger_match_callback (x_0 : Nat) : Unit :=
  ()

/-- Type quantifiers: x_0 : Nat, 0 ≤ x_0 -/
def trigger_fire_callback (x_0 : Nat) : Unit :=
  ()

def csr_name_map_backwards (arg_ : String) : SailM (BitVec 12) := do
  let head_exp_ := arg_
  match (← do
    match head_exp_ with
    | "misa" => (pure (some 0x301#12))
    | "mstatus" => (pure (some 0x300#12))
    | "mstatush" => (pure (some 0x310#12))
    | "hstatus" => (pure (some 0x600#12))
    | "mseccfg" => (pure (some 0x747#12))
    | "mseccfgh" => (pure (some 0x757#12))
    | "menvcfg" => (pure (some 0x30A#12))
    | "menvcfgh" => (pure (some 0x31A#12))
    | "senvcfg" => (pure (some 0x10A#12))
    | "henvcfg" => (pure (some 0x60A#12))
    | "henvcfgh" => (pure (some 0x61A#12))
    | "mcause" => (pure (some 0x342#12))
    | "mtval" => (pure (some 0x343#12))
    | "mscratch" => (pure (some 0x340#12))
    | "scounteren" => (pure (some 0x106#12))
    | "hcounteren" => (pure (some 0x606#12))
    | "mcounteren" => (pure (some 0x306#12))
    | "mcountinhibit" => (pure (some 0x320#12))
    | "mvendorid" => (pure (some 0xF11#12))
    | "marchid" => (pure (some 0xF12#12))
    | "mimpid" => (pure (some 0xF13#12))
    | "mhartid" => (pure (some 0xF14#12))
    | "mconfigptr" => (pure (some 0xF15#12))
    | "mtinst" => (pure (some 0x34A#12))
    | "mtval2" => (pure (some 0x34B#12))
    | "htimedelta" => (pure (some 0x605#12))
    | "htimedeltah" => (pure (some 0x615#12))
    | "htval" => (pure (some 0x643#12))
    | "htinst" => (pure (some 0x64A#12))
    | "vsstatus" => (pure (some 0x200#12))
    | "sstatus" => (pure (some 0x100#12))
    | "vsscratch" => (pure (some 0x240#12))
    | "vscause" => (pure (some 0x242#12))
    | "vstval" => (pure (some 0x243#12))
    | "sscratch" => (pure (some 0x140#12))
    | "scause" => (pure (some 0x142#12))
    | "stval" => (pure (some 0x143#12))
    | "hgeie" => (pure (some 0x607#12))
    | "hgeip" => (pure (some 0xE12#12))
    | "mie" => (pure (some 0x304#12))
    | "mip" => (pure (some 0x344#12))
    | "medeleg" => (pure (some 0x302#12))
    | "medelegh" => (pure (some 0x312#12))
    | "mideleg" => (pure (some 0x303#12))
    | "hvip" => (pure (some 0x645#12))
    | "hie" => (pure (some 0x604#12))
    | "hip" => (pure (some 0x644#12))
    | "hedeleg" => (pure (some 0x602#12))
    | "hideleg" => (pure (some 0x603#12))
    | "hedelegh" => (pure (some 0x612#12))
    | "sip" => (pure (some 0x144#12))
    | "sie" => (pure (some 0x104#12))
    | "vsie" => (pure (some 0x204#12))
    | "vsip" => (pure (some 0x244#12))
    | "mcycle" => (pure (some 0xB00#12))
    | "minstret" => (pure (some 0xB02#12))
    | "mcycleh" => (pure (some 0xB80#12))
    | "minstreth" => (pure (some 0xB82#12))
    | "mhpmevent3" => (pure (some 0x323#12))
    | "mhpmevent4" => (pure (some 0x324#12))
    | "mhpmevent5" => (pure (some 0x325#12))
    | "mhpmevent6" => (pure (some 0x326#12))
    | "mhpmevent7" => (pure (some 0x327#12))
    | "mhpmevent8" => (pure (some 0x328#12))
    | "mhpmevent9" => (pure (some 0x329#12))
    | "mhpmevent10" => (pure (some 0x32A#12))
    | "mhpmevent11" => (pure (some 0x32B#12))
    | "mhpmevent12" => (pure (some 0x32C#12))
    | "mhpmevent13" => (pure (some 0x32D#12))
    | "mhpmevent14" => (pure (some 0x32E#12))
    | "mhpmevent15" => (pure (some 0x32F#12))
    | "mhpmevent16" => (pure (some 0x330#12))
    | "mhpmevent17" => (pure (some 0x331#12))
    | "mhpmevent18" => (pure (some 0x332#12))
    | "mhpmevent19" => (pure (some 0x333#12))
    | "mhpmevent20" => (pure (some 0x334#12))
    | "mhpmevent21" => (pure (some 0x335#12))
    | "mhpmevent22" => (pure (some 0x336#12))
    | "mhpmevent23" => (pure (some 0x337#12))
    | "mhpmevent24" => (pure (some 0x338#12))
    | "mhpmevent25" => (pure (some 0x339#12))
    | "mhpmevent26" => (pure (some 0x33A#12))
    | "mhpmevent27" => (pure (some 0x33B#12))
    | "mhpmevent28" => (pure (some 0x33C#12))
    | "mhpmevent29" => (pure (some 0x33D#12))
    | "mhpmevent30" => (pure (some 0x33E#12))
    | "mhpmevent31" => (pure (some 0x33F#12))
    | "mhpmcounter3" => (pure (some 0xB03#12))
    | "mhpmcounter4" => (pure (some 0xB04#12))
    | "mhpmcounter5" => (pure (some 0xB05#12))
    | "mhpmcounter6" => (pure (some 0xB06#12))
    | "mhpmcounter7" => (pure (some 0xB07#12))
    | "mhpmcounter8" => (pure (some 0xB08#12))
    | "mhpmcounter9" => (pure (some 0xB09#12))
    | "mhpmcounter10" => (pure (some 0xB0A#12))
    | "mhpmcounter11" => (pure (some 0xB0B#12))
    | "mhpmcounter12" => (pure (some 0xB0C#12))
    | "mhpmcounter13" => (pure (some 0xB0D#12))
    | "mhpmcounter14" => (pure (some 0xB0E#12))
    | "mhpmcounter15" => (pure (some 0xB0F#12))
    | "mhpmcounter16" => (pure (some 0xB10#12))
    | "mhpmcounter17" => (pure (some 0xB11#12))
    | "mhpmcounter18" => (pure (some 0xB12#12))
    | "mhpmcounter19" => (pure (some 0xB13#12))
    | "mhpmcounter20" => (pure (some 0xB14#12))
    | "mhpmcounter21" => (pure (some 0xB15#12))
    | "mhpmcounter22" => (pure (some 0xB16#12))
    | "mhpmcounter23" => (pure (some 0xB17#12))
    | "mhpmcounter24" => (pure (some 0xB18#12))
    | "mhpmcounter25" => (pure (some 0xB19#12))
    | "mhpmcounter26" => (pure (some 0xB1A#12))
    | "mhpmcounter27" => (pure (some 0xB1B#12))
    | "mhpmcounter28" => (pure (some 0xB1C#12))
    | "mhpmcounter29" => (pure (some 0xB1D#12))
    | "mhpmcounter30" => (pure (some 0xB1E#12))
    | "mhpmcounter31" => (pure (some 0xB1F#12))
    | "mhpmcounter3h" => (pure (some 0xB83#12))
    | "mhpmcounter4h" => (pure (some 0xB84#12))
    | "mhpmcounter5h" => (pure (some 0xB85#12))
    | "mhpmcounter6h" => (pure (some 0xB86#12))
    | "mhpmcounter7h" => (pure (some 0xB87#12))
    | "mhpmcounter8h" => (pure (some 0xB88#12))
    | "mhpmcounter9h" => (pure (some 0xB89#12))
    | "mhpmcounter10h" => (pure (some 0xB8A#12))
    | "mhpmcounter11h" => (pure (some 0xB8B#12))
    | "mhpmcounter12h" => (pure (some 0xB8C#12))
    | "mhpmcounter13h" => (pure (some 0xB8D#12))
    | "mhpmcounter14h" => (pure (some 0xB8E#12))
    | "mhpmcounter15h" => (pure (some 0xB8F#12))
    | "mhpmcounter16h" => (pure (some 0xB90#12))
    | "mhpmcounter17h" => (pure (some 0xB91#12))
    | "mhpmcounter18h" => (pure (some 0xB92#12))
    | "mhpmcounter19h" => (pure (some 0xB93#12))
    | "mhpmcounter20h" => (pure (some 0xB94#12))
    | "mhpmcounter21h" => (pure (some 0xB95#12))
    | "mhpmcounter22h" => (pure (some 0xB96#12))
    | "mhpmcounter23h" => (pure (some 0xB97#12))
    | "mhpmcounter24h" => (pure (some 0xB98#12))
    | "mhpmcounter25h" => (pure (some 0xB99#12))
    | "mhpmcounter26h" => (pure (some 0xB9A#12))
    | "mhpmcounter27h" => (pure (some 0xB9B#12))
    | "mhpmcounter28h" => (pure (some 0xB9C#12))
    | "mhpmcounter29h" => (pure (some 0xB9D#12))
    | "mhpmcounter30h" => (pure (some 0xB9E#12))
    | "mhpmcounter31h" => (pure (some 0xB9F#12))
    | "vstvec" => (pure (some 0x205#12))
    | "vsepc" => (pure (some 0x241#12))
    | "stvec" => (pure (some 0x105#12))
    | "sepc" => (pure (some 0x141#12))
    | "mtvec" => (pure (some 0x305#12))
    | "mepc" => (pure (some 0x341#12))
    | "pmpcfg0" => (pure (some 0x3A0#12))
    | "pmpcfg1" => (pure (some 0x3A1#12))
    | "pmpcfg2" => (pure (some 0x3A2#12))
    | "pmpcfg3" => (pure (some 0x3A3#12))
    | "pmpcfg4" => (pure (some 0x3A4#12))
    | "pmpcfg5" => (pure (some 0x3A5#12))
    | "pmpcfg6" => (pure (some 0x3A6#12))
    | "pmpcfg7" => (pure (some 0x3A7#12))
    | "pmpcfg8" => (pure (some 0x3A8#12))
    | "pmpcfg9" => (pure (some 0x3A9#12))
    | "pmpcfg10" => (pure (some 0x3AA#12))
    | "pmpcfg11" => (pure (some 0x3AB#12))
    | "pmpcfg12" => (pure (some 0x3AC#12))
    | "pmpcfg13" => (pure (some 0x3AD#12))
    | "pmpcfg14" => (pure (some 0x3AE#12))
    | "pmpcfg15" => (pure (some 0x3AF#12))
    | "pmpaddr0" => (pure (some 0x3B0#12))
    | "pmpaddr1" => (pure (some 0x3B1#12))
    | "pmpaddr2" => (pure (some 0x3B2#12))
    | "pmpaddr3" => (pure (some 0x3B3#12))
    | "pmpaddr4" => (pure (some 0x3B4#12))
    | "pmpaddr5" => (pure (some 0x3B5#12))
    | "pmpaddr6" => (pure (some 0x3B6#12))
    | "pmpaddr7" => (pure (some 0x3B7#12))
    | "pmpaddr8" => (pure (some 0x3B8#12))
    | "pmpaddr9" => (pure (some 0x3B9#12))
    | "pmpaddr10" => (pure (some 0x3BA#12))
    | "pmpaddr11" => (pure (some 0x3BB#12))
    | "pmpaddr12" => (pure (some 0x3BC#12))
    | "pmpaddr13" => (pure (some 0x3BD#12))
    | "pmpaddr14" => (pure (some 0x3BE#12))
    | "pmpaddr15" => (pure (some 0x3BF#12))
    | "pmpaddr16" => (pure (some 0x3C0#12))
    | "pmpaddr17" => (pure (some 0x3C1#12))
    | "pmpaddr18" => (pure (some 0x3C2#12))
    | "pmpaddr19" => (pure (some 0x3C3#12))
    | "pmpaddr20" => (pure (some 0x3C4#12))
    | "pmpaddr21" => (pure (some 0x3C5#12))
    | "pmpaddr22" => (pure (some 0x3C6#12))
    | "pmpaddr23" => (pure (some 0x3C7#12))
    | "pmpaddr24" => (pure (some 0x3C8#12))
    | "pmpaddr25" => (pure (some 0x3C9#12))
    | "pmpaddr26" => (pure (some 0x3CA#12))
    | "pmpaddr27" => (pure (some 0x3CB#12))
    | "pmpaddr28" => (pure (some 0x3CC#12))
    | "pmpaddr29" => (pure (some 0x3CD#12))
    | "pmpaddr30" => (pure (some 0x3CE#12))
    | "pmpaddr31" => (pure (some 0x3CF#12))
    | "pmpaddr32" => (pure (some 0x3D0#12))
    | "pmpaddr33" => (pure (some 0x3D1#12))
    | "pmpaddr34" => (pure (some 0x3D2#12))
    | "pmpaddr35" => (pure (some 0x3D3#12))
    | "pmpaddr36" => (pure (some 0x3D4#12))
    | "pmpaddr37" => (pure (some 0x3D5#12))
    | "pmpaddr38" => (pure (some 0x3D6#12))
    | "pmpaddr39" => (pure (some 0x3D7#12))
    | "pmpaddr40" => (pure (some 0x3D8#12))
    | "pmpaddr41" => (pure (some 0x3D9#12))
    | "pmpaddr42" => (pure (some 0x3DA#12))
    | "pmpaddr43" => (pure (some 0x3DB#12))
    | "pmpaddr44" => (pure (some 0x3DC#12))
    | "pmpaddr45" => (pure (some 0x3DD#12))
    | "pmpaddr46" => (pure (some 0x3DE#12))
    | "pmpaddr47" => (pure (some 0x3DF#12))
    | "pmpaddr48" => (pure (some 0x3E0#12))
    | "pmpaddr49" => (pure (some 0x3E1#12))
    | "pmpaddr50" => (pure (some 0x3E2#12))
    | "pmpaddr51" => (pure (some 0x3E3#12))
    | "pmpaddr52" => (pure (some 0x3E4#12))
    | "pmpaddr53" => (pure (some 0x3E5#12))
    | "pmpaddr54" => (pure (some 0x3E6#12))
    | "pmpaddr55" => (pure (some 0x3E7#12))
    | "pmpaddr56" => (pure (some 0x3E8#12))
    | "pmpaddr57" => (pure (some 0x3E9#12))
    | "pmpaddr58" => (pure (some 0x3EA#12))
    | "pmpaddr59" => (pure (some 0x3EB#12))
    | "pmpaddr60" => (pure (some 0x3EC#12))
    | "pmpaddr61" => (pure (some 0x3ED#12))
    | "pmpaddr62" => (pure (some 0x3EE#12))
    | "pmpaddr63" => (pure (some 0x3EF#12))
    | "fflags" => (pure (some 0x001#12))
    | "frm" => (pure (some 0x002#12))
    | "fcsr" => (pure (some 0x003#12))
    | "vstart" => (pure (some 0x008#12))
    | "vxsat" => (pure (some 0x009#12))
    | "vxrm" => (pure (some 0x00A#12))
    | "vcsr" => (pure (some 0x00F#12))
    | "vl" => (pure (some 0xC20#12))
    | "vtype" => (pure (some 0xC21#12))
    | "vlenb" => (pure (some 0xC22#12))
    | "mcyclecfg" => (pure (some 0x321#12))
    | "mcyclecfgh" => (pure (some 0x721#12))
    | "minstretcfg" => (pure (some 0x322#12))
    | "minstretcfgh" => (pure (some 0x722#12))
    | "tselect" => (pure (some 0x7A0#12))
    | "tdata1" => (pure (some 0x7A1#12))
    | "tdata2" => (pure (some 0x7A2#12))
    | "tdata3" => (pure (some 0x7A3#12))
    | "tinfo" => (pure (some 0x7A4#12))
    | "tcontrol" => (pure (some 0x7A5#12))
    | "scontext" => (pure (some 0x5A8#12))
    | "mcontext" => (pure (some 0x7A8#12))
    | "hcontext" => (pure (some 0x6A8#12))
    | "mstateen0" => (pure (some 0x30C#12))
    | "mstateen1" => (pure (some 0x30D#12))
    | "mstateen2" => (pure (some 0x30E#12))
    | "mstateen3" => (pure (some 0x30F#12))
    | "mstateen0h" => (pure (some 0x31C#12))
    | "mstateen1h" => (pure (some 0x31D#12))
    | "mstateen2h" => (pure (some 0x31E#12))
    | "mstateen3h" => (pure (some 0x31F#12))
    | "hstateen0" => (pure (some 0x60C#12))
    | "hstateen1" => (pure (some 0x60D#12))
    | "hstateen2" => (pure (some 0x60E#12))
    | "hstateen3" => (pure (some 0x60F#12))
    | "hstateen0h" => (pure (some 0x61C#12))
    | "hstateen1h" => (pure (some 0x61D#12))
    | "hstateen2h" => (pure (some 0x61E#12))
    | "hstateen3h" => (pure (some 0x61F#12))
    | "sstateen0" => (pure (some 0x10C#12))
    | "sstateen1" => (pure (some 0x10D#12))
    | "sstateen2" => (pure (some 0x10E#12))
    | "sstateen3" => (pure (some 0x10F#12))
    | "hgatp" => (pure (some 0x680#12))
    | "vsatp" => (pure (some 0x280#12))
    | "satp" => (pure (some 0x180#12))
    | "seed" => (pure (some 0x015#12))
    | "hpmcounter3" => (pure (some 0xC03#12))
    | "hpmcounter4" => (pure (some 0xC04#12))
    | "hpmcounter5" => (pure (some 0xC05#12))
    | "hpmcounter6" => (pure (some 0xC06#12))
    | "hpmcounter7" => (pure (some 0xC07#12))
    | "hpmcounter8" => (pure (some 0xC08#12))
    | "hpmcounter9" => (pure (some 0xC09#12))
    | "hpmcounter10" => (pure (some 0xC0A#12))
    | "hpmcounter11" => (pure (some 0xC0B#12))
    | "hpmcounter12" => (pure (some 0xC0C#12))
    | "hpmcounter13" => (pure (some 0xC0D#12))
    | "hpmcounter14" => (pure (some 0xC0E#12))
    | "hpmcounter15" => (pure (some 0xC0F#12))
    | "hpmcounter16" => (pure (some 0xC10#12))
    | "hpmcounter17" => (pure (some 0xC11#12))
    | "hpmcounter18" => (pure (some 0xC12#12))
    | "hpmcounter19" => (pure (some 0xC13#12))
    | "hpmcounter20" => (pure (some 0xC14#12))
    | "hpmcounter21" => (pure (some 0xC15#12))
    | "hpmcounter22" => (pure (some 0xC16#12))
    | "hpmcounter23" => (pure (some 0xC17#12))
    | "hpmcounter24" => (pure (some 0xC18#12))
    | "hpmcounter25" => (pure (some 0xC19#12))
    | "hpmcounter26" => (pure (some 0xC1A#12))
    | "hpmcounter27" => (pure (some 0xC1B#12))
    | "hpmcounter28" => (pure (some 0xC1C#12))
    | "hpmcounter29" => (pure (some 0xC1D#12))
    | "hpmcounter30" => (pure (some 0xC1E#12))
    | "hpmcounter31" => (pure (some 0xC1F#12))
    | "hpmcounter3h" => (pure (some 0xC83#12))
    | "hpmcounter4h" => (pure (some 0xC84#12))
    | "hpmcounter5h" => (pure (some 0xC85#12))
    | "hpmcounter6h" => (pure (some 0xC86#12))
    | "hpmcounter7h" => (pure (some 0xC87#12))
    | "hpmcounter8h" => (pure (some 0xC88#12))
    | "hpmcounter9h" => (pure (some 0xC89#12))
    | "hpmcounter10h" => (pure (some 0xC8A#12))
    | "hpmcounter11h" => (pure (some 0xC8B#12))
    | "hpmcounter12h" => (pure (some 0xC8C#12))
    | "hpmcounter13h" => (pure (some 0xC8D#12))
    | "hpmcounter14h" => (pure (some 0xC8E#12))
    | "hpmcounter15h" => (pure (some 0xC8F#12))
    | "hpmcounter16h" => (pure (some 0xC90#12))
    | "hpmcounter17h" => (pure (some 0xC91#12))
    | "hpmcounter18h" => (pure (some 0xC92#12))
    | "hpmcounter19h" => (pure (some 0xC93#12))
    | "hpmcounter20h" => (pure (some 0xC94#12))
    | "hpmcounter21h" => (pure (some 0xC95#12))
    | "hpmcounter22h" => (pure (some 0xC96#12))
    | "hpmcounter23h" => (pure (some 0xC97#12))
    | "hpmcounter24h" => (pure (some 0xC98#12))
    | "hpmcounter25h" => (pure (some 0xC99#12))
    | "hpmcounter26h" => (pure (some 0xC9A#12))
    | "hpmcounter27h" => (pure (some 0xC9B#12))
    | "hpmcounter28h" => (pure (some 0xC9C#12))
    | "hpmcounter29h" => (pure (some 0xC9D#12))
    | "hpmcounter30h" => (pure (some 0xC9E#12))
    | "hpmcounter31h" => (pure (some 0xC9F#12))
    | "mhpmevent3h" => (pure (some 0x723#12))
    | "mhpmevent4h" => (pure (some 0x724#12))
    | "mhpmevent5h" => (pure (some 0x725#12))
    | "mhpmevent6h" => (pure (some 0x726#12))
    | "mhpmevent7h" => (pure (some 0x727#12))
    | "mhpmevent8h" => (pure (some 0x728#12))
    | "mhpmevent9h" => (pure (some 0x729#12))
    | "mhpmevent10h" => (pure (some 0x72A#12))
    | "mhpmevent11h" => (pure (some 0x72B#12))
    | "mhpmevent12h" => (pure (some 0x72C#12))
    | "mhpmevent13h" => (pure (some 0x72D#12))
    | "mhpmevent14h" => (pure (some 0x72E#12))
    | "mhpmevent15h" => (pure (some 0x72F#12))
    | "mhpmevent16h" => (pure (some 0x730#12))
    | "mhpmevent17h" => (pure (some 0x731#12))
    | "mhpmevent18h" => (pure (some 0x732#12))
    | "mhpmevent19h" => (pure (some 0x733#12))
    | "mhpmevent20h" => (pure (some 0x734#12))
    | "mhpmevent21h" => (pure (some 0x735#12))
    | "mhpmevent22h" => (pure (some 0x736#12))
    | "mhpmevent23h" => (pure (some 0x737#12))
    | "mhpmevent24h" => (pure (some 0x738#12))
    | "mhpmevent25h" => (pure (some 0x739#12))
    | "mhpmevent26h" => (pure (some 0x73A#12))
    | "mhpmevent27h" => (pure (some 0x73B#12))
    | "mhpmevent28h" => (pure (some 0x73C#12))
    | "mhpmevent29h" => (pure (some 0x73D#12))
    | "mhpmevent30h" => (pure (some 0x73E#12))
    | "mhpmevent31h" => (pure (some 0x73F#12))
    | "scountovf" => (pure (some 0xDA0#12))
    | "stimecmp" => (pure (some 0x14D#12))
    | "stimecmph" => (pure (some 0x15D#12))
    | "vstimecmp" => (pure (some 0x24D#12))
    | "vstimecmph" => (pure (some 0x25D#12))
    | "ssp" => (pure (some 0x011#12))
    | "cycle" => (pure (some 0xC00#12))
    | "time" => (pure (some 0xC01#12))
    | "instret" => (pure (some 0xC02#12))
    | "cycleh" => (pure (some 0xC80#12))
    | "timeh" => (pure (some 0xC81#12))
    | "instreth" => (pure (some 0xC82#12))
    | "srmcfg" => (pure (some 0x181#12))
    | mapping0_ =>
      (do
        if ((hex_bits_12_backwards_matches mapping0_) : Bool)
        then
          (do
            match (← (hex_bits_12_backwards mapping0_)) with
            | reg => (pure (some reg)))
        else (pure none))) with
  | .some result => (pure result)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def csr_name_write_callback (name : String) (value : (BitVec 32)) : SailM Unit := do
  let csr ← do (csr_name_map_backwards name)
  (pure (csr_full_write_callback name csr value))

def csr_id_write_callback (csr : (BitVec 12)) (value : (BitVec 32)) : SailM Unit := do
  let name ← do (csr_name_map_forwards csr)
  (pure (csr_full_write_callback name csr value))

def csr_name_read_callback (name : String) (value : (BitVec 32)) : SailM Unit := do
  let csr ← do (csr_name_map_backwards name)
  (pure (csr_full_read_callback name csr value))

def csr_id_read_callback (csr : (BitVec 12)) (value : (BitVec 32)) : SailM Unit := do
  let name ← do (csr_name_map_forwards csr)
  (pure (csr_full_read_callback name csr value))

def long_csr_write_callback (name : String) (name_high : String) (value : (BitVec 64)) : SailM Unit := do
  (csr_name_write_callback name (Sail.BitVec.extractLsb value (xlen -i 1) 0))
  (csr_name_write_callback name_high (Sail.BitVec.extractLsb value 63 32))

