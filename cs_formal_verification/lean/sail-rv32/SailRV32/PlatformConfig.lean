import SailRV32.SailRV32
import SailRV32.Flow
import SailRV32.Mapping
import SailRV32.Vector
import SailRV32.HexBits
import SailRV32.HexBitsSigned
import SailRV32.DecBits
import SailRV32.Prelude
import SailRV32.Errors
import SailRV32.AextTypes
import SailRV32.PmTypes
import SailRV32.Xlen
import SailRV32.Flen
import SailRV32.Vlen

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

def plat_have_mcountinhibit : Bool := true

def plat_mcountinhibit_writable_bits : (BitVec 32) := 0b11111111111111111111111111111101#32

def plat_mtvec_direct_mode_supported : Bool := true

def plat_mtvec_vectored_mode_supported : Bool := true

def plat_stvec_direct_mode_supported : Bool := true

def plat_stvec_vectored_mode_supported : Bool := true

def plat_vstvec_direct_mode_supported : Bool := true

def plat_vstvec_vectored_mode_supported : Bool := true

def plat_mtvec_direct_base_alignment_exp : tvec_alignment := 2

def plat_mtvec_vectored_base_alignment_exp : tvec_alignment := 2

def plat_stvec_vectored_base_alignment_exp : tvec_alignment := 2

def plat_vstvec_vectored_base_alignment_exp : tvec_alignment := 2

def plat_medeleg_delegatable_bits : (BitVec 64) :=
  0b0000000000000000000000000000000000000000111111001011011111111111#64

def plat_mideleg_delegatable_bits : xlenbits := (sail_mask 32 0b00000000000000000010001000100010#32)

def plat_cache_block_size_exp : Nat := 6

def plat_reservation_set_size_exp : Nat := 3

def plat_reservation_require_exact_addr_match : Bool := false

def plat_reservation_invalidate_on_same_hart_store : Bool := false

def undefined_misaligned_exception (_ : Unit) : SailM misaligned_exception := do
  (internal_pick [AccessFault, AlignmentException])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def misaligned_exception_of_num (arg_ : Nat) : misaligned_exception :=
  match arg_ with
  | 0 => AccessFault
  | _ => AlignmentException

def num_of_misaligned_exception (arg_ : misaligned_exception) : Int :=
  match arg_ with
  | .AccessFault => 0
  | .AlignmentException => 1

def misaligned_exception_str_forwards (arg_ : misaligned_exception) : String :=
  match arg_ with
  | .AccessFault => "AccessFault"
  | .AlignmentException => "AlignmentException"

def misaligned_exception_str_backwards (arg_ : String) : SailM misaligned_exception := do
  match arg_ with
  | "AccessFault" => (pure AccessFault)
  | "AlignmentException" => (pure AlignmentException)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def misaligned_exception_str_forwards_matches (arg_ : misaligned_exception) : Bool :=
  match arg_ with
  | .AccessFault => true
  | .AlignmentException => true

def misaligned_exception_str_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "AccessFault" => true
  | "AlignmentException" => true
  | _ => false

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

def atomic_support_str_backwards (arg_ : String) : SailM AtomicSupport := do
  match arg_ with
  | "AMONone" => (pure AMONone)
  | "AMOSwap" => (pure AMOSwap)
  | "AMOLogical" => (pure AMOLogical)
  | "AMOArithmetic" => (pure AMOArithmetic)
  | "AMOCASW" => (pure AMOCASW)
  | "AMOCASD" => (pure AMOCASD)
  | "AMOCASQ" => (pure AMOCASQ)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def atomic_support_str_forwards (arg_ : AtomicSupport) : String :=
  match arg_ with
  | .AMONone => "AMONone"
  | .AMOSwap => "AMOSwap"
  | .AMOLogical => "AMOLogical"
  | .AMOArithmetic => "AMOArithmetic"
  | .AMOCASW => "AMOCASW"
  | .AMOCASD => "AMOCASD"
  | .AMOCASQ => "AMOCASQ"

def csr_name_map_forwards (arg_ : (BitVec 12)) : SailM String := do
  match arg_ with
  | 0x301 => (pure "misa")
  | 0x300 => (pure "mstatus")
  | 0x310 => (pure "mstatush")
  | 0x600 => (pure "hstatus")
  | 0x747 => (pure "mseccfg")
  | 0x757 => (pure "mseccfgh")
  | 0x30A => (pure "menvcfg")
  | 0x31A => (pure "menvcfgh")
  | 0x10A => (pure "senvcfg")
  | 0x60A => (pure "henvcfg")
  | 0x61A => (pure "henvcfgh")
  | 0x342 => (pure "mcause")
  | 0x343 => (pure "mtval")
  | 0x340 => (pure "mscratch")
  | 0x106 => (pure "scounteren")
  | 0x606 => (pure "hcounteren")
  | 0x306 => (pure "mcounteren")
  | 0x320 => (pure "mcountinhibit")
  | 0xF11 => (pure "mvendorid")
  | 0xF12 => (pure "marchid")
  | 0xF13 => (pure "mimpid")
  | 0xF14 => (pure "mhartid")
  | 0xF15 => (pure "mconfigptr")
  | 0x34A => (pure "mtinst")
  | 0x34B => (pure "mtval2")
  | 0x605 => (pure "htimedelta")
  | 0x615 => (pure "htimedeltah")
  | 0x643 => (pure "htval")
  | 0x64A => (pure "htinst")
  | 0x200 => (pure "vsstatus")
  | 0x100 => (pure "sstatus")
  | 0x240 => (pure "vsscratch")
  | 0x242 => (pure "vscause")
  | 0x243 => (pure "vstval")
  | 0x140 => (pure "sscratch")
  | 0x142 => (pure "scause")
  | 0x143 => (pure "stval")
  | 0x607 => (pure "hgeie")
  | 0xE12 => (pure "hgeip")
  | 0x304 => (pure "mie")
  | 0x344 => (pure "mip")
  | 0x302 => (pure "medeleg")
  | 0x312 => (pure "medelegh")
  | 0x303 => (pure "mideleg")
  | 0x645 => (pure "hvip")
  | 0x604 => (pure "hie")
  | 0x644 => (pure "hip")
  | 0x602 => (pure "hedeleg")
  | 0x603 => (pure "hideleg")
  | 0x612 => (pure "hedelegh")
  | 0x144 => (pure "sip")
  | 0x104 => (pure "sie")
  | 0x204 => (pure "vsie")
  | 0x244 => (pure "vsip")
  | 0xB00 => (pure "mcycle")
  | 0xB02 => (pure "minstret")
  | 0xB80 => (pure "mcycleh")
  | 0xB82 => (pure "minstreth")
  | 0x323 => (pure "mhpmevent3")
  | 0x324 => (pure "mhpmevent4")
  | 0x325 => (pure "mhpmevent5")
  | 0x326 => (pure "mhpmevent6")
  | 0x327 => (pure "mhpmevent7")
  | 0x328 => (pure "mhpmevent8")
  | 0x329 => (pure "mhpmevent9")
  | 0x32A => (pure "mhpmevent10")
  | 0x32B => (pure "mhpmevent11")
  | 0x32C => (pure "mhpmevent12")
  | 0x32D => (pure "mhpmevent13")
  | 0x32E => (pure "mhpmevent14")
  | 0x32F => (pure "mhpmevent15")
  | 0x330 => (pure "mhpmevent16")
  | 0x331 => (pure "mhpmevent17")
  | 0x332 => (pure "mhpmevent18")
  | 0x333 => (pure "mhpmevent19")
  | 0x334 => (pure "mhpmevent20")
  | 0x335 => (pure "mhpmevent21")
  | 0x336 => (pure "mhpmevent22")
  | 0x337 => (pure "mhpmevent23")
  | 0x338 => (pure "mhpmevent24")
  | 0x339 => (pure "mhpmevent25")
  | 0x33A => (pure "mhpmevent26")
  | 0x33B => (pure "mhpmevent27")
  | 0x33C => (pure "mhpmevent28")
  | 0x33D => (pure "mhpmevent29")
  | 0x33E => (pure "mhpmevent30")
  | 0x33F => (pure "mhpmevent31")
  | 0xB03 => (pure "mhpmcounter3")
  | 0xB04 => (pure "mhpmcounter4")
  | 0xB05 => (pure "mhpmcounter5")
  | 0xB06 => (pure "mhpmcounter6")
  | 0xB07 => (pure "mhpmcounter7")
  | 0xB08 => (pure "mhpmcounter8")
  | 0xB09 => (pure "mhpmcounter9")
  | 0xB0A => (pure "mhpmcounter10")
  | 0xB0B => (pure "mhpmcounter11")
  | 0xB0C => (pure "mhpmcounter12")
  | 0xB0D => (pure "mhpmcounter13")
  | 0xB0E => (pure "mhpmcounter14")
  | 0xB0F => (pure "mhpmcounter15")
  | 0xB10 => (pure "mhpmcounter16")
  | 0xB11 => (pure "mhpmcounter17")
  | 0xB12 => (pure "mhpmcounter18")
  | 0xB13 => (pure "mhpmcounter19")
  | 0xB14 => (pure "mhpmcounter20")
  | 0xB15 => (pure "mhpmcounter21")
  | 0xB16 => (pure "mhpmcounter22")
  | 0xB17 => (pure "mhpmcounter23")
  | 0xB18 => (pure "mhpmcounter24")
  | 0xB19 => (pure "mhpmcounter25")
  | 0xB1A => (pure "mhpmcounter26")
  | 0xB1B => (pure "mhpmcounter27")
  | 0xB1C => (pure "mhpmcounter28")
  | 0xB1D => (pure "mhpmcounter29")
  | 0xB1E => (pure "mhpmcounter30")
  | 0xB1F => (pure "mhpmcounter31")
  | 0xB83 => (pure "mhpmcounter3h")
  | 0xB84 => (pure "mhpmcounter4h")
  | 0xB85 => (pure "mhpmcounter5h")
  | 0xB86 => (pure "mhpmcounter6h")
  | 0xB87 => (pure "mhpmcounter7h")
  | 0xB88 => (pure "mhpmcounter8h")
  | 0xB89 => (pure "mhpmcounter9h")
  | 0xB8A => (pure "mhpmcounter10h")
  | 0xB8B => (pure "mhpmcounter11h")
  | 0xB8C => (pure "mhpmcounter12h")
  | 0xB8D => (pure "mhpmcounter13h")
  | 0xB8E => (pure "mhpmcounter14h")
  | 0xB8F => (pure "mhpmcounter15h")
  | 0xB90 => (pure "mhpmcounter16h")
  | 0xB91 => (pure "mhpmcounter17h")
  | 0xB92 => (pure "mhpmcounter18h")
  | 0xB93 => (pure "mhpmcounter19h")
  | 0xB94 => (pure "mhpmcounter20h")
  | 0xB95 => (pure "mhpmcounter21h")
  | 0xB96 => (pure "mhpmcounter22h")
  | 0xB97 => (pure "mhpmcounter23h")
  | 0xB98 => (pure "mhpmcounter24h")
  | 0xB99 => (pure "mhpmcounter25h")
  | 0xB9A => (pure "mhpmcounter26h")
  | 0xB9B => (pure "mhpmcounter27h")
  | 0xB9C => (pure "mhpmcounter28h")
  | 0xB9D => (pure "mhpmcounter29h")
  | 0xB9E => (pure "mhpmcounter30h")
  | 0xB9F => (pure "mhpmcounter31h")
  | 0x205 => (pure "vstvec")
  | 0x241 => (pure "vsepc")
  | 0x105 => (pure "stvec")
  | 0x141 => (pure "sepc")
  | 0x305 => (pure "mtvec")
  | 0x341 => (pure "mepc")
  | 0x3A0 => (pure "pmpcfg0")
  | 0x3A1 => (pure "pmpcfg1")
  | 0x3A2 => (pure "pmpcfg2")
  | 0x3A3 => (pure "pmpcfg3")
  | 0x3A4 => (pure "pmpcfg4")
  | 0x3A5 => (pure "pmpcfg5")
  | 0x3A6 => (pure "pmpcfg6")
  | 0x3A7 => (pure "pmpcfg7")
  | 0x3A8 => (pure "pmpcfg8")
  | 0x3A9 => (pure "pmpcfg9")
  | 0x3AA => (pure "pmpcfg10")
  | 0x3AB => (pure "pmpcfg11")
  | 0x3AC => (pure "pmpcfg12")
  | 0x3AD => (pure "pmpcfg13")
  | 0x3AE => (pure "pmpcfg14")
  | 0x3AF => (pure "pmpcfg15")
  | 0x3B0 => (pure "pmpaddr0")
  | 0x3B1 => (pure "pmpaddr1")
  | 0x3B2 => (pure "pmpaddr2")
  | 0x3B3 => (pure "pmpaddr3")
  | 0x3B4 => (pure "pmpaddr4")
  | 0x3B5 => (pure "pmpaddr5")
  | 0x3B6 => (pure "pmpaddr6")
  | 0x3B7 => (pure "pmpaddr7")
  | 0x3B8 => (pure "pmpaddr8")
  | 0x3B9 => (pure "pmpaddr9")
  | 0x3BA => (pure "pmpaddr10")
  | 0x3BB => (pure "pmpaddr11")
  | 0x3BC => (pure "pmpaddr12")
  | 0x3BD => (pure "pmpaddr13")
  | 0x3BE => (pure "pmpaddr14")
  | 0x3BF => (pure "pmpaddr15")
  | 0x3C0 => (pure "pmpaddr16")
  | 0x3C1 => (pure "pmpaddr17")
  | 0x3C2 => (pure "pmpaddr18")
  | 0x3C3 => (pure "pmpaddr19")
  | 0x3C4 => (pure "pmpaddr20")
  | 0x3C5 => (pure "pmpaddr21")
  | 0x3C6 => (pure "pmpaddr22")
  | 0x3C7 => (pure "pmpaddr23")
  | 0x3C8 => (pure "pmpaddr24")
  | 0x3C9 => (pure "pmpaddr25")
  | 0x3CA => (pure "pmpaddr26")
  | 0x3CB => (pure "pmpaddr27")
  | 0x3CC => (pure "pmpaddr28")
  | 0x3CD => (pure "pmpaddr29")
  | 0x3CE => (pure "pmpaddr30")
  | 0x3CF => (pure "pmpaddr31")
  | 0x3D0 => (pure "pmpaddr32")
  | 0x3D1 => (pure "pmpaddr33")
  | 0x3D2 => (pure "pmpaddr34")
  | 0x3D3 => (pure "pmpaddr35")
  | 0x3D4 => (pure "pmpaddr36")
  | 0x3D5 => (pure "pmpaddr37")
  | 0x3D6 => (pure "pmpaddr38")
  | 0x3D7 => (pure "pmpaddr39")
  | 0x3D8 => (pure "pmpaddr40")
  | 0x3D9 => (pure "pmpaddr41")
  | 0x3DA => (pure "pmpaddr42")
  | 0x3DB => (pure "pmpaddr43")
  | 0x3DC => (pure "pmpaddr44")
  | 0x3DD => (pure "pmpaddr45")
  | 0x3DE => (pure "pmpaddr46")
  | 0x3DF => (pure "pmpaddr47")
  | 0x3E0 => (pure "pmpaddr48")
  | 0x3E1 => (pure "pmpaddr49")
  | 0x3E2 => (pure "pmpaddr50")
  | 0x3E3 => (pure "pmpaddr51")
  | 0x3E4 => (pure "pmpaddr52")
  | 0x3E5 => (pure "pmpaddr53")
  | 0x3E6 => (pure "pmpaddr54")
  | 0x3E7 => (pure "pmpaddr55")
  | 0x3E8 => (pure "pmpaddr56")
  | 0x3E9 => (pure "pmpaddr57")
  | 0x3EA => (pure "pmpaddr58")
  | 0x3EB => (pure "pmpaddr59")
  | 0x3EC => (pure "pmpaddr60")
  | 0x3ED => (pure "pmpaddr61")
  | 0x3EE => (pure "pmpaddr62")
  | 0x3EF => (pure "pmpaddr63")
  | 0x001 => (pure "fflags")
  | 0x002 => (pure "frm")
  | 0x003 => (pure "fcsr")
  | 0x008 => (pure "vstart")
  | 0x009 => (pure "vxsat")
  | 0x00A => (pure "vxrm")
  | 0x00F => (pure "vcsr")
  | 0xC20 => (pure "vl")
  | 0xC21 => (pure "vtype")
  | 0xC22 => (pure "vlenb")
  | 0x321 => (pure "mcyclecfg")
  | 0x721 => (pure "mcyclecfgh")
  | 0x322 => (pure "minstretcfg")
  | 0x722 => (pure "minstretcfgh")
  | 0x7A0 => (pure "tselect")
  | 0x7A1 => (pure "tdata1")
  | 0x7A2 => (pure "tdata2")
  | 0x7A3 => (pure "tdata3")
  | 0x7A4 => (pure "tinfo")
  | 0x7A5 => (pure "tcontrol")
  | 0x5A8 => (pure "scontext")
  | 0x7A8 => (pure "mcontext")
  | 0x6A8 => (pure "hcontext")
  | 0x30C => (pure "mstateen0")
  | 0x30D => (pure "mstateen1")
  | 0x30E => (pure "mstateen2")
  | 0x30F => (pure "mstateen3")
  | 0x31C => (pure "mstateen0h")
  | 0x31D => (pure "mstateen1h")
  | 0x31E => (pure "mstateen2h")
  | 0x31F => (pure "mstateen3h")
  | 0x60C => (pure "hstateen0")
  | 0x60D => (pure "hstateen1")
  | 0x60E => (pure "hstateen2")
  | 0x60F => (pure "hstateen3")
  | 0x61C => (pure "hstateen0h")
  | 0x61D => (pure "hstateen1h")
  | 0x61E => (pure "hstateen2h")
  | 0x61F => (pure "hstateen3h")
  | 0x10C => (pure "sstateen0")
  | 0x10D => (pure "sstateen1")
  | 0x10E => (pure "sstateen2")
  | 0x10F => (pure "sstateen3")
  | 0x680 => (pure "hgatp")
  | 0x280 => (pure "vsatp")
  | 0x180 => (pure "satp")
  | 0x015 => (pure "seed")
  | 0xC03 => (pure "hpmcounter3")
  | 0xC04 => (pure "hpmcounter4")
  | 0xC05 => (pure "hpmcounter5")
  | 0xC06 => (pure "hpmcounter6")
  | 0xC07 => (pure "hpmcounter7")
  | 0xC08 => (pure "hpmcounter8")
  | 0xC09 => (pure "hpmcounter9")
  | 0xC0A => (pure "hpmcounter10")
  | 0xC0B => (pure "hpmcounter11")
  | 0xC0C => (pure "hpmcounter12")
  | 0xC0D => (pure "hpmcounter13")
  | 0xC0E => (pure "hpmcounter14")
  | 0xC0F => (pure "hpmcounter15")
  | 0xC10 => (pure "hpmcounter16")
  | 0xC11 => (pure "hpmcounter17")
  | 0xC12 => (pure "hpmcounter18")
  | 0xC13 => (pure "hpmcounter19")
  | 0xC14 => (pure "hpmcounter20")
  | 0xC15 => (pure "hpmcounter21")
  | 0xC16 => (pure "hpmcounter22")
  | 0xC17 => (pure "hpmcounter23")
  | 0xC18 => (pure "hpmcounter24")
  | 0xC19 => (pure "hpmcounter25")
  | 0xC1A => (pure "hpmcounter26")
  | 0xC1B => (pure "hpmcounter27")
  | 0xC1C => (pure "hpmcounter28")
  | 0xC1D => (pure "hpmcounter29")
  | 0xC1E => (pure "hpmcounter30")
  | 0xC1F => (pure "hpmcounter31")
  | 0xC83 => (pure "hpmcounter3h")
  | 0xC84 => (pure "hpmcounter4h")
  | 0xC85 => (pure "hpmcounter5h")
  | 0xC86 => (pure "hpmcounter6h")
  | 0xC87 => (pure "hpmcounter7h")
  | 0xC88 => (pure "hpmcounter8h")
  | 0xC89 => (pure "hpmcounter9h")
  | 0xC8A => (pure "hpmcounter10h")
  | 0xC8B => (pure "hpmcounter11h")
  | 0xC8C => (pure "hpmcounter12h")
  | 0xC8D => (pure "hpmcounter13h")
  | 0xC8E => (pure "hpmcounter14h")
  | 0xC8F => (pure "hpmcounter15h")
  | 0xC90 => (pure "hpmcounter16h")
  | 0xC91 => (pure "hpmcounter17h")
  | 0xC92 => (pure "hpmcounter18h")
  | 0xC93 => (pure "hpmcounter19h")
  | 0xC94 => (pure "hpmcounter20h")
  | 0xC95 => (pure "hpmcounter21h")
  | 0xC96 => (pure "hpmcounter22h")
  | 0xC97 => (pure "hpmcounter23h")
  | 0xC98 => (pure "hpmcounter24h")
  | 0xC99 => (pure "hpmcounter25h")
  | 0xC9A => (pure "hpmcounter26h")
  | 0xC9B => (pure "hpmcounter27h")
  | 0xC9C => (pure "hpmcounter28h")
  | 0xC9D => (pure "hpmcounter29h")
  | 0xC9E => (pure "hpmcounter30h")
  | 0xC9F => (pure "hpmcounter31h")
  | 0x723 => (pure "mhpmevent3h")
  | 0x724 => (pure "mhpmevent4h")
  | 0x725 => (pure "mhpmevent5h")
  | 0x726 => (pure "mhpmevent6h")
  | 0x727 => (pure "mhpmevent7h")
  | 0x728 => (pure "mhpmevent8h")
  | 0x729 => (pure "mhpmevent9h")
  | 0x72A => (pure "mhpmevent10h")
  | 0x72B => (pure "mhpmevent11h")
  | 0x72C => (pure "mhpmevent12h")
  | 0x72D => (pure "mhpmevent13h")
  | 0x72E => (pure "mhpmevent14h")
  | 0x72F => (pure "mhpmevent15h")
  | 0x730 => (pure "mhpmevent16h")
  | 0x731 => (pure "mhpmevent17h")
  | 0x732 => (pure "mhpmevent18h")
  | 0x733 => (pure "mhpmevent19h")
  | 0x734 => (pure "mhpmevent20h")
  | 0x735 => (pure "mhpmevent21h")
  | 0x736 => (pure "mhpmevent22h")
  | 0x737 => (pure "mhpmevent23h")
  | 0x738 => (pure "mhpmevent24h")
  | 0x739 => (pure "mhpmevent25h")
  | 0x73A => (pure "mhpmevent26h")
  | 0x73B => (pure "mhpmevent27h")
  | 0x73C => (pure "mhpmevent28h")
  | 0x73D => (pure "mhpmevent29h")
  | 0x73E => (pure "mhpmevent30h")
  | 0x73F => (pure "mhpmevent31h")
  | 0xDA0 => (pure "scountovf")
  | 0x14D => (pure "stimecmp")
  | 0x15D => (pure "stimecmph")
  | 0x24D => (pure "vstimecmp")
  | 0x25D => (pure "vstimecmph")
  | 0x011 => (pure "ssp")
  | 0xC00 => (pure "cycle")
  | 0xC01 => (pure "time")
  | 0xC02 => (pure "instret")
  | 0xC80 => (pure "cycleh")
  | 0xC81 => (pure "timeh")
  | 0xC82 => (pure "instreth")
  | 0x181 => (pure "srmcfg")
  | reg => (hex_bits_12_forwards reg)

def csr_name (csr : (BitVec 12)) : SailM String := do
  (csr_name_map_forwards csr)

def ext_exc_type_to_str (_e : Unit) : String :=
  "extension-exception"

def exceptionType_to_str (e : ExceptionType) : String :=
  match e with
  | .E_Fetch_Addr_Align () => "misaligned-fetch"
  | .E_Fetch_Access_Fault () => "fetch-access-fault"
  | .E_Illegal_Instr () => "illegal-instruction"
  | .E_Load_Addr_Align () => "misaligned-load"
  | .E_Load_Access_Fault () => "load-access-fault"
  | .E_SAMO_Addr_Align () => "misaligned-store/amo"
  | .E_SAMO_Access_Fault () => "store/amo-access-fault"
  | .E_U_EnvCall () => "u-call"
  | .E_S_EnvCall () => "s-call"
  | .E_VS_EnvCall () => "vs-call"
  | .E_M_EnvCall () => "m-call"
  | .E_Fetch_Page_Fault () => "fetch-page-fault"
  | .E_Load_Page_Fault () => "load-page-fault"
  | .E_Reserved_14 () => "reserved-1"
  | .E_SAMO_Page_Fault () => "store/amo-page-fault"
  | .E_Double_Trap () => "double-trap"
  | .E_Reserved_17 () => "reserved-3"
  | .E_Software_Check () => "software-check-exception"
  | .E_Hardware_Error () => "hardware-error-exception"
  | .E_Fetch_GPage_Fault () => "fetch-guest-page-fault"
  | .E_Load_GPage_Fault () => "load-guest-page-fault"
  | .E_Virtual_Instr () => "virtual-instruction"
  | .E_SAMO_GPage_Fault () => "store/amo-guest-page-fault"
  | .E_Breakpoint .Brk_Software => "software-breakpoint"
  | .E_Breakpoint .Brk_Hardware => "hardware-breakpoint"
  | .E_Extension e => (ext_exc_type_to_str e)

def bitype_mnemonic_forwards (arg_ : biop) : String :=
  match arg_ with
  | .BEQI => "beqi"
  | .BNEI => "bnei"

def btype_mnemonic_forwards (arg_ : bop) : String :=
  match arg_ with
  | .BEQ => "beq"
  | .BNE => "bne"
  | .BLT => "blt"
  | .BGE => "bge"
  | .BLTU => "bltu"
  | .BGEU => "bgeu"

def cbop_mnemonic_forwards (arg_ : cbop_zicbom) : String :=
  match arg_ with
  | .CBO_CLEAN => "cbo.clean"
  | .CBO_FLUSH => "cbo.flush"
  | .CBO_INVAL => "cbo.inval"

def freg_abi_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  match arg_ with
  | 0b00000 => "ft0"
  | 0b00001 => "ft1"
  | 0b00010 => "ft2"
  | 0b00011 => "ft3"
  | 0b00100 => "ft4"
  | 0b00101 => "ft5"
  | 0b00110 => "ft6"
  | 0b00111 => "ft7"
  | 0b01000 => "fs0"
  | 0b01001 => "fs1"
  | 0b01010 => "fa0"
  | 0b01011 => "fa1"
  | 0b01100 => "fa2"
  | 0b01101 => "fa3"
  | 0b01110 => "fa4"
  | 0b01111 => "fa5"
  | 0b10000 => "fa6"
  | 0b10001 => "fa7"
  | 0b10010 => "fs2"
  | 0b10011 => "fs3"
  | 0b10100 => "fs4"
  | 0b10101 => "fs5"
  | 0b10110 => "fs6"
  | 0b10111 => "fs7"
  | 0b11000 => "fs8"
  | 0b11001 => "fs9"
  | 0b11010 => "fs10"
  | 0b11011 => "fs11"
  | 0b11100 => "ft8"
  | 0b11101 => "ft9"
  | 0b11110 => "ft10"
  | _ => "ft11"

def freg_arch_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  match arg_ with
  | 0b00000 => "f0"
  | 0b00001 => "f1"
  | 0b00010 => "f2"
  | 0b00011 => "f3"
  | 0b00100 => "f4"
  | 0b00101 => "f5"
  | 0b00110 => "f6"
  | 0b00111 => "f7"
  | 0b01000 => "f8"
  | 0b01001 => "f9"
  | 0b01010 => "f10"
  | 0b01011 => "f11"
  | 0b01100 => "f12"
  | 0b01101 => "f13"
  | 0b01110 => "f14"
  | 0b01111 => "f15"
  | 0b10000 => "f16"
  | 0b10001 => "f17"
  | 0b10010 => "f18"
  | 0b10011 => "f19"
  | 0b10100 => "f20"
  | 0b10101 => "f21"
  | 0b10110 => "f22"
  | 0b10111 => "f23"
  | 0b11000 => "f24"
  | 0b11001 => "f25"
  | 0b11010 => "f26"
  | 0b11011 => "f27"
  | 0b11100 => "f28"
  | 0b11101 => "f29"
  | 0b11110 => "f30"
  | _ => "f31"

def freg_name_forwards (arg_ : fregidx) : SailM String := do
  match arg_ with
  | .Fregidx i =>
    (do
      if ((get_config_use_abi_names ()) : Bool)
      then (pure (freg_abi_name_raw_forwards i))
      else
        (do
          if ((not (get_config_use_abi_names ())) : Bool)
          then (pure (freg_arch_name_raw_forwards i))
          else
            (do
              «assert» false "Pattern match failure at unknown location"
              throw Error.Exit)))

def cfreg_name_forwards (arg_ : cfregidx) : SailM String := do
  match arg_ with
  | .Cfregidx i => (freg_name_forwards (Fregidx (0b01#2 +++ (i : (BitVec 3)))))

def base_E_enabled := false

def regidx_bit_width := 5

def encdec_reg_backwards (arg_ : (BitVec 5)) : SailM regidx := do
  let r := arg_
  if (((not base_E_enabled) || ((BitVec.access r 4) == 0#1)) : Bool)
  then (pure (Regidx (Sail.BitVec.extractLsb r (regidx_bit_width -i 1) 0)))
  else
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_reg_forwards (arg_ : regidx) : (BitVec 5) :=
  match arg_ with
  | .Regidx r => (zero_extend (m := 5) r)

def encdec_reg_forwards_matches (arg_ : regidx) : Bool :=
  match arg_ with
  | .Regidx r => true

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
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))

def creg_name_forwards (arg_ : cregidx) : SailM String := do
  match arg_ with
  | .Cregidx i => (reg_name_forwards (← (encdec_reg_backwards (0b01#2 +++ (i : (BitVec 3))))))

def csr_mnemonic_forwards (arg_ : csrop) : String :=
  match arg_ with
  | .CSRRW => "csrrw"
  | .CSRRS => "csrrs"
  | .CSRRC => "csrrc"

def f_bin_f_type_mnemonic_D_forwards (arg_ : f_bin_f_op_D) : String :=
  match arg_ with
  | .FSGNJ_D => "fsgnj.d"
  | .FSGNJN_D => "fsgnjn.d"
  | .FSGNJX_D => "fsgnjx.d"
  | .FMIN_D => "fmin.d"
  | .FMAX_D => "fmax.d"

def f_bin_f_type_mnemonic_H_forwards (arg_ : f_bin_f_op_H) : String :=
  match arg_ with
  | .FSGNJ_H => "fsgnj.h"
  | .FSGNJN_H => "fsgnjn.h"
  | .FSGNJX_H => "fsgnjx.h"
  | .FMIN_H => "fmin.h"
  | .FMAX_H => "fmax.h"

def f_bin_rm_type_mnemonic_D_forwards (arg_ : f_bin_rm_op_D) : String :=
  match arg_ with
  | .FADD_D => "fadd.d"
  | .FSUB_D => "fsub.d"
  | .FMUL_D => "fmul.d"
  | .FDIV_D => "fdiv.d"

def f_bin_rm_type_mnemonic_H_forwards (arg_ : f_bin_rm_op_H) : String :=
  match arg_ with
  | .FADD_H => "fadd.h"
  | .FSUB_H => "fsub.h"
  | .FMUL_H => "fmul.h"
  | .FDIV_H => "fdiv.h"

def f_bin_rm_type_mnemonic_S_forwards (arg_ : f_bin_rm_op_S) : String :=
  match arg_ with
  | .FADD_S => "fadd.s"
  | .FSUB_S => "fsub.s"
  | .FMUL_S => "fmul.s"
  | .FDIV_S => "fdiv.s"

def f_bin_type_mnemonic_f_S_forwards (arg_ : f_bin_op_f_S) : String :=
  match arg_ with
  | .FSGNJ_S => "fsgnj.s"
  | .FSGNJN_S => "fsgnjn.s"
  | .FSGNJX_S => "fsgnjx.s"
  | .FMIN_S => "fmin.s"
  | .FMAX_S => "fmax.s"

def f_bin_type_mnemonic_x_S_forwards (arg_ : f_bin_op_x_S) : String :=
  match arg_ with
  | .FEQ_S => "feq.s"
  | .FLT_S => "flt.s"
  | .FLE_S => "fle.s"

def f_bin_x_type_mnemonic_D_forwards (arg_ : f_bin_x_op_D) : String :=
  match arg_ with
  | .FEQ_D => "feq.d"
  | .FLT_D => "flt.d"
  | .FLE_D => "fle.d"

def f_bin_x_type_mnemonic_H_forwards (arg_ : f_bin_x_op_H) : String :=
  match arg_ with
  | .FEQ_H => "feq.h"
  | .FLT_H => "flt.h"
  | .FLE_H => "fle.h"

def f_madd_type_mnemonic_D_forwards (arg_ : f_madd_op_D) : String :=
  match arg_ with
  | .FMADD_D => "fmadd.d"
  | .FMSUB_D => "fmsub.d"
  | .FNMSUB_D => "fnmsub.d"
  | .FNMADD_D => "fnmadd.d"

def f_madd_type_mnemonic_H_forwards (arg_ : f_madd_op_H) : String :=
  match arg_ with
  | .FMADD_H => "fmadd.h"
  | .FMSUB_H => "fmsub.h"
  | .FNMSUB_H => "fnmsub.h"
  | .FNMADD_H => "fnmadd.h"

def f_madd_type_mnemonic_S_forwards (arg_ : f_madd_op_S) : String :=
  match arg_ with
  | .FMADD_S => "fmadd.s"
  | .FMSUB_S => "fmsub.s"
  | .FNMSUB_S => "fnmsub.s"
  | .FNMADD_S => "fnmadd.s"

def f_un_f_type_mnemonic_D_forwards (arg_ : f_un_f_op_D) : String :=
  match arg_ with
  | .FMV_D_X => "fmv.d.x"

def f_un_f_type_mnemonic_H_forwards (arg_ : f_un_f_op_H) : String :=
  match arg_ with
  | .FMV_H_X => "fmv.h.x"

def f_un_rm_ff_type_mnemonic_D_forwards (arg_ : f_un_rm_ff_op_D) : String :=
  match arg_ with
  | .FSQRT_D => "fsqrt.d"
  | .FCVT_S_D => "fcvt.s.d"
  | .FCVT_D_S => "fcvt.d.s"

def f_un_rm_ff_type_mnemonic_H_forwards (arg_ : f_un_rm_ff_op_H) : String :=
  match arg_ with
  | .FSQRT_H => "fsqrt.h"
  | .FCVT_H_S => "fcvt.h.s"
  | .FCVT_H_D => "fcvt.h.d"
  | .FCVT_S_H => "fcvt.s.h"
  | .FCVT_D_H => "fcvt.d.h"

def f_un_rm_fx_type_mnemonic_D_forwards (arg_ : f_un_rm_fx_op_D) : String :=
  match arg_ with
  | .FCVT_W_D => "fcvt.w.d"
  | .FCVT_WU_D => "fcvt.wu.d"
  | .FCVT_L_D => "fcvt.l.d"
  | .FCVT_LU_D => "fcvt.lu.d"

def f_un_rm_fx_type_mnemonic_H_forwards (arg_ : f_un_rm_fx_op_H) : String :=
  match arg_ with
  | .FCVT_W_H => "fcvt.w.h"
  | .FCVT_WU_H => "fcvt.wu.h"
  | .FCVT_L_H => "fcvt.l.h"
  | .FCVT_LU_H => "fcvt.lu.h"

def f_un_rm_fx_type_mnemonic_S_forwards (arg_ : f_un_rm_fx_op_S) : String :=
  match arg_ with
  | .FCVT_W_S => "fcvt.w.s"
  | .FCVT_WU_S => "fcvt.wu.s"
  | .FCVT_L_S => "fcvt.l.s"
  | .FCVT_LU_S => "fcvt.lu.s"

def f_un_rm_xf_type_mnemonic_D_forwards (arg_ : f_un_rm_xf_op_D) : String :=
  match arg_ with
  | .FCVT_D_W => "fcvt.d.w"
  | .FCVT_D_WU => "fcvt.d.wu"
  | .FCVT_D_L => "fcvt.d.l"
  | .FCVT_D_LU => "fcvt.d.lu"

def f_un_rm_xf_type_mnemonic_H_forwards (arg_ : f_un_rm_xf_op_H) : String :=
  match arg_ with
  | .FCVT_H_W => "fcvt.h.w"
  | .FCVT_H_WU => "fcvt.h.wu"
  | .FCVT_H_L => "fcvt.h.l"
  | .FCVT_H_LU => "fcvt.h.lu"

def f_un_rm_xf_type_mnemonic_S_forwards (arg_ : f_un_rm_xf_op_S) : String :=
  match arg_ with
  | .FCVT_S_W => "fcvt.s.w"
  | .FCVT_S_WU => "fcvt.s.wu"
  | .FCVT_S_L => "fcvt.s.l"
  | .FCVT_S_LU => "fcvt.s.lu"

def f_un_type_mnemonic_f_S_forwards (arg_ : f_un_op_f_S) : String :=
  match arg_ with
  | .FMV_W_X => "fmv.w.x"

def f_un_type_mnemonic_x_S_forwards (arg_ : f_un_op_x_S) : String :=
  match arg_ with
  | .FCLASS_S => "fclass.s"
  | .FMV_X_W => "fmv.x.w"

def f_un_x_type_mnemonic_D_forwards (arg_ : f_un_x_op_D) : String :=
  match arg_ with
  | .FMV_X_D => "fmv.x.d"
  | .FCLASS_D => "fclass.d"

def f_un_x_type_mnemonic_H_forwards (arg_ : f_un_x_op_H) : String :=
  match arg_ with
  | .FMV_X_H => "fmv.x.h"
  | .FCLASS_H => "fclass.h"

def bit_maybe_i_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "i"
  | _ => ""

def bit_maybe_o_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "o"
  | _ => ""

def bit_maybe_r_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "r"
  | _ => ""

def bit_maybe_w_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "w"
  | _ => ""

def fence_bits_forwards (arg_ : (BitVec 4)) : String :=
  let b__0 := arg_
  if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
  then "0"
  else
    (let i : (BitVec 1) := (Sail.BitVec.extractLsb b__0 3 3)
    let w : (BitVec 1) := (Sail.BitVec.extractLsb b__0 0 0)
    let r : (BitVec 1) := (Sail.BitVec.extractLsb b__0 1 1)
    let o : (BitVec 1) := (Sail.BitVec.extractLsb b__0 2 2)
    let i : (BitVec 1) := (Sail.BitVec.extractLsb b__0 3 3)
    (String.append (bit_maybe_i_forwards i)
      (String.append (bit_maybe_o_forwards o)
        (String.append (bit_maybe_r_forwards r) (String.append (bit_maybe_w_forwards w) "")))))

def fregidx_to_regidx (app_0 : fregidx) : regidx :=
  let .Fregidx b := app_0
  (Regidx (trunc (m := 5) b))

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
  | .Ext_Zicbop => false
  | .Ext_Zicboz => true
  | .Ext_Zicfilp => false
  | .Ext_Zicfiss => false
  | .Ext_Zicntr => false
  | .Ext_Zicond => true
  | .Ext_Zicsr => true
  | .Ext_Zifencei => true
  | .Ext_Zihintntl => false
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
  | .Ext_Zca => false
  | .Ext_Zcb => false
  | .Ext_Zcd => false
  | .Ext_Zcf => ((false : Bool) && (xlen == 32))
  | .Ext_Zcmop => false
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
  | .Ext_Sdtrig => true
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

def freg_or_reg_name_forwards (arg_ : fregidx) : SailM String := do
  let f := arg_
  if ((hartSupports Ext_Zfinx) : Bool)
  then (reg_name_forwards (fregidx_to_regidx f))
  else (freg_name_forwards f)

def frm_mnemonic_forwards (arg_ : rounding_mode) : String :=
  match arg_ with
  | .RM_RNE => "rne"
  | .RM_RTZ => "rtz"
  | .RM_RDN => "rdn"
  | .RM_RUP => "rup"
  | .RM_RMM => "rmm"
  | .RM_DYN => "dyn"

def fvfmatype_mnemonic_forwards (arg_ : fvfmafunct6) : String :=
  match arg_ with
  | .VF_VMADD => "vfmadd.vf"
  | .VF_VNMADD => "vfnmadd.vf"
  | .VF_VMSUB => "vfmsub.vf"
  | .VF_VNMSUB => "vfnmsub.vf"
  | .VF_VMACC => "vfmacc.vf"
  | .VF_VNMACC => "vfnmacc.vf"
  | .VF_VMSAC => "vfmsac.vf"
  | .VF_VNMSAC => "vfnmsac.vf"

def fvfmtype_mnemonic_forwards (arg_ : fvfmfunct6) : String :=
  match arg_ with
  | .VFM_VMFEQ => "vmfeq.vf"
  | .VFM_VMFLE => "vmfle.vf"
  | .VFM_VMFLT => "vmflt.vf"
  | .VFM_VMFNE => "vmfne.vf"
  | .VFM_VMFGT => "vmfgt.vf"
  | .VFM_VMFGE => "vmfge.vf"

def fvftype_mnemonic_forwards (arg_ : fvffunct6) : String :=
  match arg_ with
  | .VF_VADD => "vfadd.vf"
  | .VF_VSUB => "vfsub.vf"
  | .VF_VMIN => "vfmin.vf"
  | .VF_VMAX => "vfmax.vf"
  | .VF_VSGNJ => "vfsgnj.vf"
  | .VF_VSGNJN => "vfsgnjn.vf"
  | .VF_VSGNJX => "vfsgnjx.vf"
  | .VF_VSLIDE1UP => "vfslide1up.vf"
  | .VF_VSLIDE1DOWN => "vfslide1down.vf"
  | .VF_VDIV => "vfdiv.vf"
  | .VF_VRDIV => "vfrdiv.vf"
  | .VF_VMUL => "vfmul.vf"
  | .VF_VRSUB => "vfrsub.vf"

def fvvmatype_mnemonic_forwards (arg_ : fvvmafunct6) : String :=
  match arg_ with
  | .FVV_VMADD => "vfmadd.vv"
  | .FVV_VNMADD => "vfnmadd.vv"
  | .FVV_VMSUB => "vfmsub.vv"
  | .FVV_VNMSUB => "vfnmsub.vv"
  | .FVV_VMACC => "vfmacc.vv"
  | .FVV_VNMACC => "vfnmacc.vv"
  | .FVV_VMSAC => "vfmsac.vv"
  | .FVV_VNMSAC => "vfnmsac.vv"

def fvvmtype_mnemonic_forwards (arg_ : fvvmfunct6) : String :=
  match arg_ with
  | .FVVM_VMFEQ => "vmfeq.vv"
  | .FVVM_VMFLE => "vmfle.vv"
  | .FVVM_VMFLT => "vmflt.vv"
  | .FVVM_VMFNE => "vmfne.vv"

def fvvtype_mnemonic_forwards (arg_ : fvvfunct6) : String :=
  match arg_ with
  | .FVV_VADD => "vfadd.vv"
  | .FVV_VSUB => "vfsub.vv"
  | .FVV_VMIN => "vfmin.vv"
  | .FVV_VMAX => "vfmax.vv"
  | .FVV_VSGNJ => "vfsgnj.vv"
  | .FVV_VSGNJN => "vfsgnjn.vv"
  | .FVV_VSGNJX => "vfsgnjx.vv"
  | .FVV_VDIV => "vfdiv.vv"
  | .FVV_VMUL => "vfmul.vv"

def fwftype_mnemonic_forwards (arg_ : fwffunct6) : String :=
  match arg_ with
  | .FWF_VADD => "vfwadd.wf"
  | .FWF_VSUB => "vfwsub.wf"

def fwvfmatype_mnemonic_forwards (arg_ : fwvfmafunct6) : String :=
  match arg_ with
  | .FWVF_VMACC => "vfwmacc.vf"
  | .FWVF_VNMACC => "vfwnmacc.vf"
  | .FWVF_VMSAC => "vfwmsac.vf"
  | .FWVF_VNMSAC => "vfwnmsac.vf"

def fwvftype_mnemonic_forwards (arg_ : fwvffunct6) : String :=
  match arg_ with
  | .FWVF_VADD => "vfwadd.vf"
  | .FWVF_VSUB => "vfwsub.vf"
  | .FWVF_VMUL => "vfwmul.vf"

def fwvtype_mnemonic_forwards (arg_ : fwvfunct6) : String :=
  match arg_ with
  | .FWV_VADD => "vfwadd.wv"
  | .FWV_VSUB => "vfwsub.wv"

def fwvvmatype_mnemonic_forwards (arg_ : fwvvmafunct6) : String :=
  match arg_ with
  | .FWVV_VMACC => "vfwmacc.vv"
  | .FWVV_VNMACC => "vfwnmacc.vv"
  | .FWVV_VMSAC => "vfwmsac.vv"
  | .FWVV_VNMSAC => "vfwnmsac.vv"

def fwvvtype_mnemonic_forwards (arg_ : fwvvfunct6) : String :=
  match arg_ with
  | .FWVV_VADD => "vfwadd.vv"
  | .FWVV_VSUB => "vfwsub.vv"
  | .FWVV_VMUL => "vfwmul.vv"

def indexed_mop_mnemonic_forwards (arg_ : indexed_mop) : String :=
  match arg_ with
  | .INDEXED_UNORDERED => "u"
  | .INDEXED_ORDERED => "o"

def itype_mnemonic_forwards (arg_ : iop) : String :=
  match arg_ with
  | .ADDI => "addi"
  | .SLTI => "slti"
  | .SLTIU => "sltiu"
  | .XORI => "xori"
  | .ORI => "ori"
  | .ANDI => "andi"

def maybe_hlvx_forwards (arg_ : hlvop) : String :=
  match arg_ with
  | .HLV => ""
  | .HLVX => "x"

/-- Type quantifiers: k_ex1818816_ : Bool -/
def maybe_u_forwards (arg_ : Bool) : String :=
  match arg_ with
  | true => "u"
  | false => ""

def maybe_vmask_backwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => ""
  | _ => (String.append (sep_forwards ()) (String.append "v0.t" ""))

def mmtype_mnemonic_forwards (arg_ : mmfunct6) : String :=
  match arg_ with
  | .MM_VMAND => "vmand.mm"
  | .MM_VMNAND => "vmnand.mm"
  | .MM_VMANDN => "vmandn.mm"
  | .MM_VMXOR => "vmxor.mm"
  | .MM_VMOR => "vmor.mm"
  | .MM_VMNOR => "vmnor.mm"
  | .MM_VMORN => "vmorn.mm"
  | .MM_VMXNOR => "vmxnor.mm"

def mul_mnemonic_forwards (arg_ : mul_op) : SailM String := do
  match arg_ with
  | { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed } => (pure "mul")
  | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed } => (pure "mulh")
  | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned } => (pure "mulhsu")
  | { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned } => (pure "mulhu")
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def mvvmatype_mnemonic_forwards (arg_ : mvvmafunct6) : String :=
  match arg_ with
  | .MVV_VMACC => "vmacc.vv"
  | .MVV_VNMSAC => "vnmsac.vv"
  | .MVV_VMADD => "vmadd.vv"
  | .MVV_VNMSUB => "vnmsub.vv"

def mvvtype_mnemonic_forwards (arg_ : mvvfunct6) : String :=
  match arg_ with
  | .MVV_VAADDU => "vaaddu.vv"
  | .MVV_VAADD => "vaadd.vv"
  | .MVV_VASUBU => "vasubu.vv"
  | .MVV_VASUB => "vasub.vv"
  | .MVV_VMUL => "vmul.vv"
  | .MVV_VMULH => "vmulh.vv"
  | .MVV_VMULHU => "vmulhu.vv"
  | .MVV_VMULHSU => "vmulhsu.vv"
  | .MVV_VDIVU => "vdivu.vv"
  | .MVV_VDIV => "vdiv.vv"
  | .MVV_VREMU => "vremu.vv"
  | .MVV_VREM => "vrem.vv"

def mvxmatype_mnemonic_forwards (arg_ : mvxmafunct6) : String :=
  match arg_ with
  | .MVX_VMACC => "vmacc.vx"
  | .MVX_VNMSAC => "vnmsac.vx"
  | .MVX_VMADD => "vmadd.vx"
  | .MVX_VNMSUB => "vnmsub.vx"

def mvxtype_mnemonic_forwards (arg_ : mvxfunct6) : String :=
  match arg_ with
  | .MVX_VAADDU => "vaaddu.vx"
  | .MVX_VAADD => "vaadd.vx"
  | .MVX_VASUBU => "vasubu.vx"
  | .MVX_VASUB => "vasub.vx"
  | .MVX_VSLIDE1UP => "vslide1up.vx"
  | .MVX_VSLIDE1DOWN => "vslide1down.vx"
  | .MVX_VMUL => "vmul.vx"
  | .MVX_VMULH => "vmulh.vx"
  | .MVX_VMULHU => "vmulhu.vx"
  | .MVX_VMULHSU => "vmulhsu.vx"
  | .MVX_VDIVU => "vdivu.vx"
  | .MVX_VDIV => "vdiv.vx"
  | .MVX_VREMU => "vremu.vx"
  | .MVX_VREM => "vrem.vx"

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8] -/
def nfields_pow2_string_forwards (arg_ : Nat) : String :=
  match arg_ with
  | 1 => "1"
  | 2 => "2"
  | 4 => "4"
  | _ => "8"

/-- Type quantifiers: arg_ : Nat, arg_ > 0 ∧ arg_ ≤ 8 -/
def nfields_string_forwards (arg_ : Nat) : String :=
  match arg_ with
  | 1 => ""
  | 2 => "seg2"
  | 3 => "seg3"
  | 4 => "seg4"
  | 5 => "seg5"
  | 6 => "seg6"
  | 7 => "seg7"
  | _ => "seg8"

def nistype_mnemonic_forwards (arg_ : nisfunct6) : String :=
  match arg_ with
  | .NIS_VNSRL => "vnsrl.wi"
  | .NIS_VNSRA => "vnsra.wi"

def nitype_mnemonic_forwards (arg_ : nifunct6) : String :=
  match arg_ with
  | .NI_VNCLIPU => "vnclipu.wi"
  | .NI_VNCLIP => "vnclip.wi"

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8] -/
def nreg_string_forwards (arg_ : Nat) : String :=
  match arg_ with
  | 1 => "1"
  | 2 => "2"
  | 4 => "4"
  | _ => "8"

def ntl_name_forwards (arg_ : ntl_type) : String :=
  match arg_ with
  | .NTL_P1 => "p1"
  | .NTL_PALL => "pall"
  | .NTL_S1 => "s1"
  | .NTL_ALL => "all"

def nvstype_mnemonic_forwards (arg_ : nvsfunct6) : String :=
  match arg_ with
  | .NVS_VNSRL => "vnsrl.wv"
  | .NVS_VNSRA => "vnsra.wv"

def nvtype_mnemonic_forwards (arg_ : nvfunct6) : String :=
  match arg_ with
  | .NV_VNCLIPU => "vnclipu.wv"
  | .NV_VNCLIP => "vnclip.wv"

def nxstype_mnemonic_forwards (arg_ : nxsfunct6) : String :=
  match arg_ with
  | .NXS_VNSRL => "vnsrl.wx"
  | .NXS_VNSRA => "vnsra.wx"

def nxtype_mnemonic_forwards (arg_ : nxfunct6) : String :=
  match arg_ with
  | .NX_VNCLIPU => "vnclipu.wx"
  | .NX_VNCLIP => "vnclip.wx"

def prefetch_mnemonic_forwards (arg_ : cbop_zicbop) : String :=
  match arg_ with
  | .PREFETCH_I => "prefetch.i"
  | .PREFETCH_R => "prefetch.r"
  | .PREFETCH_W => "prefetch.w"

def rfvvtype_mnemonic_forwards (arg_ : rfvvfunct6) : String :=
  match arg_ with
  | .FVV_VFREDOSUM => "vfredosum.vs"
  | .FVV_VFREDUSUM => "vfredusum.vs"
  | .FVV_VFREDMAX => "vfredmax.vs"
  | .FVV_VFREDMIN => "vfredmin.vs"

def rfwvvtype_mnemonic_forwards (arg_ : rfwvvfunct6) : String :=
  match arg_ with
  | .FVV_VFWREDOSUM => "vfwredosum.vs"
  | .FVV_VFWREDUSUM => "vfwredusum.vs"

def rivvtype_mnemonic_forwards (arg_ : rivvfunct6) : String :=
  match arg_ with
  | .IVV_VWREDSUMU => "vwredsumu.vs"
  | .IVV_VWREDSUM => "vwredsum.vs"

def rmvvtype_mnemonic_forwards (arg_ : rmvvfunct6) : String :=
  match arg_ with
  | .MVV_VREDSUM => "vredsum.vs"
  | .MVV_VREDAND => "vredand.vs"
  | .MVV_VREDOR => "vredor.vs"
  | .MVV_VREDXOR => "vredxor.vs"
  | .MVV_VREDMINU => "vredminu.vs"
  | .MVV_VREDMIN => "vredmin.vs"
  | .MVV_VREDMAXU => "vredmaxu.vs"
  | .MVV_VREDMAX => "vredmax.vs"

def rtype_mnemonic_forwards (arg_ : rop) : String :=
  match arg_ with
  | .ADD => "add"
  | .SLT => "slt"
  | .SLTU => "sltu"
  | .AND => "and"
  | .OR => "or"
  | .XOR => "xor"
  | .SLL => "sll"
  | .SRL => "srl"
  | .SUB => "sub"
  | .SRA => "sra"

def rtypew_mnemonic_forwards (arg_ : ropw) : String :=
  match arg_ with
  | .ADDW => "addw"
  | .SUBW => "subw"
  | .SLLW => "sllw"
  | .SRLW => "srlw"
  | .SRAW => "sraw"

def shiftiop_mnemonic_forwards (arg_ : sop) : String :=
  match arg_ with
  | .SLLI => "slli"
  | .SRLI => "srli"
  | .SRAI => "srai"

def shiftiwop_mnemonic_forwards (arg_ : sopw) : String :=
  match arg_ with
  | .SLLIW => "slliw"
  | .SRLIW => "srliw"
  | .SRAIW => "sraiw"

def sp_reg_name_forwards (arg_ : Unit) : SailM String := do
  match arg_ with
  | () =>
    (do
      if ((get_config_use_abi_names ()) : Bool)
      then (pure "sp")
      else
        (do
          if ((not (get_config_use_abi_names ())) : Bool)
          then (pure "x2")
          else
            (do
              «assert» false "Pattern match failure at unknown location"
              throw Error.Exit)))

def utype_mnemonic_forwards (arg_ : uop) : String :=
  match arg_ with
  | .LUI => "lui"
  | .AUIPC => "auipc"

def vabd_vv_mnemonic_forwards (arg_ : zvabd_vabd_func6) : String :=
  match arg_ with
  | .VABD => "vabd.vv"
  | .VABDU => "vabdu.vv"

def vabd_vx_mnemonic_forwards (arg_ : zvabd_vabd_func6) : String :=
  match arg_ with
  | .VABD => "vabd.vx"
  | .VABDU => "vabdu.vx"

def vaesdf_mnemonic_forwards (arg_ : zvk_vaesdf_funct6) : String :=
  match arg_ with
  | .ZVK_VAESDF_VV => "vaesdf.vv"
  | .ZVK_VAESDF_VS => "vaesdf.vs"

def vaesdm_mnemonic_forwards (arg_ : zvk_vaesdm_funct6) : String :=
  match arg_ with
  | .ZVK_VAESDM_VV => "vaesdm.vv"
  | .ZVK_VAESDM_VS => "vaesdm.vs"

def vaesef_mnemonic_forwards (arg_ : zvk_vaesef_funct6) : String :=
  match arg_ with
  | .ZVK_VAESEF_VV => "vaesef.vv"
  | .ZVK_VAESEF_VS => "vaesef.vs"

def vaesem_mnemonic_forwards (arg_ : zvk_vaesem_funct6) : String :=
  match arg_ with
  | .ZVK_VAESEM_VV => "vaesem.vv"
  | .ZVK_VAESEM_VS => "vaesem.vs"

def vexttype_mnemonic_forwards (arg_ : vextfunct6) : String :=
  match arg_ with
  | .VEXT2_ZVF2 => "vzext.vf2"
  | .VEXT2_SVF2 => "vsext.vf2"
  | .VEXT4_ZVF4 => "vzext.vf4"
  | .VEXT4_SVF4 => "vsext.vf4"
  | .VEXT8_ZVF8 => "vzext.vf8"
  | .VEXT8_SVF8 => "vsext.vf8"

def vfnunary0_mnemonic_forwards (arg_ : vfnunary0) : String :=
  match arg_ with
  | .FNV_CVT_XU_F => "vfncvt.xu.f.w"
  | .FNV_CVT_X_F => "vfncvt.x.f.w"
  | .FNV_CVT_F_XU => "vfncvt.f.xu.w"
  | .FNV_CVT_F_X => "vfncvt.f.x.w"
  | .FNV_CVT_F_F => "vfncvt.f.f.w"
  | .FNV_CVT_ROD_F_F => "vfncvt.rod.f.f.w"
  | .FNV_CVT_RTZ_XU_F => "vfncvt.rtz.xu.f.w"
  | .FNV_CVT_RTZ_X_F => "vfncvt.rtz.x.f.w"

def vfunary0_mnemonic_forwards (arg_ : vfunary0) : String :=
  match arg_ with
  | .FV_CVT_XU_F => "vfcvt.xu.f.v"
  | .FV_CVT_X_F => "vfcvt.x.f.v"
  | .FV_CVT_F_XU => "vfcvt.f.xu.v"
  | .FV_CVT_F_X => "vfcvt.f.x.v"
  | .FV_CVT_RTZ_XU_F => "vfcvt.rtz.xu.f.v"
  | .FV_CVT_RTZ_X_F => "vfcvt.rtz.x.f.v"

def vfunary1_mnemonic_forwards (arg_ : vfunary1) : String :=
  match arg_ with
  | .FVV_VSQRT => "vfsqrt.v"
  | .FVV_VRSQRT7 => "vfrsqrt7.v"
  | .FVV_VREC7 => "vfrec7.v"
  | .FVV_VCLASS => "vfclass.v"

def vfwunary0_mnemonic_forwards (arg_ : vfwunary0) : String :=
  match arg_ with
  | .FWV_CVT_XU_F => "vfwcvt.xu.f.v"
  | .FWV_CVT_X_F => "vfwcvt.x.f.v"
  | .FWV_CVT_F_XU => "vfwcvt.f.xu.v"
  | .FWV_CVT_F_X => "vfwcvt.f.x.v"
  | .FWV_CVT_F_F => "vfwcvt.f.f.v"
  | .FWV_CVT_RTZ_XU_F => "vfwcvt.rtz.xu.f.v"
  | .FWV_CVT_RTZ_X_F => "vfwcvt.rtz.x.f.v"

def vicmptype_mnemonic_forwards (arg_ : vicmpfunct6) : String :=
  match arg_ with
  | .VICMP_VMSEQ => "vmseq.vi"
  | .VICMP_VMSNE => "vmsne.vi"
  | .VICMP_VMSLEU => "vmsleu.vi"
  | .VICMP_VMSLE => "vmsle.vi"
  | .VICMP_VMSGTU => "vmsgtu.vi"
  | .VICMP_VMSGT => "vmsgt.vi"

def vimctype_mnemonic_forwards (arg_ : vimcfunct6) : String :=
  match arg_ with
  | .VIMC_VMADC => "vmadc.vi"

def vimstype_mnemonic_forwards (arg_ : vimsfunct6) : String :=
  match arg_ with
  | .VIMS_VADC => "vadc.vim"

def vimtype_mnemonic_forwards (arg_ : vimfunct6) : String :=
  match arg_ with
  | .VIM_VMADC => "vmadc.vim"

def visg_mnemonic_forwards (arg_ : visgfunct6) : String :=
  match arg_ with
  | .VI_VSLIDEUP => "vslideup.vi"
  | .VI_VSLIDEDOWN => "vslidedown.vi"
  | .VI_VRGATHER => "vrgather.vi"

def vitype_mnemonic_forwards (arg_ : vifunct6) : String :=
  match arg_ with
  | .VI_VADD => "vadd.vi"
  | .VI_VRSUB => "vrsub.vi"
  | .VI_VAND => "vand.vi"
  | .VI_VOR => "vor.vi"
  | .VI_VXOR => "vxor.vi"
  | .VI_VSADDU => "vsaddu.vi"
  | .VI_VSADD => "vsadd.vi"
  | .VI_VSLL => "vsll.vi"
  | .VI_VSRL => "vsrl.vi"
  | .VI_VSRA => "vsra.vi"
  | .VI_VSSRL => "vssrl.vi"
  | .VI_VSSRA => "vssra.vi"

def vlewidth_bitsnumberstr_forwards (arg_ : vlewidth) : String :=
  match arg_ with
  | .VLE8 => "8"
  | .VLE16 => "16"
  | .VLE32 => "32"
  | .VLE64 => "64"

def vmtype_mnemonic_forwards (arg_ : vmlsop) : String :=
  match arg_ with
  | .VLM => "vlm.v"
  | .VSM => "vsm.v"

def vreg_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  match arg_ with
  | 0b00000 => "v0"
  | 0b00001 => "v1"
  | 0b00010 => "v2"
  | 0b00011 => "v3"
  | 0b00100 => "v4"
  | 0b00101 => "v5"
  | 0b00110 => "v6"
  | 0b00111 => "v7"
  | 0b01000 => "v8"
  | 0b01001 => "v9"
  | 0b01010 => "v10"
  | 0b01011 => "v11"
  | 0b01100 => "v12"
  | 0b01101 => "v13"
  | 0b01110 => "v14"
  | 0b01111 => "v15"
  | 0b10000 => "v16"
  | 0b10001 => "v17"
  | 0b10010 => "v18"
  | 0b10011 => "v19"
  | 0b10100 => "v20"
  | 0b10101 => "v21"
  | 0b10110 => "v22"
  | 0b10111 => "v23"
  | 0b11000 => "v24"
  | 0b11001 => "v25"
  | 0b11010 => "v26"
  | 0b11011 => "v27"
  | 0b11100 => "v28"
  | 0b11101 => "v29"
  | 0b11110 => "v30"
  | _ => "v31"

def vreg_name_forwards (arg_ : vregidx) : String :=
  match arg_ with
  | .Vregidx i => (vreg_name_raw_forwards i)

def vsha2_mnemonic_forwards (arg_ : zvk_vsha2_funct6) : String :=
  match arg_ with
  | .ZVK_VSHA2CH_VV => "vsha2ch.vv"
  | .ZVK_VSHA2CL_VV => "vsha2cl.vv"

def vsm4r_mnemonic_forwards (arg_ : zvk_vsm4r_funct6) : String :=
  match arg_ with
  | .ZVK_VSM4R_VV => "vsm4r.vv"
  | .ZVK_VSM4R_VS => "vsm4r.vs"

def ma_flag_backwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => (String.append (sep_forwards ()) (String.append "ma" ""))
  | _ => (String.append (sep_forwards ()) (String.append "mu" ""))

def maybe_lmul_flag_backwards (arg_ : (BitVec 3)) : SailM String := do
  match arg_ with
  | 0b101 => (pure (String.append (sep_forwards ()) (String.append "mf8" "")))
  | 0b110 => (pure (String.append (sep_forwards ()) (String.append "mf4" "")))
  | 0b111 => (pure (String.append (sep_forwards ()) (String.append "mf2" "")))
  | 0b000 => (pure (String.append (sep_forwards ()) (String.append "m1" "")))
  | 0b001 => (pure (String.append (sep_forwards ()) (String.append "m2" "")))
  | 0b010 => (pure (String.append (sep_forwards ()) (String.append "m4" "")))
  | 0b011 => (pure (String.append (sep_forwards ()) (String.append "m8" "")))
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def sew_flag_backwards (arg_ : (BitVec 3)) : SailM String := do
  match arg_ with
  | 0b000 => (pure "e8")
  | 0b001 => (pure "e16")
  | 0b010 => (pure "e32")
  | 0b011 => (pure "e64")
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def ta_flag_backwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => (String.append (sep_forwards ()) (String.append "ta" ""))
  | _ => (String.append (sep_forwards ()) (String.append "tu" ""))

def vtr_mnemonic_forwards (_vtr : (BitVec 3)) : String :=
  ""

def vtype_assembly_forwards (arg_ : ((BitVec 3) × (BitVec 1) × (BitVec 1) × (BitVec 3) × (BitVec 3))) : SailM String := do
  match arg_ with
  | (vtr, ma, ta, sew, lmul) =>
    (do
      if ((((BitVec.access sew 2) != 1#1) && ((lmul != 0b100#3) && (vtr == 0b000#3))) : Bool)
      then
        (pure (String.append (← (sew_flag_backwards sew))
            (String.append (← (maybe_lmul_flag_backwards lmul))
              (String.append (ta_flag_backwards ta)
                (String.append (ma_flag_backwards ma) (String.append (vtr_mnemonic_forwards vtr) ""))))))
      else
        (hex_bits_11_forwards
          ((vtr : (BitVec 3)) +++ ((ma : (BitVec 1)) +++ ((ta : (BitVec 1)) +++ ((sew : (BitVec 3)) +++ (lmul : (BitVec 3))))))))

def vvcmptype_mnemonic_forwards (arg_ : vvcmpfunct6) : String :=
  match arg_ with
  | .VVCMP_VMSEQ => "vmseq.vv"
  | .VVCMP_VMSNE => "vmsne.vv"
  | .VVCMP_VMSLTU => "vmsltu.vv"
  | .VVCMP_VMSLT => "vmslt.vv"
  | .VVCMP_VMSLEU => "vmsleu.vv"
  | .VVCMP_VMSLE => "vmsle.vv"

def vvmctype_mnemonic_forwards (arg_ : vvmcfunct6) : String :=
  match arg_ with
  | .VVMC_VMADC => "vmadc.vv"
  | .VVMC_VMSBC => "vmsbc.vv"

def vvmstype_mnemonic_forwards (arg_ : vvmsfunct6) : String :=
  match arg_ with
  | .VVMS_VADC => "vadc.vvm"
  | .VVMS_VSBC => "vsbc.vvm"

def vvmtype_mnemonic_forwards (arg_ : vvmfunct6) : String :=
  match arg_ with
  | .VVM_VMADC => "vmadc.vvm"
  | .VVM_VMSBC => "vmsbc.vvm"

def vvtype_mnemonic_forwards (arg_ : vvfunct6) : String :=
  match arg_ with
  | .VV_VADD => "vadd.vv"
  | .VV_VSUB => "vsub.vv"
  | .VV_VAND => "vand.vv"
  | .VV_VOR => "vor.vv"
  | .VV_VXOR => "vxor.vv"
  | .VV_VRGATHER => "vrgather.vv"
  | .VV_VRGATHEREI16 => "vrgatherei16.vv"
  | .VV_VSADDU => "vsaddu.vv"
  | .VV_VSADD => "vsadd.vv"
  | .VV_VSSUBU => "vssubu.vv"
  | .VV_VSSUB => "vssub.vv"
  | .VV_VSLL => "vsll.vv"
  | .VV_VSMUL => "vsmul.vv"
  | .VV_VSRL => "vsrl.vv"
  | .VV_VSRA => "vsra.vv"
  | .VV_VSSRL => "vssrl.vv"
  | .VV_VSSRA => "vssra.vv"
  | .VV_VMINU => "vminu.vv"
  | .VV_VMIN => "vmin.vv"
  | .VV_VMAXU => "vmaxu.vv"
  | .VV_VMAX => "vmax.vv"

def vwabda_vv_mnemonic_forwards (arg_ : zvabd_vwabda_func6) : String :=
  match arg_ with
  | .VWABDA => "vwabda.vv"
  | .VWABDAU => "vwabdau.vv"

def vwabda_vx_mnemonic_forwards (arg_ : zvabd_vwabda_func6) : String :=
  match arg_ with
  | .VWABDA => "vwabda.vx"
  | .VWABDAU => "vwabdau.vx"

def vxcmptype_mnemonic_forwards (arg_ : vxcmpfunct6) : String :=
  match arg_ with
  | .VXCMP_VMSEQ => "vmseq.vx"
  | .VXCMP_VMSNE => "vmsne.vx"
  | .VXCMP_VMSLTU => "vmsltu.vx"
  | .VXCMP_VMSLT => "vmslt.vx"
  | .VXCMP_VMSLEU => "vmsleu.vx"
  | .VXCMP_VMSLE => "vmsle.vx"
  | .VXCMP_VMSGTU => "vmsgtu.vx"
  | .VXCMP_VMSGT => "vmsgt.vx"

def vxmctype_mnemonic_forwards (arg_ : vxmcfunct6) : String :=
  match arg_ with
  | .VXMC_VMADC => "vmadc.vx"
  | .VXMC_VMSBC => "vmsbc.vx"

def vxmstype_mnemonic_forwards (arg_ : vxmsfunct6) : String :=
  match arg_ with
  | .VXMS_VADC => "vadc.vxm"
  | .VXMS_VSBC => "vsbc.vxm"

def vxmtype_mnemonic_forwards (arg_ : vxmfunct6) : String :=
  match arg_ with
  | .VXM_VMADC => "vmadc.vxm"
  | .VXM_VMSBC => "vmsbc.vxm"

def vxsg_mnemonic_forwards (arg_ : vxsgfunct6) : String :=
  match arg_ with
  | .VX_VSLIDEUP => "vslideup.vx"
  | .VX_VSLIDEDOWN => "vslidedown.vx"
  | .VX_VRGATHER => "vrgather.vx"

def vxtype_mnemonic_forwards (arg_ : vxfunct6) : String :=
  match arg_ with
  | .VX_VADD => "vadd.vx"
  | .VX_VSUB => "vsub.vx"
  | .VX_VRSUB => "vrsub.vx"
  | .VX_VAND => "vand.vx"
  | .VX_VOR => "vor.vx"
  | .VX_VXOR => "vxor.vx"
  | .VX_VSADDU => "vsaddu.vx"
  | .VX_VSADD => "vsadd.vx"
  | .VX_VSSUBU => "vssubu.vx"
  | .VX_VSSUB => "vssub.vx"
  | .VX_VSLL => "vsll.vx"
  | .VX_VSMUL => "vsmul.vx"
  | .VX_VSRL => "vsrl.vx"
  | .VX_VSRA => "vsra.vx"
  | .VX_VSSRL => "vssrl.vx"
  | .VX_VSSRA => "vssra.vx"
  | .VX_VMINU => "vminu.vx"
  | .VX_VMIN => "vmin.vx"
  | .VX_VMAXU => "vmaxu.vx"
  | .VX_VMAX => "vmax.vx"

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8] -/
def width_mnemonic_forwards (arg_ : Nat) : String :=
  match arg_ with
  | 1 => "b"
  | 2 => "h"
  | 4 => "w"
  | _ => "d"

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8, 16] -/
def width_mnemonic_wide_forwards (arg_ : Nat) : String :=
  match arg_ with
  | 1 => "b"
  | 2 => "h"
  | 4 => "w"
  | 8 => "d"
  | _ => "q"

def wmvvtype_mnemonic_forwards (arg_ : wmvvfunct6) : String :=
  match arg_ with
  | .WMVV_VWMACCU => "vwmaccu.vv"
  | .WMVV_VWMACC => "vwmacc.vv"
  | .WMVV_VWMACCSU => "vwmaccsu.vv"

def wmvxtype_mnemonic_forwards (arg_ : wmvxfunct6) : String :=
  match arg_ with
  | .WMVX_VWMACCU => "vwmaccu.vx"
  | .WMVX_VWMACC => "vwmacc.vx"
  | .WMVX_VWMACCUS => "vwmaccus.vx"
  | .WMVX_VWMACCSU => "vwmaccsu.vx"

def wvtype_mnemonic_forwards (arg_ : wvfunct6) : String :=
  match arg_ with
  | .WV_VADD => "vwadd.wv"
  | .WV_VSUB => "vwsub.wv"
  | .WV_VADDU => "vwaddu.wv"
  | .WV_VSUBU => "vwsubu.wv"

def wvvtype_mnemonic_forwards (arg_ : wvvfunct6) : String :=
  match arg_ with
  | .WVV_VADD => "vwadd.vv"
  | .WVV_VSUB => "vwsub.vv"
  | .WVV_VADDU => "vwaddu.vv"
  | .WVV_VSUBU => "vwsubu.vv"
  | .WVV_VWMUL => "vwmul.vv"
  | .WVV_VWMULU => "vwmulu.vv"
  | .WVV_VWMULSU => "vwmulsu.vv"

def wvxtype_mnemonic_forwards (arg_ : wvxfunct6) : String :=
  match arg_ with
  | .WVX_VADD => "vwadd.vx"
  | .WVX_VSUB => "vwsub.vx"
  | .WVX_VADDU => "vwaddu.vx"
  | .WVX_VSUBU => "vwsubu.vx"
  | .WVX_VWMUL => "vwmul.vx"
  | .WVX_VWMULU => "vwmulu.vx"
  | .WVX_VWMULSU => "vwmulsu.vx"

def wxtype_mnemonic_forwards (arg_ : wxfunct6) : String :=
  match arg_ with
  | .WX_VADD => "vwadd.wx"
  | .WX_VSUB => "vwsub.wx"
  | .WX_VADDU => "vwaddu.wx"
  | .WX_VSUBU => "vwsubu.wx"

def zba_rtype_mnemonic_forwards (arg_ : (BitVec 2)) : SailM String := do
  match arg_ with
  | 0b01 => (pure "sh1add")
  | 0b10 => (pure "sh2add")
  | 0b11 => (pure "sh3add")
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def zba_rtypeuw_mnemonic_forwards (arg_ : (BitVec 2)) : String :=
  match arg_ with
  | 0b00 => "add.uw"
  | 0b01 => "sh1add.uw"
  | 0b10 => "sh2add.uw"
  | _ => "sh3add.uw"

def zbb_extop_mnemonic_forwards (arg_ : extop_zbb) : String :=
  match arg_ with
  | .SEXTB => "sext.b"
  | .SEXTH => "sext.h"
  | .ZEXTH => "zext.h"

def zbb_rtype_mnemonic_forwards (arg_ : brop_zbb) : String :=
  match arg_ with
  | .ANDN => "andn"
  | .ORN => "orn"
  | .XNOR => "xnor"
  | .MAX => "max"
  | .MAXU => "maxu"
  | .MIN => "min"
  | .MINU => "minu"
  | .ROL => "rol"
  | .ROR => "ror"

def zbb_rtypew_mnemonic_forwards (arg_ : bropw_zbb) : String :=
  match arg_ with
  | .ROLW => "rolw"
  | .RORW => "rorw"

def zbkb_rtype_mnemonic_forwards (arg_ : brop_zbkb) : String :=
  match arg_ with
  | .PACK => "pack"
  | .PACKH => "packh"

def zbs_iop_mnemonic_forwards (arg_ : biop_zbs) : String :=
  match arg_ with
  | .BCLRI => "bclri"
  | .BEXTI => "bexti"
  | .BINVI => "binvi"
  | .BSETI => "bseti"

def zbs_rtype_mnemonic_forwards (arg_ : brop_zbs) : String :=
  match arg_ with
  | .BCLR => "bclr"
  | .BEXT => "bext"
  | .BINV => "binv"
  | .BSET => "bset"

def zicond_mnemonic_forwards (arg_ : zicondop) : String :=
  match arg_ with
  | .CZERO_EQZ => "czero.eqz"
  | .CZERO_NEZ => "czero.nez"

/-- Type quantifiers: k_ex1818823_ : Bool, width : Nat, List.elem width [1, 2, 4, 8] -/
def valid_load_encdec (width : Nat) (is_unsigned : Bool) : Bool :=
  ((width <b xlen_bytes) || ((not is_unsigned) && (width ≤b xlen_bytes)))

/-- Type quantifiers: k_ex1818825_ : Bool, width : Nat, List.elem width [1, 2, 4, 8] -/
def zilx_encoding_valid (mode : zilx_mode) (width : Nat) (is_unsigned : Bool) : Bool :=
  ((valid_load_encdec width is_unsigned) && (((bne mode ZILX_UNSCALED) || (width != 1)) && ((bne
          mode ZILX_SCALED_UW) || (xlen == 64))))

def zilx_mode_mnemonic_forwards (arg_ : zilx_mode) : String :=
  match arg_ with
  | .ZILX_UNSCALED => "lx"
  | .ZILX_SCALED => "lxs"
  | .ZILX_SCALED_UW => "lxsuw"

def zreg : regidx := (Regidx (zero_extend (m := 5) 0b00#2))

def assembly_forwards (arg_ : instruction) : SailM String := do
  match arg_ with
  | .ZICBOP (cbop, rs1, offset) =>
    (pure (String.append (prefetch_mnemonic_forwards cbop)
        (String.append (spc_forwards ())
          (String.append (← (hex_bits_12_forwards offset))
            (String.append "("
              (String.append (opt_spc_forwards ())
                (String.append (← (reg_name_forwards rs1))
                  (String.append (opt_spc_forwards ()) (String.append ")" "")))))))))
  | .NTL op => (pure (String.append "ntl." (String.append (ntl_name_forwards op) "")))
  | .C_NTL op => (pure (String.append "c.ntl." (String.append (ntl_name_forwards op) "")))
  | .PAUSE () => (pure "pause")
  | .LPAD lpl =>
    (pure (String.append "lpad"
        (String.append (spc_forwards ()) (String.append (← (hex_bits_20_forwards lpl)) ""))))
  | .UTYPE (imm, rd, op) =>
    (pure (String.append (utype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_20_forwards imm)) ""))))))
  | .JAL (imm, rd) =>
    (pure (String.append "jal"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_21_forwards imm)) ""))))))
  | .JALR (imm, rs1, rd) =>
    (pure (String.append "jalr"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_12_forwards imm))
                (String.append "("
                  (String.append (← (reg_name_forwards rs1)) (String.append ")" "")))))))))
  | .BTYPE (imm, rs2, rs1, op) =>
    (pure (String.append (btype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs1))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs2))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_13_forwards imm)) ""))))))))
  | .ITYPE (imm, rs1, rd, op) =>
    (pure (String.append (itype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_12_forwards imm)) ""))))))))
  | .SHIFTIOP (shamt, rs1, rd, op) =>
    (pure (String.append (shiftiop_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))))
  | .RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (rtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .LOAD (imm, rs1, rd, is_unsigned, width) =>
    (pure (String.append "l"
        (String.append (width_mnemonic_forwards width)
          (String.append (maybe_u_forwards is_unsigned)
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_12_forwards imm))
                    (String.append "("
                      (String.append (← (reg_name_forwards rs1)) (String.append ")" "")))))))))))
  | .STORE (imm, rs2, rs1, width) =>
    (pure (String.append "s"
        (String.append (width_mnemonic_forwards width)
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rs2))
              (String.append (sep_forwards ())
                (String.append (← (hex_bits_signed_12_forwards imm))
                  (String.append (opt_spc_forwards ())
                    (String.append "("
                      (String.append (opt_spc_forwards ())
                        (String.append (← (reg_name_forwards rs1))
                          (String.append (opt_spc_forwards ()) (String.append ")" "")))))))))))))
  | .ADDIW (imm, rs1, rd) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "addiw"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_signed_12_forwards imm)) ""))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, op) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append (rtypew_mnemonic_forwards op)
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ())
                      (String.append (← (reg_name_forwards rs2)) ""))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIWOP (shamt, rs1, rd, op) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append (shiftiwop_mnemonic_forwards op)
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_5_forwards shamt)) ""))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FENCE_TSO () => (pure "fence.tso")
  | .FENCE (0b0000, pred, succ, rs, rd) =>
    (do
      if (((rs == zreg) && (rd == zreg)) : Bool)
      then
        (pure (HAppend.hAppend "fence"
            (HAppend.hAppend (spc_forwards ())
              (HAppend.hAppend (fence_bits_forwards pred)
                (HAppend.hAppend (sep_forwards ()) (fence_bits_forwards succ))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ECALL () => (pure "ecall")
  | .MRET () => (pure "mret")
  | .SRET () => (pure "sret")
  | .EBREAK () => (pure "ebreak")
  | .WFI () => (pure "wfi")
  | .SFENCE_VMA (rs1, rs2) =>
    (pure (String.append "sfence.vma"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs1))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
  | .AMO (op, aq, rl, rs2, rs1, width, rd) =>
    (pure (String.append (amo_mnemonic_forwards op)
        (String.append "."
          (String.append (width_mnemonic_wide_forwards width)
            (String.append (maybe_aqrl_forwards (aq, rl))
              (String.append (spc_forwards ())
                (String.append (← (reg_name_forwards rd))
                  (String.append (sep_forwards ())
                    (String.append (← (reg_name_forwards rs2))
                      (String.append (sep_forwards ())
                        (String.append "("
                          (String.append (← (reg_name_forwards rs1)) (String.append ")" "")))))))))))))
  | .LOADRES (aq, rl, rs1, width, rd) =>
    (pure (String.append "lr."
        (String.append (width_mnemonic_forwards width)
          (String.append (maybe_aqrl_forwards (aq, rl))
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append "("
                    (String.append (← (reg_name_forwards rs1)) (String.append ")" ""))))))))))
  | .STORECON (aq, rl, rs2, rs1, width, rd) =>
    (pure (String.append "sc."
        (String.append (width_mnemonic_forwards width)
          (String.append (maybe_aqrl_forwards (aq, rl))
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs2))
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (← (reg_name_forwards rs1)) (String.append ")" ""))))))))))))
  | .MUL (rs2, rs1, rd, mul_op) =>
    (pure (String.append (← (mul_mnemonic_forwards mul_op))
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .DIV (rs2, rs1, rd, is_unsigned) =>
    (pure (String.append "div"
        (String.append (maybe_u_forwards is_unsigned)
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rd))
              (String.append (sep_forwards ())
                (String.append (← (reg_name_forwards rs1))
                  (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) "")))))))))
  | .REM (rs2, rs1, rd, is_unsigned) =>
    (pure (String.append "rem"
        (String.append (maybe_u_forwards is_unsigned)
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rd))
              (String.append (sep_forwards ())
                (String.append (← (reg_name_forwards rs1))
                  (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) "")))))))))
  | .MULW (rs2, rs1, rd) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "mulw"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ())
                      (String.append (← (reg_name_forwards rs2)) ""))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "div"
            (String.append (maybe_u_forwards is_unsigned)
              (String.append "w"
                (String.append (spc_forwards ())
                  (String.append (← (reg_name_forwards rd))
                    (String.append (sep_forwards ())
                      (String.append (← (reg_name_forwards rs1))
                        (String.append (sep_forwards ())
                          (String.append (← (reg_name_forwards rs2)) ""))))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "rem"
            (String.append (maybe_u_forwards is_unsigned)
              (String.append "w"
                (String.append (spc_forwards ())
                  (String.append (← (reg_name_forwards rd))
                    (String.append (sep_forwards ())
                      (String.append (← (reg_name_forwards rs1))
                        (String.append (sep_forwards ())
                          (String.append (← (reg_name_forwards rs2)) ""))))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SLLIUW (shamt, rs1, rd) =>
    (pure (String.append "slli.uw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))))
  | .ZBA_RTYPEUW (rs2, rs1, rd, shamt) =>
    (pure (String.append (zba_rtypeuw_mnemonic_forwards shamt)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .ZBA_RTYPE (rs2, rs1, rd, shamt) =>
    (pure (String.append (← (zba_rtype_mnemonic_forwards shamt))
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .RORIW (shamt, rs1, rd) =>
    (pure (String.append "roriw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards shamt)) ""))))))))
  | .RORI (shamt, rs1, rd) =>
    (pure (String.append "rori"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))))
  | .ZBB_RTYPEW (rs2, rs1, rd, op) =>
    (pure (String.append (zbb_rtypew_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .ZBB_RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (zbb_rtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .ZBB_EXTOP (rs1, rd, op) =>
    (pure (String.append (zbb_extop_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .REV8 (rs1, rd) =>
    (pure (String.append "rev8"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .ORCB (rs1, rd) =>
    (pure (String.append "orc.b"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .CPOP (rs1, rd) =>
    (pure (String.append "cpop"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .CPOPW (rs1, rd) =>
    (pure (String.append "cpopw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .CLZ (rs1, rd) =>
    (pure (String.append "clz"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .CLZW (rs1, rd) =>
    (pure (String.append "clzw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .CTZ (rs1, rd) =>
    (pure (String.append "ctz"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .CTZW (rs1, rd) =>
    (pure (String.append "ctzw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .CLMUL (rs2, rs1, rd) =>
    (pure (String.append "clmul"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .CLMULH (rs2, rs1, rd) =>
    (pure (String.append "clmulh"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .CLMULR (rs2, rs1, rd) =>
    (pure (String.append "clmulr"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .ZBS_IOP (shamt, rs1, rd, op) =>
    (pure (String.append (zbs_iop_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))))
  | .ZBS_RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (zbs_rtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .C_NOP 0b000000 => (pure "c.nop")
  | .C_NOP imm =>
    (do
      if ((imm != (zeros (n := 6))) : Bool)
      then
        (pure (String.append "c.nop"
            (String.append (spc_forwards ())
              (String.append (← (hex_bits_signed_6_forwards imm)) ""))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDI4SPN (rdc, nzimm) =>
    (do
      if ((nzimm != 0b00000000#8) : Bool)
      then
        (pure (String.append "c.addi4spn"
            (String.append (spc_forwards ())
              (String.append (← (creg_name_forwards rdc))
                (String.append (sep_forwards ())
                  (String.append (← (sp_reg_name_forwards ()))
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_10_forwards ((nzimm : (BitVec 8)) +++ 0b00#2)))
                        ""))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LW (uimm, rsc, rdc) =>
    (pure (String.append "c.lw"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rdc))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_7_forwards ((uimm : (BitVec 5)) +++ 0b00#2)))
                (String.append "("
                  (String.append (← (creg_name_forwards rsc)) (String.append ")" "")))))))))
  | .C_LD (uimm, rsc, rdc) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "c.ld"
            (String.append (spc_forwards ())
              (String.append (← (creg_name_forwards rdc))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 5)) +++ 0b000#3)))
                    (String.append "("
                      (String.append (← (creg_name_forwards rsc)) (String.append ")" "")))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SW (uimm, rsc1, rsc2) =>
    (pure (String.append "c.sw"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsc2))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_7_forwards ((uimm : (BitVec 5)) +++ 0b00#2)))
                (String.append "("
                  (String.append (← (creg_name_forwards rsc1)) (String.append ")" "")))))))))
  | .C_SD (uimm, rsc1, rsc2) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "c.sd"
            (String.append (spc_forwards ())
              (String.append (← (creg_name_forwards rsc2))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 5)) +++ 0b000#3)))
                    (String.append "("
                      (String.append (← (creg_name_forwards rsc1)) (String.append ")" "")))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDI (imm, rsd) =>
    (do
      if ((bne rsd zreg) : Bool)
      then
        (pure (String.append "c.addi"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rsd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JAL imm =>
    (pure (String.append "c.jal"
        (String.append (spc_forwards ())
          (String.append (← (hex_bits_signed_12_forwards ((imm : (BitVec 11)) +++ 0#1))) ""))))
  | .C_ADDIW (imm, rsd) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "c.addiw"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rsd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LI (imm, rd) =>
    (pure (String.append "c.li"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
  | .C_ADDI16SP imm =>
    (do
      if ((imm != 0b000000#6) : Bool)
      then
        (pure (String.append "c.addi16sp"
            (String.append (spc_forwards ())
              (String.append (← (sp_reg_name_forwards ()))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_10_forwards ((imm : (BitVec 6)) +++ 0x0#4)))
                    ""))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LUI (imm, rd) =>
    (do
      if (((bne rd sp) && (imm != 0b000000#6)) : Bool)
      then
        (pure (String.append "c.lui"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SRLI (shamt, rsd) =>
    (pure (String.append "c.srli"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards shamt)) ""))))))
  | .C_SRAI (shamt, rsd) =>
    (pure (String.append "c.srai"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards shamt)) ""))))))
  | .C_ANDI (imm, rsd) =>
    (pure (String.append "c.andi"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
  | .C_SUB (rsd, rs2) =>
    (pure (String.append "c.sub"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
  | .C_XOR (rsd, rs2) =>
    (pure (String.append "c.xor"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
  | .C_OR (rsd, rs2) =>
    (pure (String.append "c.or"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
  | .C_AND (rsd, rs2) =>
    (pure (String.append "c.and"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
  | .C_SUBW (rsd, rs2) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "c.subw"
            (String.append (spc_forwards ())
              (String.append (← (creg_name_forwards rsd))
                (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDW (rsd, rs2) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "c.addw"
            (String.append (spc_forwards ())
              (String.append (← (creg_name_forwards rsd))
                (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_J imm =>
    (pure (String.append "c.j"
        (String.append (spc_forwards ())
          (String.append (← (hex_bits_signed_12_forwards ((imm : (BitVec 11)) +++ 0#1))) ""))))
  | .C_BEQZ (imm, rs) =>
    (pure (String.append "c.beqz"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rs))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_9_forwards ((imm : (BitVec 8)) +++ 0#1))) ""))))))
  | .C_BNEZ (imm, rs) =>
    (pure (String.append "c.bnez"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rs))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_9_forwards ((imm : (BitVec 8)) +++ 0#1))) ""))))))
  | .C_SLLI (shamt, rsd) =>
    (pure (String.append "c.slli"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards shamt)) ""))))))
  | .C_LWSP (uimm, rd) =>
    (do
      if ((bne rd zreg) : Bool)
      then
        (pure (String.append "c.lwsp"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 6)) +++ 0b00#2)))
                    (String.append "("
                      (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LDSP (uimm, rd) =>
    (do
      if (((bne rd zreg) && (xlen == 64)) : Bool)
      then
        (pure (String.append "c.ldsp"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_9_forwards ((uimm : (BitVec 6)) +++ 0b000#3)))
                    (String.append "("
                      (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SWSP (uimm, rs2) =>
    (pure (String.append "c.swsp"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs2))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 6)) +++ 0b00#2)))
                (String.append "("
                  (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
  | .C_SDSP (uimm, rs2) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "c.sdsp"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rs2))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_9_forwards ((uimm : (BitVec 6)) +++ 0b000#3)))
                    (String.append "("
                      (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JR rs1 =>
    (do
      if ((bne rs1 zreg) : Bool)
      then
        (pure (String.append "c.jr"
            (String.append (spc_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JALR rs1 =>
    (do
      if ((bne rs1 zreg) : Bool)
      then
        (pure (String.append "c.jalr"
            (String.append (spc_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_MV (rd, rs2) =>
    (do
      if ((bne rs2 zreg) : Bool)
      then
        (pure (String.append "c.mv"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_EBREAK () => (pure "c.ebreak")
  | .C_ADD (rsd, rs2) =>
    (do
      if ((bne rs2 zreg) : Bool)
      then
        (pure (String.append "c.add"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rsd))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LBU (uimm, rdc, rsc1) =>
    (pure (String.append "c.lbu"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rdc))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_2_forwards uimm))
                (String.append (opt_spc_forwards ())
                  (String.append "("
                    (String.append (opt_spc_forwards ())
                      (String.append (← (creg_name_forwards rsc1))
                        (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))))))
  | .C_LHU (uimm, rdc, rsc1) =>
    (pure (String.append "c.lhu"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rdc))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_2_forwards uimm))
                (String.append (opt_spc_forwards ())
                  (String.append "("
                    (String.append (opt_spc_forwards ())
                      (String.append (← (creg_name_forwards rsc1))
                        (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))))))
  | .C_LH (uimm, rdc, rsc1) =>
    (pure (String.append "c.lh"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rdc))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_2_forwards uimm))
                (String.append (opt_spc_forwards ())
                  (String.append "("
                    (String.append (opt_spc_forwards ())
                      (String.append (← (creg_name_forwards rsc1))
                        (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))))))
  | .C_SB (uimm, rsc1, rsc2) =>
    (pure (String.append "c.sb"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsc2))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_2_forwards uimm))
                (String.append (opt_spc_forwards ())
                  (String.append "("
                    (String.append (opt_spc_forwards ())
                      (String.append (← (creg_name_forwards rsc1))
                        (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))))))
  | .C_SH (uimm, rsc1, rsc2) =>
    (pure (String.append "c.sh"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsc2))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_2_forwards uimm))
                (String.append (opt_spc_forwards ())
                  (String.append "("
                    (String.append (opt_spc_forwards ())
                      (String.append (← (creg_name_forwards rsc1))
                        (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))))))
  | .C_ZEXT_B rsdc =>
    (pure (String.append "c.zext.b"
        (String.append (spc_forwards ()) (String.append (← (creg_name_forwards rsdc)) ""))))
  | .C_SEXT_B rsdc =>
    (pure (String.append "c.sext.b"
        (String.append (spc_forwards ()) (String.append (← (creg_name_forwards rsdc)) ""))))
  | .C_ZEXT_H rsdc =>
    (pure (String.append "c.zext.h"
        (String.append (spc_forwards ()) (String.append (← (creg_name_forwards rsdc)) ""))))
  | .C_SEXT_H rsdc =>
    (pure (String.append "c.sext.h"
        (String.append (spc_forwards ()) (String.append (← (creg_name_forwards rsdc)) ""))))
  | .C_ZEXT_W rsdc =>
    (pure (String.append "c.zext.w"
        (String.append (spc_forwards ()) (String.append (← (creg_name_forwards rsdc)) ""))))
  | .C_NOT rsdc =>
    (pure (String.append "c.not"
        (String.append (spc_forwards ()) (String.append (← (creg_name_forwards rsdc)) ""))))
  | .C_MUL (rsdc, rsc2) =>
    (pure (String.append "c.mul"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsdc))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rsc2)) ""))))))
  | .HLVTYPE (width, op, is_unsigned, rs1, rd) =>
    (pure (String.append "hlv"
        (String.append (maybe_hlvx_forwards op)
          (String.append "."
            (String.append (width_mnemonic_forwards width)
              (String.append (maybe_u_forwards is_unsigned)
                (String.append (spc_forwards ())
                  (String.append (← (reg_name_forwards rd))
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (← (reg_name_forwards rs1)) (String.append ")" ""))))))))))))
  | .HSV (width, rs1, rs2) =>
    (pure (String.append "hsv."
        (String.append (width_mnemonic_forwards width)
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rs2))
              (String.append (sep_forwards ())
                (String.append "("
                  (String.append (← (reg_name_forwards rs1)) (String.append ")" "")))))))))
  | .HFENCE_VVMA (rs1, rs2) =>
    (pure (String.append "hfence.vvma"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs1))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
  | .HFENCE_GVMA (rs1, rs2) =>
    (pure (String.append "hfence.gvma"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs1))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
  | .LOAD_FP (imm, rs1, rd, width) =>
    (pure (String.append "fl"
        (String.append (width_mnemonic_forwards width)
          (String.append (spc_forwards ())
            (String.append (← (freg_name_forwards rd))
              (String.append (sep_forwards ())
                (String.append (← (hex_bits_signed_12_forwards imm))
                  (String.append (opt_spc_forwards ())
                    (String.append "("
                      (String.append (opt_spc_forwards ())
                        (String.append (← (reg_name_forwards rs1))
                          (String.append (opt_spc_forwards ()) (String.append ")" "")))))))))))))
  | .STORE_FP (imm, rs2, rs1, width) =>
    (pure (String.append "fs"
        (String.append (width_mnemonic_forwards width)
          (String.append (spc_forwards ())
            (String.append (← (freg_name_forwards rs2))
              (String.append (sep_forwards ())
                (String.append (← (hex_bits_signed_12_forwards imm))
                  (String.append (opt_spc_forwards ())
                    (String.append "("
                      (String.append (opt_spc_forwards ())
                        (String.append (← (reg_name_forwards rs1))
                          (String.append (opt_spc_forwards ()) (String.append ")" "")))))))))))))
  | .F_MADD_TYPE_S (rs3, rs2, rs1, rm, rd, op) =>
    (pure (String.append (f_madd_type_mnemonic_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (freg_or_reg_name_forwards rs2))
                    (String.append (sep_forwards ())
                      (String.append (← (freg_or_reg_name_forwards rs3))
                        (String.append (sep_forwards ())
                          (String.append (frm_mnemonic_forwards rm) ""))))))))))))
  | .F_BIN_RM_TYPE_S (rs2, rs1, rm, rd, op) =>
    (pure (String.append (f_bin_rm_type_mnemonic_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (freg_or_reg_name_forwards rs2))
                    (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))))
  | .F_UN_RM_FF_TYPE_S (rs1, rm, rd, .FSQRT_S) =>
    (pure (String.append "fsqrt.s"
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_UN_RM_FX_TYPE_S (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_fx_type_mnemonic_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_UN_RM_XF_TYPE_S (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_xf_type_mnemonic_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_BIN_TYPE_F_S (rs2, rs1, rd, op) =>
    (pure (String.append (f_bin_type_mnemonic_f_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (freg_or_reg_name_forwards rs2)) ""))))))))
  | .F_BIN_TYPE_X_S (rs2, rs1, rd, op) =>
    (pure (String.append (f_bin_type_mnemonic_x_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (freg_or_reg_name_forwards rs2)) ""))))))))
  | .F_UN_TYPE_X_S (rs1, rd, op) =>
    (pure (String.append (f_un_type_mnemonic_x_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1)) ""))))))
  | .F_UN_TYPE_F_S (rs1, rd, op) =>
    (pure (String.append (f_un_type_mnemonic_f_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .C_FLWSP (imm, rd) =>
    (pure (String.append "c.flwsp"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_8_forwards ((imm : (BitVec 6)) +++ 0b00#2)))
                (String.append "("
                  (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
  | .C_FSWSP (uimm, rs2) =>
    (pure (String.append "c.fswsp"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rs2))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 6)) +++ 0b00#2)))
                (String.append "("
                  (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
  | .C_FLW (uimm, rsc, rdc) =>
    (pure (String.append "c.flw"
        (String.append (spc_forwards ())
          (String.append (← (cfreg_name_forwards rdc))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_7_forwards ((uimm : (BitVec 5)) +++ 0b00#2)))
                (String.append "("
                  (String.append (← (creg_name_forwards rsc)) (String.append ")" "")))))))))
  | .C_FSW (uimm, rsc1, rsc2) =>
    (pure (String.append "c.fsw"
        (String.append (spc_forwards ())
          (String.append (← (cfreg_name_forwards rsc2))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_7_forwards ((uimm : (BitVec 5)) +++ 0b00#2)))
                (String.append "("
                  (String.append (← (creg_name_forwards rsc1)) (String.append ")" "")))))))))
  | .F_MADD_TYPE_D (rs3, rs2, rs1, rm, rd, op) =>
    (pure (String.append (f_madd_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (freg_or_reg_name_forwards rs2))
                    (String.append (sep_forwards ())
                      (String.append (← (freg_or_reg_name_forwards rs3))
                        (String.append (sep_forwards ())
                          (String.append (frm_mnemonic_forwards rm) ""))))))))))))
  | .F_BIN_RM_TYPE_D (rs2, rs1, rm, rd, op) =>
    (pure (String.append (f_bin_rm_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (freg_or_reg_name_forwards rs2))
                    (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))))
  | .F_UN_RM_FF_TYPE_D (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_ff_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_UN_RM_FX_TYPE_D (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_fx_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_UN_RM_XF_TYPE_D (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_xf_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_BIN_F_TYPE_D (rs2, rs1, rd, op) =>
    (pure (String.append (f_bin_f_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (freg_or_reg_name_forwards rs2)) ""))))))))
  | .F_BIN_X_TYPE_D (rs2, rs1, rd, op) =>
    (pure (String.append (f_bin_x_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (freg_or_reg_name_forwards rs2)) ""))))))))
  | .F_UN_X_TYPE_D (rs1, rd, op) =>
    (pure (String.append (f_un_x_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1)) ""))))))
  | .F_UN_F_TYPE_D (rs1, rd, op) =>
    (pure (String.append (f_un_f_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .C_FLDSP (uimm, rd) =>
    (pure (String.append "c.fldsp"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_9_forwards ((uimm : (BitVec 6)) +++ 0b000#3)))
                (String.append "("
                  (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
  | .C_FSDSP (uimm, rs2) =>
    (pure (String.append "c.fsdsp"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rs2))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_9_forwards ((uimm : (BitVec 6)) +++ 0b000#3)))
                (String.append "("
                  (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
  | .C_FLD (uimm, rsc, rdc) =>
    (pure (String.append "c.fld"
        (String.append (spc_forwards ())
          (String.append (← (cfreg_name_forwards rdc))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 5)) +++ 0b000#3)))
                (String.append "("
                  (String.append (← (creg_name_forwards rsc)) (String.append ")" "")))))))))
  | .C_FSD (uimm, rsc1, rsc2) =>
    (pure (String.append "c.fsd"
        (String.append (spc_forwards ())
          (String.append (← (cfreg_name_forwards rsc2))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 5)) +++ 0b000#3)))
                (String.append "("
                  (String.append (← (creg_name_forwards rsc1)) (String.append ")" "")))))))))
  | .F_BIN_RM_TYPE_H (rs2, rs1, rm, rd, op) =>
    (pure (String.append (f_bin_rm_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (freg_or_reg_name_forwards rs2))
                    (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))))
  | .F_MADD_TYPE_H (rs3, rs2, rs1, rm, rd, op) =>
    (pure (String.append (f_madd_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (freg_or_reg_name_forwards rs2))
                    (String.append (sep_forwards ())
                      (String.append (← (freg_or_reg_name_forwards rs3))
                        (String.append (sep_forwards ())
                          (String.append (frm_mnemonic_forwards rm) ""))))))))))))
  | .F_BIN_F_TYPE_H (rs2, rs1, rd, op) =>
    (pure (String.append (f_bin_f_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (freg_or_reg_name_forwards rs2)) ""))))))))
  | .F_BIN_X_TYPE_H (rs2, rs1, rd, op) =>
    (pure (String.append (f_bin_x_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (freg_or_reg_name_forwards rs2)) ""))))))))
  | .F_UN_RM_FF_TYPE_H (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_ff_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_UN_RM_FX_TYPE_H (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_fx_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_UN_RM_XF_TYPE_H (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_xf_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_or_reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_UN_F_TYPE_H (rs1, rd, op) =>
    (pure (String.append (f_un_f_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .F_UN_X_TYPE_H (rs1, rd, op) =>
    (pure (String.append (f_un_x_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_or_reg_name_forwards rs1)) ""))))))
  | .FLI_H (constantidx, rd) =>
    (pure (String.append "fli.h"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_5_forwards constantidx)) ""))))))
  | .FLI_S (constantidx, rd) =>
    (pure (String.append "fli.s"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_5_forwards constantidx)) ""))))))
  | .FLI_D (constantidx, rd) =>
    (pure (String.append "fli.d"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_5_forwards constantidx)) ""))))))
  | .FMINM_H (rs2, rs1, rd) =>
    (pure (String.append "fminm.h"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs2)) ""))))))))
  | .FMAXM_H (rs2, rs1, rd) =>
    (pure (String.append "fmaxm.h"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs2)) ""))))))))
  | .FMINM_S (rs2, rs1, rd) =>
    (pure (String.append "fminm.s"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs2)) ""))))))))
  | .FMAXM_S (rs2, rs1, rd) =>
    (pure (String.append "fmaxm.s"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs2)) ""))))))))
  | .FMINM_D (rs2, rs1, rd) =>
    (pure (String.append "fminm.d"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs2)) ""))))))))
  | .FMAXM_D (rs2, rs1, rd) =>
    (pure (String.append "fmaxm.d"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs2)) ""))))))))
  | .FROUND_H (rs1, rm, rd) =>
    (pure (String.append "fround.h"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .FROUNDNX_H (rs1, rm, rd) =>
    (pure (String.append "froundnx.h"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .FROUND_S (rs1, rm, rd) =>
    (pure (String.append "fround.s"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .FROUNDNX_S (rs1, rm, rd) =>
    (pure (String.append "froundnx.s"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .FROUND_D (rs1, rm, rd) =>
    (pure (String.append "fround.d"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .FROUNDNX_D (rs1, rm, rd) =>
    (pure (String.append "froundnx.d"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .FMVH_X_D (rs1, rd) =>
    (pure (String.append "fmvh.x.d"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs1)) ""))))))
  | .FMVP_D_X (rs2, rs1, rd) =>
    (pure (String.append "fmvp.d.x"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .FLEQ_H (rs2, rs1, rd) =>
    (pure (String.append "fleq.h"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs2)) ""))))))))
  | .FLTQ_H (rs2, rs1, rd) =>
    (pure (String.append "fltq.h"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs2)) ""))))))))
  | .FLEQ_S (rs2, rs1, rd) =>
    (pure (String.append "fleq.s"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs2)) ""))))))))
  | .FLTQ_S (rs2, rs1, rd) =>
    (pure (String.append "fltq.s"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs2)) ""))))))))
  | .FLEQ_D (rs2, rs1, rd) =>
    (pure (String.append "fleq.d"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs2)) ""))))))))
  | .FLTQ_D (rs2, rs1, rd) =>
    (pure (String.append "fltq.d"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs2)) ""))))))))
  | .FCVTMOD_W_D (rs1, rd) =>
    (pure (String.append "fcvtmod.w.d"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append "rtz" ""))))))))
  | .VSETVLI (vtr, ma, ta, sew, lmul, rs1, rd) =>
    (pure (String.append "vsetvli"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (vtype_assembly_forwards (vtr, ma, ta, sew, lmul))) ""))))))))
  | .VSETVL (rs2, rs1, rd) =>
    (pure (String.append "vsetvl"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .VSETIVLI (vtr, ma, ta, sew, lmul, uimm, rd) =>
    (pure (String.append "vsetivli"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_5_forwards uimm))
                (String.append (sep_forwards ())
                  (String.append (← (vtype_assembly_forwards (vtr, ma, ta, sew, lmul))) ""))))))))
  | .VVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (vvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .NVSTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (nvstype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .NVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (nvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .MASKTYPEV (vs2, vs1, vd) =>
    (pure (String.append "vmerge.vvm"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .MOVETYPEV (vs1, vd) =>
    (pure (String.append "vmv.v.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs1) ""))))))
  | .VXTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (vxtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .NXSTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (nxstype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .NXTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (nxtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VXSG (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (vxsg_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .MASKTYPEX (vs2, rs1, vd) =>
    (pure (String.append "vmerge.vxm"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .MOVETYPEX (rs1, vd) =>
    (pure (String.append "vmv.v.x"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .VITYPE (funct6, vm, vs2, simm, vd) =>
    (pure (String.append (vitype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_5_forwards simm))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .NISTYPE (funct6, vm, vs2, uimm, vd) =>
    (pure (String.append (nistype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards uimm))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .NITYPE (funct6, vm, vs2, uimm, vd) =>
    (pure (String.append (nitype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards uimm))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VISG (funct6, vm, vs2, simm, vd) =>
    (pure (String.append (visg_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_5_forwards simm))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .MASKTYPEI (vs2, simm, vd) =>
    (pure (String.append "vmerge.vim"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_5_forwards simm))
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .MOVETYPEI (vd, simm) =>
    (pure (String.append "vmv.v.i"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_5_forwards simm)) ""))))))
  | .VMVRTYPE (vs2, nreg, vd) =>
    (pure (String.append "vmv"
        (String.append (nreg_string_forwards nreg)
          (String.append "r.v"
            (String.append (spc_forwards ())
              (String.append (vreg_name_forwards vd)
                (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs2) ""))))))))
  | .MVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (mvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .MVVMATYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (mvvmatype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs1)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .WVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (wvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .WVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (wvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .WMVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (wmvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs1)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VEXTTYPE (funct6, vm, vs2, vd) =>
    (pure (String.append (vexttype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VMVXS (vs2, rd) =>
    (pure (String.append "vmv.x.s"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs2) ""))))))
  | .MVVCOMPRESS (vs2, vs1, vd) =>
    (pure (String.append "vcompress.vm"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs1) ""))))))))
  | .MVXTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (mvxtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .MVXMATYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (mvxmatype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .WVXTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (wvxtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .WXTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (wxtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .WMVXTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (wmvxtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VMVSX (rs1, vd) =>
    (pure (String.append "vmv.s.x"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .FVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (fvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FVVMATYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (fvvmatype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs1)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FWVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (fwvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FWVVMATYPE (funct6, vm, vs1, vs2, vd) =>
    (pure (String.append (fwvvmatype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs1)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FWVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (fwvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VFUNARY0 (vm, vs2, vfunary0, vd) =>
    (pure (String.append (vfunary0_mnemonic_forwards vfunary0)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VFWUNARY0 (vm, vs2, vfwunary0, vd) =>
    (pure (String.append (vfwunary0_mnemonic_forwards vfwunary0)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VFNUNARY0 (vm, vs2, vfnunary0, vd) =>
    (pure (String.append (vfnunary0_mnemonic_forwards vfnunary0)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VFUNARY1 (vm, vs2, vfunary1, vd) =>
    (pure (String.append (vfunary1_mnemonic_forwards vfunary1)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VFMVFS (vs2, rd) =>
    (pure (String.append "vfmv.f.s"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs2) ""))))))
  | .FVFTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (fvftype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (freg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FVFMATYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (fvfmatype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FWVFTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (fwvftype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (freg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FWVFMATYPE (funct6, vm, rs1, vs2, vd) =>
    (pure (String.append (fwvfmatype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FWFTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (fwftype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (freg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VFMERGE (vs2, rs1, vd) =>
    (pure (String.append "vfmerge.vfm"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (freg_name_forwards rs1))
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .VFMV (rs1, vd) =>
    (pure (String.append "vfmv.v.f"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs1)) ""))))))
  | .VFMVSF (rs1, vd) =>
    (pure (String.append "vfmv.s.f"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (← (freg_name_forwards rs1)) ""))))))
  | .VLSEGTYPE (nf, vm, rs1, width, vd) =>
    (pure (String.append "vl"
        (String.append (nfields_string_forwards nf)
          (String.append "e"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append ".v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vd)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (← (reg_name_forwards rs1))
                          (String.append ")" (String.append (maybe_vmask_backwards vm) "")))))))))))))
  | .VLSEGFFTYPE (nf, vm, rs1, width, vd) =>
    (pure (String.append "vl"
        (String.append (nfields_string_forwards nf)
          (String.append "e"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append "ff.v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vd)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (← (reg_name_forwards rs1))
                          (String.append ")" (String.append (maybe_vmask_backwards vm) "")))))))))))))
  | .VSSEGTYPE (nf, vm, rs1, width, vs3) =>
    (pure (String.append "vs"
        (String.append (nfields_string_forwards nf)
          (String.append "e"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append ".v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vs3)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (← (reg_name_forwards rs1))
                          (String.append ")" (String.append (maybe_vmask_backwards vm) "")))))))))))))
  | .VLSSEGTYPE (nf, vm, rs2, rs1, width, vd) =>
    (pure (String.append "vls"
        (String.append (nfields_string_forwards nf)
          (String.append "e"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append ".v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vd)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (← (reg_name_forwards rs1))
                          (String.append ")"
                            (String.append (sep_forwards ())
                              (String.append (← (reg_name_forwards rs2))
                                (String.append (maybe_vmask_backwards vm) "")))))))))))))))
  | .VSSSEGTYPE (nf, vm, rs2, rs1, width, vs3) =>
    (pure (String.append "vss"
        (String.append (nfields_string_forwards nf)
          (String.append "e"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append ".v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vs3)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (← (reg_name_forwards rs1))
                          (String.append ")"
                            (String.append (sep_forwards ())
                              (String.append (← (reg_name_forwards rs2))
                                (String.append (maybe_vmask_backwards vm) "")))))))))))))))
  | .VLXSEGTYPE (nf, vm, vs2, rs1, width, vd, mop) =>
    (pure (String.append "vl"
        (String.append (indexed_mop_mnemonic_forwards mop)
          (String.append "x"
            (String.append (nfields_string_forwards nf)
              (String.append "ei"
                (String.append (vlewidth_bitsnumberstr_forwards width)
                  (String.append ".v"
                    (String.append (spc_forwards ())
                      (String.append (vreg_name_forwards vd)
                        (String.append (sep_forwards ())
                          (String.append "("
                            (String.append (← (reg_name_forwards rs1))
                              (String.append ")"
                                (String.append (sep_forwards ())
                                  (String.append (vreg_name_forwards vs2)
                                    (String.append (maybe_vmask_backwards vm) "")))))))))))))))))
  | .VSXSEGTYPE (nf, vm, vs2, rs1, width, vs3, mop) =>
    (pure (String.append "vs"
        (String.append (indexed_mop_mnemonic_forwards mop)
          (String.append "x"
            (String.append (nfields_string_forwards nf)
              (String.append "ei"
                (String.append (vlewidth_bitsnumberstr_forwards width)
                  (String.append ".v"
                    (String.append (spc_forwards ())
                      (String.append (vreg_name_forwards vs3)
                        (String.append (sep_forwards ())
                          (String.append "("
                            (String.append (← (reg_name_forwards rs1))
                              (String.append ")"
                                (String.append (sep_forwards ())
                                  (String.append (vreg_name_forwards vs2)
                                    (String.append (maybe_vmask_backwards vm) "")))))))))))))))))
  | .VLRETYPE (nf, rs1, width, vd) =>
    (pure (String.append "vl"
        (String.append (nfields_pow2_string_forwards nf)
          (String.append "re"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append ".v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vd)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (← (reg_name_forwards rs1)) (String.append ")" ""))))))))))))
  | .VSRETYPE (nf, rs1, vs3) =>
    (pure (String.append "vs"
        (String.append (nfields_pow2_string_forwards nf)
          (String.append "r.v"
            (String.append (spc_forwards ())
              (String.append (vreg_name_forwards vs3)
                (String.append (sep_forwards ())
                  (String.append "("
                    (String.append (← (reg_name_forwards rs1)) (String.append ")" ""))))))))))
  | .VMTYPE (rs1, vd_or_vs3, op) =>
    (pure (String.append (vmtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd_or_vs3)
            (String.append (sep_forwards ())
              (String.append "("
                (String.append (← (reg_name_forwards rs1)) (String.append ")" ""))))))))
  | .MMTYPE (funct6, vs2, vs1, vd) =>
    (pure (String.append (mmtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs1) ""))))))))
  | .VCPOP_M (vm, vs2, rd) =>
    (pure (String.append "vcpop.m"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VFIRST_M (vm, vs2, rd) =>
    (pure (String.append "vfirst.m"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VMSBF_M (vm, vs2, vd) =>
    (pure (String.append "vmsbf.m"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VMSIF_M (vm, vs2, vd) =>
    (pure (String.append "vmsif.m"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VMSOF_M (vm, vs2, vd) =>
    (pure (String.append "vmsof.m"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VIOTA_M (vm, vs2, vd) =>
    (pure (String.append "viota.m"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VID_V (vm, vd) =>
    (pure (String.append "vid.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd) (String.append (maybe_vmask_backwards vm) "")))))
  | .VVMTYPE (funct6, vs2, vs1, vd) =>
    (pure (String.append (vvmtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .VVMCTYPE (funct6, vs2, vs1, vd) =>
    (pure (String.append (vvmctype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs1) ""))))))))
  | .VVMSTYPE (funct6, vs2, vs1, vd) =>
    (pure (String.append (vvmstype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .VVCMPTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (vvcmptype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VXMTYPE (funct6, vs2, rs1, vd) =>
    (pure (String.append (vxmtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .VXMCTYPE (funct6, vs2, rs1, vd) =>
    (pure (String.append (vxmctype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))))
  | .VXMSTYPE (funct6, vs2, rs1, vd) =>
    (pure (String.append (vxmstype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .VXCMPTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (vxcmptype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VIMTYPE (funct6, vs2, simm, vd) =>
    (pure (String.append (vimtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_5_forwards simm))
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .VIMCTYPE (funct6, vs2, simm, vd) =>
    (pure (String.append (vimctype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_5_forwards simm)) ""))))))))
  | .VIMSTYPE (funct6, vs2, simm, vd) =>
    (pure (String.append (vimstype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_5_forwards simm))
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .VICMPTYPE (funct6, vm, vs2, simm, vd) =>
    (pure (String.append (vicmptype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_5_forwards simm))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FVVMTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (fvvmtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FVFMTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (fvfmtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (freg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .RIVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (rivvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .RMVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (rmvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .RFVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (rfvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .RFWVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (rfwvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .SHA256SIG0 (rs1, rd) =>
    (pure (String.append "sha256sig0"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .SHA256SIG1 (rs1, rd) =>
    (pure (String.append "sha256sig1"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .SHA256SUM0 (rs1, rd) =>
    (pure (String.append "sha256sum0"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .SHA256SUM1 (rs1, rd) =>
    (pure (String.append "sha256sum1"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .AES32ESMI (bs, rs2, rs1, rd) =>
    (pure (String.append "aes32esmi"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs2))
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_2_forwards bs)) ""))))))))))
  | .AES32ESI (bs, rs2, rs1, rd) =>
    (pure (String.append "aes32esi"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs2))
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_2_forwards bs)) ""))))))))))
  | .AES32DSMI (bs, rs2, rs1, rd) =>
    (pure (String.append "aes32dsmi"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs2))
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_2_forwards bs)) ""))))))))))
  | .AES32DSI (bs, rs2, rs1, rd) =>
    (pure (String.append "aes32dsi"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs2))
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_2_forwards bs)) ""))))))))))
  | .SHA512SIG0L (rs2, rs1, rd) =>
    (pure (String.append "sha512sig0l"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .SHA512SIG0H (rs2, rs1, rd) =>
    (pure (String.append "sha512sig0h"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .SHA512SIG1L (rs2, rs1, rd) =>
    (pure (String.append "sha512sig1l"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .SHA512SIG1H (rs2, rs1, rd) =>
    (pure (String.append "sha512sig1h"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .SHA512SUM0R (rs2, rs1, rd) =>
    (pure (String.append "sha512sum0r"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .SHA512SUM1R (rs2, rs1, rd) =>
    (pure (String.append "sha512sum1r"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .AES64KS1I (rnum, rs1, rd) =>
    (pure (String.append "aes64ks1i"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (hex_bits_4_forwards rnum)) ""))))))))
  | .AES64KS2 (rs2, rs1, rd) =>
    (pure (String.append "aes64ks2"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .AES64IM (rs1, rd) =>
    (pure (String.append "aes64im"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .AES64ESM (rs2, rs1, rd) =>
    (pure (String.append "aes64esm"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .AES64ES (rs2, rs1, rd) =>
    (pure (String.append "aes64es"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .AES64DSM (rs2, rs1, rd) =>
    (pure (String.append "aes64dsm"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .AES64DS (rs2, rs1, rd) =>
    (pure (String.append "aes64ds"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .SHA512SIG0 (rs1, rd) =>
    (pure (String.append "sha512sig0"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .SHA512SIG1 (rs1, rd) =>
    (pure (String.append "sha512sig1"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .SHA512SUM0 (rs1, rd) =>
    (pure (String.append "sha512sum0"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .SHA512SUM1 (rs1, rd) =>
    (pure (String.append "sha512sum1"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .SM3P0 (rs1, rd) =>
    (pure (String.append "sm3p0"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .SM3P1 (rs1, rd) =>
    (pure (String.append "sm3p1"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .SM4ED (bs, rs2, rs1, rd) =>
    (pure (String.append "sm4ed"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs2))
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_2_forwards bs)) ""))))))))))
  | .SM4KS (bs, rs2, rs1, rd) =>
    (pure (String.append "sm4ks"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs2))
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_2_forwards bs)) ""))))))))))
  | .ZBKB_RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (zbkb_rtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .ZBKB_PACKW (rs2, rs1, rd) =>
    (pure (String.append "packw"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .ZIP (rs1, rd) =>
    (pure (String.append "zip"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .UNZIP (rs1, rd) =>
    (pure (String.append "unzip"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .BREV8 (rs1, rd) =>
    (pure (String.append "brev8"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))
  | .XPERM8 (rs2, rs1, rd) =>
    (pure (String.append "xperm8"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .XPERM4 (rs2, rs1, rd) =>
    (pure (String.append "xperm4"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .VANDN_VV (vm, vs1, vs2, vd) =>
    (pure (String.append "vandn.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VANDN_VX (vm, vs2, rs1, vd) =>
    (pure (String.append "vandn.vx"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VBREV_V (vm, vs2, vd) =>
    (pure (String.append "vbrev.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VBREV8_V (vm, vs2, vd) =>
    (pure (String.append "vbrev8.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VREV8_V (vm, vs2, vd) =>
    (pure (String.append "vrev8.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VCLZ_V (vm, vs2, vd) =>
    (pure (String.append "vclz.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VCTZ_V (vm, vs2, vd) =>
    (pure (String.append "vctz.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VCPOP_V (vm, vs2, vd) =>
    (pure (String.append "vcpop.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VROL_VV (vm, vs1, vs2, vd) =>
    (pure (String.append "vrol.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VROL_VX (vm, vs2, rs1, vd) =>
    (pure (String.append "vrol.vx"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VROR_VV (vm, vs1, vs2, vd) =>
    (pure (String.append "vror.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VROR_VX (vm, vs2, rs1, vd) =>
    (pure (String.append "vror.vx"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VROR_VI (vm, vs2, uimm, vd) =>
    (pure (String.append "vror.vi"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards uimm))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VWSLL_VV (vm, vs2, vs1, vd) =>
    (pure (String.append "vwsll.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VWSLL_VX (vm, vs2, rs1, vd) =>
    (pure (String.append "vwsll.vx"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VWSLL_VI (vm, vs2, uimm, vd) =>
    (pure (String.append "vwsll.vi"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards uimm))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VCLMUL_VV (vm, vs2, vs1, vd) =>
    (pure (String.append "vclmul.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VCLMUL_VX (vm, vs2, rs1, vd) =>
    (pure (String.append "vclmul.vx"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VCLMULH_VV (vm, vs2, vs1, vd) =>
    (pure (String.append "vclmulh.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VCLMULH_VX (vm, vs2, rs1, vd) =>
    (pure (String.append "vclmulh.vx"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VGHSH_VV (vs2, vs1, vd) =>
    (pure (String.append "vghsh.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs1) ""))))))))
  | .VGMUL_VV (vs2, vd) =>
    (pure (String.append "vgmul.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs2) ""))))))
  | .VAESDF (funct6, vs2, vd) =>
    (pure (String.append (vaesdf_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs2) ""))))))
  | .VAESDM (funct6, vs2, vd) =>
    (pure (String.append (vaesdm_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs2) ""))))))
  | .VAESEF (funct6, vs2, vd) =>
    (pure (String.append (vaesef_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs2) ""))))))
  | .VAESEM (funct6, vs2, vd) =>
    (pure (String.append (vaesem_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs2) ""))))))
  | .VAESKF1_VI (vs2, rnd, vd) =>
    (pure (String.append "vaeskf1.vi"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (← (hex_bits_5_forwards rnd)) ""))))))))
  | .VAESKF2_VI (vs2, rnd, vd) =>
    (pure (String.append "vaeskf2.vi"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (← (hex_bits_5_forwards rnd)) ""))))))))
  | .VAESZ_VS (vs2, vd) =>
    (pure (String.append "vaesz.vs"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs2) ""))))))
  | .VSM4K_VI (vs2, uimm, vd) =>
    (pure (String.append "vsm4k.vi"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (← (hex_bits_5_forwards uimm)) ""))))))))
  | .ZVKSM4RTYPE (funct6, vs2, vd) =>
    (pure (String.append (vsm4r_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs2) ""))))))
  | .VSHA2MS_VV (vs2, vs1, vd) =>
    (pure (String.append "vsha2ms.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs1) ""))))))))
  | .ZVKSHA2TYPE (funct6, vs2, vs1, vd) =>
    (pure (String.append (vsha2_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs1) ""))))))))
  | .VSM3ME_VV (vs2, vs1, vd) =>
    (pure (String.append "vsm3me.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs1) ""))))))))
  | .VSM3C_VI (vs2, uimm, vd) =>
    (pure (String.append "vsm3c.vi"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (← (hex_bits_5_forwards uimm)) ""))))))))
  | .ZVABD_VV (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (vabd_vv_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .ZVABD_VX (.VABD, vm, vs2, rs1, vd) =>
    (do
      if ((rs1 == zreg) : Bool)
      then
        (pure (HAppend.hAppend "vabs.v"
            (HAppend.hAppend (spc_forwards ())
              (HAppend.hAppend (vreg_name_forwards vd)
                (HAppend.hAppend (sep_forwards ())
                  (HAppend.hAppend (vreg_name_forwards vs2) (maybe_vmask_backwards vm)))))))
      else
        (do
          match (ZVABD_VX (VABD, vm, vs2, rs1, vd)) with
          | .ZVABD_VX (funct6, vm, vs2, rs1, vd) =>
            (pure (String.append (vabd_vx_mnemonic_forwards funct6)
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vd)
                    (String.append (sep_forwards ())
                      (String.append (vreg_name_forwards vs2)
                        (String.append (sep_forwards ())
                          (String.append (← (reg_name_forwards rs1))
                            (String.append (maybe_vmask_backwards vm) "")))))))))
          | _ =>
            (do
              «assert» false "Pattern match failure at unknown location"
              throw Error.Exit)))
  | .ZVABD_VX (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (vabd_vx_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .ZVWABDA_VV (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (vwabda_vv_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .ZVWABDA_VX (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (vwabda_vx_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .CSRImm (csr, imm, rd, op) =>
    (pure (String.append (csr_mnemonic_forwards op)
        (String.append "i"
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rd))
              (String.append (sep_forwards ())
                (String.append (← (csr_name_map_forwards csr))
                  (String.append (sep_forwards ())
                    (String.append (← (hex_bits_5_forwards imm)) "")))))))))
  | .CSRReg (csr, rs1, rd, op) =>
    (pure (String.append (csr_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (csr_name_map_forwards csr))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))))
  | .SINVAL_VMA (rs1, rs2) =>
    (pure (String.append "sinval.vma"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs1))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
  | .SFENCE_W_INVAL () => (pure "sfence.w.inval")
  | .SFENCE_INVAL_IR () => (pure "sfence.inval.ir")
  | .HINVAL_VVMA (rs1, rs2) =>
    (pure (String.append "hinval.vvma"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs1))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
  | .HINVAL_GVMA (rs1, rs2) =>
    (pure (String.append "hinval.gvma"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs1))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
  | .WRS .WRS_STO => (pure "wrs.sto")
  | .WRS .WRS_NTO => (pure "wrs.nto")
  | .SSPUSH rs2 =>
    (pure (String.append "sspush"
        (String.append (spc_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))
  | .C_SSPUSH () =>
    (pure (String.append "c.sspush"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards (← (encdec_reg_backwards 0b00001#5)))) ""))))
  | .SSPOPCHK rs1 =>
    (pure (String.append "sspopchk"
        (String.append (spc_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))
  | .C_SSPOPCHK () =>
    (pure (String.append "c.sspopchk"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards (← (encdec_reg_backwards 0b00101#5)))) ""))))
  | .SSRDP rd =>
    (pure (String.append "ssrdp"
        (String.append (spc_forwards ()) (String.append (← (reg_name_forwards rd)) ""))))
  | .SSAMOSWAP (aq, rl, rs2, rs1, width, rd) =>
    (do
      if (((width == 4) || (width == 8)) : Bool)
      then
        (pure (String.append "ssamoswap."
            (String.append (width_mnemonic_forwards width)
              (String.append (maybe_aqrl_forwards (aq, rl))
                (String.append (spc_forwards ())
                  (String.append (← (reg_name_forwards rd))
                    (String.append (sep_forwards ())
                      (String.append (← (reg_name_forwards rs2))
                        (String.append (sep_forwards ())
                          (String.append "("
                            (String.append (opt_spc_forwards ())
                              (String.append (← (reg_name_forwards rs1))
                                (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZICOND_RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (zicond_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .ZICBOM (cbop, rs1) =>
    (pure (String.append (cbop_mnemonic_forwards cbop)
        (String.append (spc_forwards ())
          (String.append "("
            (String.append (opt_spc_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))
  | .BITYPE (imm, 0b00000, rs1, op) =>
    (pure (String.append (bitype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs1))
            (String.append (sep_forwards ())
              (String.append "-1"
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_13_forwards imm)) ""))))))))
  | .BITYPE (imm, cimm, rs1, op) =>
    (do
      if ((cimm != 0b00000#5) : Bool)
      then
        (pure (String.append (bitype_mnemonic_forwards op)
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards cimm))
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_signed_13_forwards imm)) ""))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZICBOZ rs1 =>
    (pure (String.append "cbo.zero"
        (String.append (spc_forwards ())
          (String.append "("
            (String.append (opt_spc_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))
  | .FENCEI (0x000, rs1, rd) =>
    (do
      if (((rs1 == zreg) && (rd == zreg)) : Bool)
      then (pure "fence.i")
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZILX_LOAD (mode, rs2, rs1, is_unsigned, width, rd) =>
    (do
      if ((zilx_encoding_valid mode width is_unsigned) : Bool)
      then
        (pure (String.append (zilx_mode_mnemonic_forwards mode)
            (String.append (width_mnemonic_forwards width)
              (String.append (maybe_u_forwards is_unsigned)
                (String.append (spc_forwards ())
                  (String.append (← (reg_name_forwards rd))
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (← (reg_name_forwards rs2))
                          (String.append ")"
                            (String.append (sep_forwards ())
                              (String.append (← (reg_name_forwards rs1)) ""))))))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FCVT_BF16_S (rs1, rm, rd) =>
    (pure (String.append "fcvt.bf16.s"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .FCVT_S_BF16 (rs1, rm, rd) =>
    (pure (String.append "fcvt.s.bf16"
        (String.append (spc_forwards ())
          (String.append (← (freg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .VFNCVTBF16_F_F_W (vm, vs2, vd) =>
    (pure (String.append "vfncvtbf16.f.f.w"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (maybe_vmask_backwards vm) ""))))))))
  | .VFWCVTBF16_F_F_V (vm, vs2, vd) =>
    (pure (String.append "vfwcvtbf16.f.f.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (maybe_vmask_backwards vm) ""))))))))
  | .VFWMACCBF16_VV (vm, vs2, vs1, vd) =>
    (pure (String.append "vfwmaccbf16.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs1)
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VFWMACCBF16_VF (vm, vs2, vs1, vd) =>
    (pure (String.append "vfwmaccbf16.vf"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (← (freg_name_forwards vs1))
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .ZIMOP_MOP_R (mop, rs1, rd) =>
    (pure (String.append "mop.r."
        (String.append (← (dec_bits_5_forwards mop))
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rd))
              (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) "")))))))
  | .ZIMOP_MOP_RR (mop, rs2, rs1, rd) =>
    (pure (String.append "mop.rr."
        (String.append (← (dec_bits_3_forwards mop))
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rd))
              (String.append (sep_forwards ())
                (String.append (← (reg_name_forwards rs1))
                  (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) "")))))))))
  | .ZCMOP mop =>
    (pure (String.append "c.mop."
        (String.append (← (dec_bits_4_forwards ((mop : (BitVec 3)) +++ 1#1))) "")))
  | .ILLEGAL s =>
    (pure (String.append "illegal"
        (String.append (spc_forwards ()) (String.append (← (hex_bits_32_forwards s)) ""))))
  | .C_ILLEGAL s =>
    (pure (String.append "c.illegal"
        (String.append (spc_forwards ()) (String.append (← (hex_bits_16_forwards s)) ""))))
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def assembly_forwards_matches (arg_ : instruction) : Bool :=
  match arg_ with
  | .ZICBOP (cbop, rs1, offset) => true
  | .NTL op => true
  | .C_NTL op => true
  | .PAUSE () => true
  | .LPAD lpl => true
  | .UTYPE (imm, rd, op) => true
  | .JAL (imm, rd) => true
  | .JALR (imm, rs1, rd) => true
  | .BTYPE (imm, rs2, rs1, op) => true
  | .ITYPE (imm, rs1, rd, op) => true
  | .SHIFTIOP (shamt, rs1, rd, op) => true
  | .RTYPE (rs2, rs1, rd, op) => true
  | .LOAD (imm, rs1, rd, is_unsigned, width) => true
  | .STORE (imm, rs2, rs1, width) => true
  | .ADDIW (imm, rs1, rd) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .RTYPEW (rs2, rs1, rd, op) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .SHIFTIWOP (shamt, rs1, rd, op) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .FENCE_TSO () => true
  | .FENCE (0b0000, pred, succ, rs, rd) =>
    (if (((rs == zreg) && (rd == zreg)) : Bool)
    then true
    else false)
  | .ECALL () => true
  | .MRET () => true
  | .SRET () => true
  | .EBREAK () => true
  | .WFI () => true
  | .SFENCE_VMA (rs1, rs2) => true
  | .AMO (op, aq, rl, rs2, rs1, width, rd) => true
  | .LOADRES (aq, rl, rs1, width, rd) => true
  | .STORECON (aq, rl, rs2, rs1, width, rd) => true
  | .MUL (rs2, rs1, rd, mul_op) => true
  | .DIV (rs2, rs1, rd, is_unsigned) => true
  | .REM (rs2, rs1, rd, is_unsigned) => true
  | .MULW (rs2, rs1, rd) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .SLLIUW (shamt, rs1, rd) => true
  | .ZBA_RTYPEUW (rs2, rs1, rd, shamt) => true
  | .ZBA_RTYPE (rs2, rs1, rd, shamt) => true
  | .RORIW (shamt, rs1, rd) => true
  | .RORI (shamt, rs1, rd) => true
  | .ZBB_RTYPEW (rs2, rs1, rd, op) => true
  | .ZBB_RTYPE (rs2, rs1, rd, op) => true
  | .ZBB_EXTOP (rs1, rd, op) => true
  | .REV8 (rs1, rd) => true
  | .ORCB (rs1, rd) => true
  | .CPOP (rs1, rd) => true
  | .CPOPW (rs1, rd) => true
  | .CLZ (rs1, rd) => true
  | .CLZW (rs1, rd) => true
  | .CTZ (rs1, rd) => true
  | .CTZW (rs1, rd) => true
  | .CLMUL (rs2, rs1, rd) => true
  | .CLMULH (rs2, rs1, rd) => true
  | .CLMULR (rs2, rs1, rd) => true
  | .ZBS_IOP (shamt, rs1, rd, op) => true
  | .ZBS_RTYPE (rs2, rs1, rd, op) => true
  | .C_NOP 0b000000 => true
  | .C_NOP imm =>
    (if ((imm != (zeros (n := 6))) : Bool)
    then true
    else false)
  | .C_ADDI4SPN (rdc, nzimm) =>
    (if ((nzimm != 0b00000000#8) : Bool)
    then true
    else false)
  | .C_LW (uimm, rsc, rdc) => true
  | .C_LD (uimm, rsc, rdc) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .C_SW (uimm, rsc1, rsc2) => true
  | .C_SD (uimm, rsc1, rsc2) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .C_ADDI (imm, rsd) =>
    (if ((bne rsd zreg) : Bool)
    then true
    else false)
  | .C_JAL imm => true
  | .C_ADDIW (imm, rsd) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .C_LI (imm, rd) => true
  | .C_ADDI16SP imm =>
    (if ((imm != 0b000000#6) : Bool)
    then true
    else false)
  | .C_LUI (imm, rd) =>
    (if (((bne rd sp) && (imm != 0b000000#6)) : Bool)
    then true
    else false)
  | .C_SRLI (shamt, rsd) => true
  | .C_SRAI (shamt, rsd) => true
  | .C_ANDI (imm, rsd) => true
  | .C_SUB (rsd, rs2) => true
  | .C_XOR (rsd, rs2) => true
  | .C_OR (rsd, rs2) => true
  | .C_AND (rsd, rs2) => true
  | .C_SUBW (rsd, rs2) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .C_ADDW (rsd, rs2) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .C_J imm => true
  | .C_BEQZ (imm, rs) => true
  | .C_BNEZ (imm, rs) => true
  | .C_SLLI (shamt, rsd) => true
  | .C_LWSP (uimm, rd) =>
    (if ((bne rd zreg) : Bool)
    then true
    else false)
  | .C_LDSP (uimm, rd) =>
    (if (((bne rd zreg) && (xlen == 64)) : Bool)
    then true
    else false)
  | .C_SWSP (uimm, rs2) => true
  | .C_SDSP (uimm, rs2) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .C_JR rs1 =>
    (if ((bne rs1 zreg) : Bool)
    then true
    else false)
  | .C_JALR rs1 =>
    (if ((bne rs1 zreg) : Bool)
    then true
    else false)
  | .C_MV (rd, rs2) =>
    (if ((bne rs2 zreg) : Bool)
    then true
    else false)
  | .C_EBREAK () => true
  | .C_ADD (rsd, rs2) =>
    (if ((bne rs2 zreg) : Bool)
    then true
    else false)
  | .C_LBU (uimm, rdc, rsc1) => true
  | .C_LHU (uimm, rdc, rsc1) => true
  | .C_LH (uimm, rdc, rsc1) => true
  | .C_SB (uimm, rsc1, rsc2) => true
  | .C_SH (uimm, rsc1, rsc2) => true
  | .C_ZEXT_B rsdc => true
  | .C_SEXT_B rsdc => true
  | .C_ZEXT_H rsdc => true
  | .C_SEXT_H rsdc => true
  | .C_ZEXT_W rsdc => true
  | .C_NOT rsdc => true
  | .C_MUL (rsdc, rsc2) => true
  | .HLVTYPE (width, op, is_unsigned, rs1, rd) => true
  | .HSV (width, rs1, rs2) => true
  | .HFENCE_VVMA (rs1, rs2) => true
  | .HFENCE_GVMA (rs1, rs2) => true
  | .LOAD_FP (imm, rs1, rd, width) => true
  | .STORE_FP (imm, rs2, rs1, width) => true
  | .F_MADD_TYPE_S (rs3, rs2, rs1, rm, rd, op) => true
  | .F_BIN_RM_TYPE_S (rs2, rs1, rm, rd, op) => true
  | .F_UN_RM_FF_TYPE_S (rs1, rm, rd, .FSQRT_S) => true
  | .F_UN_RM_FX_TYPE_S (rs1, rm, rd, op) => true
  | .F_UN_RM_XF_TYPE_S (rs1, rm, rd, op) => true
  | .F_BIN_TYPE_F_S (rs2, rs1, rd, op) => true
  | .F_BIN_TYPE_X_S (rs2, rs1, rd, op) => true
  | .F_UN_TYPE_X_S (rs1, rd, op) => true
  | .F_UN_TYPE_F_S (rs1, rd, op) => true
  | .C_FLWSP (imm, rd) => true
  | .C_FSWSP (uimm, rs2) => true
  | .C_FLW (uimm, rsc, rdc) => true
  | .C_FSW (uimm, rsc1, rsc2) => true
  | .F_MADD_TYPE_D (rs3, rs2, rs1, rm, rd, op) => true
  | .F_BIN_RM_TYPE_D (rs2, rs1, rm, rd, op) => true
  | .F_UN_RM_FF_TYPE_D (rs1, rm, rd, op) => true
  | .F_UN_RM_FX_TYPE_D (rs1, rm, rd, op) => true
  | .F_UN_RM_XF_TYPE_D (rs1, rm, rd, op) => true
  | .F_BIN_F_TYPE_D (rs2, rs1, rd, op) => true
  | .F_BIN_X_TYPE_D (rs2, rs1, rd, op) => true
  | .F_UN_X_TYPE_D (rs1, rd, op) => true
  | .F_UN_F_TYPE_D (rs1, rd, op) => true
  | .C_FLDSP (uimm, rd) => true
  | .C_FSDSP (uimm, rs2) => true
  | .C_FLD (uimm, rsc, rdc) => true
  | .C_FSD (uimm, rsc1, rsc2) => true
  | .F_BIN_RM_TYPE_H (rs2, rs1, rm, rd, op) => true
  | .F_MADD_TYPE_H (rs3, rs2, rs1, rm, rd, op) => true
  | .F_BIN_F_TYPE_H (rs2, rs1, rd, op) => true
  | .F_BIN_X_TYPE_H (rs2, rs1, rd, op) => true
  | .F_UN_RM_FF_TYPE_H (rs1, rm, rd, op) => true
  | .F_UN_RM_FX_TYPE_H (rs1, rm, rd, op) => true
  | .F_UN_RM_XF_TYPE_H (rs1, rm, rd, op) => true
  | .F_UN_F_TYPE_H (rs1, rd, op) => true
  | .F_UN_X_TYPE_H (rs1, rd, op) => true
  | .FLI_H (constantidx, rd) => true
  | .FLI_S (constantidx, rd) => true
  | .FLI_D (constantidx, rd) => true
  | .FMINM_H (rs2, rs1, rd) => true
  | .FMAXM_H (rs2, rs1, rd) => true
  | .FMINM_S (rs2, rs1, rd) => true
  | .FMAXM_S (rs2, rs1, rd) => true
  | .FMINM_D (rs2, rs1, rd) => true
  | .FMAXM_D (rs2, rs1, rd) => true
  | .FROUND_H (rs1, rm, rd) => true
  | .FROUNDNX_H (rs1, rm, rd) => true
  | .FROUND_S (rs1, rm, rd) => true
  | .FROUNDNX_S (rs1, rm, rd) => true
  | .FROUND_D (rs1, rm, rd) => true
  | .FROUNDNX_D (rs1, rm, rd) => true
  | .FMVH_X_D (rs1, rd) => true
  | .FMVP_D_X (rs2, rs1, rd) => true
  | .FLEQ_H (rs2, rs1, rd) => true
  | .FLTQ_H (rs2, rs1, rd) => true
  | .FLEQ_S (rs2, rs1, rd) => true
  | .FLTQ_S (rs2, rs1, rd) => true
  | .FLEQ_D (rs2, rs1, rd) => true
  | .FLTQ_D (rs2, rs1, rd) => true
  | .FCVTMOD_W_D (rs1, rd) => true
  | .VSETVLI (vtr, ma, ta, sew, lmul, rs1, rd) => true
  | .VSETVL (rs2, rs1, rd) => true
  | .VSETIVLI (vtr, ma, ta, sew, lmul, uimm, rd) => true
  | .VVTYPE (funct6, vm, vs2, vs1, vd) => true
  | .NVSTYPE (funct6, vm, vs2, vs1, vd) => true
  | .NVTYPE (funct6, vm, vs2, vs1, vd) => true
  | .MASKTYPEV (vs2, vs1, vd) => true
  | .MOVETYPEV (vs1, vd) => true
  | .VXTYPE (funct6, vm, vs2, rs1, vd) => true
  | .NXSTYPE (funct6, vm, vs2, rs1, vd) => true
  | .NXTYPE (funct6, vm, vs2, rs1, vd) => true
  | .VXSG (funct6, vm, vs2, rs1, vd) => true
  | .MASKTYPEX (vs2, rs1, vd) => true
  | .MOVETYPEX (rs1, vd) => true
  | .VITYPE (funct6, vm, vs2, simm, vd) => true
  | .NISTYPE (funct6, vm, vs2, uimm, vd) => true
  | .NITYPE (funct6, vm, vs2, uimm, vd) => true
  | .VISG (funct6, vm, vs2, simm, vd) => true
  | .MASKTYPEI (vs2, simm, vd) => true
  | .MOVETYPEI (vd, simm) => true
  | .VMVRTYPE (vs2, nreg, vd) => true
  | .MVVTYPE (funct6, vm, vs2, vs1, vd) => true
  | .MVVMATYPE (funct6, vm, vs2, vs1, vd) => true
  | .WVVTYPE (funct6, vm, vs2, vs1, vd) => true
  | .WVTYPE (funct6, vm, vs2, vs1, vd) => true
  | .WMVVTYPE (funct6, vm, vs2, vs1, vd) => true
  | .VEXTTYPE (funct6, vm, vs2, vd) => true
  | .VMVXS (vs2, rd) => true
  | .MVVCOMPRESS (vs2, vs1, vd) => true
  | .MVXTYPE (funct6, vm, vs2, rs1, vd) => true
  | .MVXMATYPE (funct6, vm, vs2, rs1, vd) => true
  | .WVXTYPE (funct6, vm, vs2, rs1, vd) => true
  | .WXTYPE (funct6, vm, vs2, rs1, vd) => true
  | .WMVXTYPE (funct6, vm, vs2, rs1, vd) => true
  | .VMVSX (rs1, vd) => true
  | .FVVTYPE (funct6, vm, vs2, vs1, vd) => true
  | .FVVMATYPE (funct6, vm, vs2, vs1, vd) => true
  | .FWVVTYPE (funct6, vm, vs2, vs1, vd) => true
  | .FWVVMATYPE (funct6, vm, vs1, vs2, vd) => true
  | .FWVTYPE (funct6, vm, vs2, vs1, vd) => true
  | .VFUNARY0 (vm, vs2, vfunary0, vd) => true
  | .VFWUNARY0 (vm, vs2, vfwunary0, vd) => true
  | .VFNUNARY0 (vm, vs2, vfnunary0, vd) => true
  | .VFUNARY1 (vm, vs2, vfunary1, vd) => true
  | .VFMVFS (vs2, rd) => true
  | .FVFTYPE (funct6, vm, vs2, rs1, vd) => true
  | .FVFMATYPE (funct6, vm, vs2, rs1, vd) => true
  | .FWVFTYPE (funct6, vm, vs2, rs1, vd) => true
  | .FWVFMATYPE (funct6, vm, rs1, vs2, vd) => true
  | .FWFTYPE (funct6, vm, vs2, rs1, vd) => true
  | .VFMERGE (vs2, rs1, vd) => true
  | .VFMV (rs1, vd) => true
  | .VFMVSF (rs1, vd) => true
  | .VLSEGTYPE (nf, vm, rs1, width, vd) => true
  | .VLSEGFFTYPE (nf, vm, rs1, width, vd) => true
  | .VSSEGTYPE (nf, vm, rs1, width, vs3) => true
  | .VLSSEGTYPE (nf, vm, rs2, rs1, width, vd) => true
  | .VSSSEGTYPE (nf, vm, rs2, rs1, width, vs3) => true
  | .VLXSEGTYPE (nf, vm, vs2, rs1, width, vd, mop) => true
  | .VSXSEGTYPE (nf, vm, vs2, rs1, width, vs3, mop) => true
  | .VLRETYPE (nf, rs1, width, vd) => true
  | .VSRETYPE (nf, rs1, vs3) => true
  | .VMTYPE (rs1, vd_or_vs3, op) => true
  | .MMTYPE (funct6, vs2, vs1, vd) => true
  | .VCPOP_M (vm, vs2, rd) => true
  | .VFIRST_M (vm, vs2, rd) => true
  | .VMSBF_M (vm, vs2, vd) => true
  | .VMSIF_M (vm, vs2, vd) => true
  | .VMSOF_M (vm, vs2, vd) => true
  | .VIOTA_M (vm, vs2, vd) => true
  | .VID_V (vm, vd) => true
  | .VVMTYPE (funct6, vs2, vs1, vd) => true
  | .VVMCTYPE (funct6, vs2, vs1, vd) => true
  | .VVMSTYPE (funct6, vs2, vs1, vd) => true
  | .VVCMPTYPE (funct6, vm, vs2, vs1, vd) => true
  | .VXMTYPE (funct6, vs2, rs1, vd) => true
  | .VXMCTYPE (funct6, vs2, rs1, vd) => true
  | .VXMSTYPE (funct6, vs2, rs1, vd) => true
  | .VXCMPTYPE (funct6, vm, vs2, rs1, vd) => true
  | .VIMTYPE (funct6, vs2, simm, vd) => true
  | .VIMCTYPE (funct6, vs2, simm, vd) => true
  | .VIMSTYPE (funct6, vs2, simm, vd) => true
  | .VICMPTYPE (funct6, vm, vs2, simm, vd) => true
  | .FVVMTYPE (funct6, vm, vs2, vs1, vd) => true
  | .FVFMTYPE (funct6, vm, vs2, rs1, vd) => true
  | .RIVVTYPE (funct6, vm, vs2, vs1, vd) => true
  | .RMVVTYPE (funct6, vm, vs2, vs1, vd) => true
  | .RFVVTYPE (funct6, vm, vs2, vs1, vd) => true
  | .RFWVVTYPE (funct6, vm, vs2, vs1, vd) => true
  | .SHA256SIG0 (rs1, rd) => true
  | .SHA256SIG1 (rs1, rd) => true
  | .SHA256SUM0 (rs1, rd) => true
  | .SHA256SUM1 (rs1, rd) => true
  | .AES32ESMI (bs, rs2, rs1, rd) => true
  | .AES32ESI (bs, rs2, rs1, rd) => true
  | .AES32DSMI (bs, rs2, rs1, rd) => true
  | .AES32DSI (bs, rs2, rs1, rd) => true
  | .SHA512SIG0L (rs2, rs1, rd) => true
  | .SHA512SIG0H (rs2, rs1, rd) => true
  | .SHA512SIG1L (rs2, rs1, rd) => true
  | .SHA512SIG1H (rs2, rs1, rd) => true
  | .SHA512SUM0R (rs2, rs1, rd) => true
  | .SHA512SUM1R (rs2, rs1, rd) => true
  | .AES64KS1I (rnum, rs1, rd) => true
  | .AES64KS2 (rs2, rs1, rd) => true
  | .AES64IM (rs1, rd) => true
  | .AES64ESM (rs2, rs1, rd) => true
  | .AES64ES (rs2, rs1, rd) => true
  | .AES64DSM (rs2, rs1, rd) => true
  | .AES64DS (rs2, rs1, rd) => true
  | .SHA512SIG0 (rs1, rd) => true
  | .SHA512SIG1 (rs1, rd) => true
  | .SHA512SUM0 (rs1, rd) => true
  | .SHA512SUM1 (rs1, rd) => true
  | .SM3P0 (rs1, rd) => true
  | .SM3P1 (rs1, rd) => true
  | .SM4ED (bs, rs2, rs1, rd) => true
  | .SM4KS (bs, rs2, rs1, rd) => true
  | .ZBKB_RTYPE (rs2, rs1, rd, op) => true
  | .ZBKB_PACKW (rs2, rs1, rd) => true
  | .ZIP (rs1, rd) => true
  | .UNZIP (rs1, rd) => true
  | .BREV8 (rs1, rd) => true
  | .XPERM8 (rs2, rs1, rd) => true
  | .XPERM4 (rs2, rs1, rd) => true
  | .VANDN_VV (vm, vs1, vs2, vd) => true
  | .VANDN_VX (vm, vs2, rs1, vd) => true
  | .VBREV_V (vm, vs2, vd) => true
  | .VBREV8_V (vm, vs2, vd) => true
  | .VREV8_V (vm, vs2, vd) => true
  | .VCLZ_V (vm, vs2, vd) => true
  | .VCTZ_V (vm, vs2, vd) => true
  | .VCPOP_V (vm, vs2, vd) => true
  | .VROL_VV (vm, vs1, vs2, vd) => true
  | .VROL_VX (vm, vs2, rs1, vd) => true
  | .VROR_VV (vm, vs1, vs2, vd) => true
  | .VROR_VX (vm, vs2, rs1, vd) => true
  | .VROR_VI (vm, vs2, uimm, vd) => true
  | .VWSLL_VV (vm, vs2, vs1, vd) => true
  | .VWSLL_VX (vm, vs2, rs1, vd) => true
  | .VWSLL_VI (vm, vs2, uimm, vd) => true
  | .VCLMUL_VV (vm, vs2, vs1, vd) => true
  | .VCLMUL_VX (vm, vs2, rs1, vd) => true
  | .VCLMULH_VV (vm, vs2, vs1, vd) => true
  | .VCLMULH_VX (vm, vs2, rs1, vd) => true
  | .VGHSH_VV (vs2, vs1, vd) => true
  | .VGMUL_VV (vs2, vd) => true
  | .VAESDF (funct6, vs2, vd) => true
  | .VAESDM (funct6, vs2, vd) => true
  | .VAESEF (funct6, vs2, vd) => true
  | .VAESEM (funct6, vs2, vd) => true
  | .VAESKF1_VI (vs2, rnd, vd) => true
  | .VAESKF2_VI (vs2, rnd, vd) => true
  | .VAESZ_VS (vs2, vd) => true
  | .VSM4K_VI (vs2, uimm, vd) => true
  | .ZVKSM4RTYPE (funct6, vs2, vd) => true
  | .VSHA2MS_VV (vs2, vs1, vd) => true
  | .ZVKSHA2TYPE (funct6, vs2, vs1, vd) => true
  | .VSM3ME_VV (vs2, vs1, vd) => true
  | .VSM3C_VI (vs2, uimm, vd) => true
  | .ZVABD_VV (funct6, vm, vs2, vs1, vd) => true
  | .ZVABD_VX (.VABD, vm, vs2, rs1, vd) =>
    (if ((rs1 == zreg) : Bool)
    then true
    else
      (match (ZVABD_VX (VABD, vm, vs2, rs1, vd)) with
      | .ZVABD_VX (funct6, vm, vs2, rs1, vd) => true
      | _ => false))
  | .ZVABD_VX (funct6, vm, vs2, rs1, vd) => true
  | .ZVWABDA_VV (funct6, vm, vs2, vs1, vd) => true
  | .ZVWABDA_VX (funct6, vm, vs2, rs1, vd) => true
  | .CSRImm (csr, imm, rd, op) => true
  | .CSRReg (csr, rs1, rd, op) => true
  | .SINVAL_VMA (rs1, rs2) => true
  | .SFENCE_W_INVAL () => true
  | .SFENCE_INVAL_IR () => true
  | .HINVAL_VVMA (rs1, rs2) => true
  | .HINVAL_GVMA (rs1, rs2) => true
  | .WRS .WRS_STO => true
  | .WRS .WRS_NTO => true
  | .SSPUSH rs2 => true
  | .C_SSPUSH () => true
  | .SSPOPCHK rs1 => true
  | .C_SSPOPCHK () => true
  | .SSRDP rd => true
  | .SSAMOSWAP (aq, rl, rs2, rs1, width, rd) =>
    (if (((width == 4) || (width == 8)) : Bool)
    then true
    else false)
  | .ZICOND_RTYPE (rs2, rs1, rd, op) => true
  | .ZICBOM (cbop, rs1) => true
  | .BITYPE (imm, 0b00000, rs1, op) => true
  | .BITYPE (imm, cimm, rs1, op) =>
    (if ((cimm != 0b00000#5) : Bool)
    then true
    else false)
  | .ZICBOZ rs1 => true
  | .FENCEI (0x000, rs1, rd) =>
    (if (((rs1 == zreg) && (rd == zreg)) : Bool)
    then true
    else false)
  | .ZILX_LOAD (mode, rs2, rs1, is_unsigned, width, rd) =>
    (if ((zilx_encoding_valid mode width is_unsigned) : Bool)
    then true
    else false)
  | .FCVT_BF16_S (rs1, rm, rd) => true
  | .FCVT_S_BF16 (rs1, rm, rd) => true
  | .VFNCVTBF16_F_F_W (vm, vs2, vd) => true
  | .VFWCVTBF16_F_F_V (vm, vs2, vd) => true
  | .VFWMACCBF16_VV (vm, vs2, vs1, vd) => true
  | .VFWMACCBF16_VF (vm, vs2, vs1, vd) => true
  | .ZIMOP_MOP_R (mop, rs1, rd) => true
  | .ZIMOP_MOP_RR (mop, rs2, rs1, rd) => true
  | .ZCMOP mop => true
  | .ILLEGAL s => true
  | .C_ILLEGAL s => true
  | _ => false

def undefined_Privilege (_ : Unit) : SailM Privilege := do
  (internal_pick [User, VirtualUser, Supervisor, VirtualSupervisor, Machine])

def Mk_MEnvcfg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MEnvcfg_ADUE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _get_MEnvcfg_CBCFE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_MEnvcfg_CBIE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_MEnvcfg_CBZE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_MEnvcfg_DTE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _get_MEnvcfg_FIOM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

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

def _update_MEnvcfg_ADUE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_MEnvcfg_CBCFE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_MEnvcfg_CBIE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_MEnvcfg_CBZE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_MEnvcfg_DTE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_MEnvcfg_FIOM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_MEnvcfg_LPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_MEnvcfg_PBMTE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_MEnvcfg_PMM (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _update_MEnvcfg_SSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_MEnvcfg_STCE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def xenvcfg_cbie_reserved_behavior : XenvcfgCbieReservedBehavior := Xenvcfg_ClearPermissions

def legalize_xenvcfg_cbie (old_cbie : (BitVec 2)) (new_cbie : (BitVec 2)) : SailM (BitVec 2) := do
  if ((new_cbie != 0b10#2) : Bool)
  then (pure new_cbie)
  else
    (do
      match xenvcfg_cbie_reserved_behavior with
      | .Xenvcfg_Fatal => (reserved_behavior "xenvcfg.CBIE = 0b10")
      | .Xenvcfg_ClearPermissions => (pure 0b00#2)
      | .Xenvcfg_Ignore => (pure old_cbie))

def sys_enable_writable_fiom : Bool := true

def Mk_Misa (v : (BitVec 32)) : (BitVec 32) :=
  v

def _update_Misa_MXL (v : (BitVec 32)) (x : (BitVec (32 - 1 - (32 - 2) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) (32 -i 2) x)

def architecture_bits_forwards (arg_ : Architecture) : (BitVec 2) :=
  match arg_ with
  | .RV32 => 0b01#2
  | .RV64 => 0b10#2
  | .RV128 => 0b11#2

def Mk_Mstatus (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_Mstatus_SXL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 34 x)

def _update_Mstatus_UXL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _get_Misa_A (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_Misa_B (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

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

def Mk_Seccfg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Seccfg_MLPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_Seccfg_PMM (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _get_Seccfg_SSEED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_Seccfg_USEED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_Seccfg_MLPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_Seccfg_PMM (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _update_Seccfg_SSEED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_Seccfg_USEED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_HEnvcfg_LPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_SEnvcfg_LPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def Mk_HEnvcfg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HEnvcfg_ADUE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _get_HEnvcfg_CBCFE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_HEnvcfg_CBIE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_HEnvcfg_CBZE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_HEnvcfg_DTE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _get_HEnvcfg_FIOM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

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

def _update_HEnvcfg_CBCFE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_HEnvcfg_CBIE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_HEnvcfg_CBZE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_HEnvcfg_DTE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_HEnvcfg_FIOM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_HEnvcfg_LPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_HEnvcfg_PBMTE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_HEnvcfg_PMM (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _update_HEnvcfg_SSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_HEnvcfg_STCE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def Mk_SEnvcfg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_SEnvcfg_CBCFE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SEnvcfg_CBIE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_SEnvcfg_CBZE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SEnvcfg_FIOM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_SEnvcfg_PMM (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _get_SEnvcfg_SSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_SEnvcfg_UKTE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_SEnvcfg_CBCFE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SEnvcfg_CBIE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_SEnvcfg_CBZE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SEnvcfg_FIOM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SEnvcfg_LPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_SEnvcfg_PMM (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _update_SEnvcfg_SSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_SEnvcfg_UKTE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def privLevel_is_virtual (p : Privilege) : Bool :=
  ((p == VirtualSupervisor) || (p == VirtualUser))

def inVirtualPrivilege (_ : Unit) : SailM Bool := do
  (pure (privLevel_is_virtual (← readReg cur_privilege)))

def Mk_Hstateen0 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Hstateen1 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Hstateen2 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Hstateen3 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Mstateen0 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Mstateen1 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Mstateen2 (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_Mstateen3 (v : (BitVec 64)) : (BitVec 64) :=
  v

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

def Mk_Sstateen0 (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_Sstateen1 (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_Sstateen2 (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_Sstateen3 (v : (BitVec 32)) : (BitVec 32) :=
  v

def stateen_bit_index_forwards (arg_ : stateen_bit) : Nat :=
  match arg_ with
  | .STATEEN_SE => 63
  | .STATEEN_ENVCFG => 62
  | .STATEEN_CONTEXT => 57
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
  | .Ext_Sdtrig => (pure (hartSupports Ext_Sdtrig))
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
  | .Ext_Zicbop => (pure (hartSupports Ext_Zicbop))
  | .Ext_Zihintntl => (pure (hartSupports Ext_Zihintntl))
  | .Ext_Zihintpause => (pure (hartSupports Ext_Zihintpause))
  | .Ext_C => (pure ((hartSupports Ext_C) && ((_get_Misa_C (← readReg misa)) == 1#1)))
  | .Ext_Zca =>
    (pure ((hartSupports Ext_Zca) && ((← (currentlyEnabled Ext_C)) || (not (hartSupports Ext_C)))))
  | .Ext_A => (pure ((hartSupports Ext_A) && ((_get_Misa_A (← readReg misa)) == 1#1)))
  | .Ext_Zaamo => (pure ((hartSupports Ext_Zaamo) || (← (currentlyEnabled Ext_A))))
  | .Ext_Zabha => (pure ((hartSupports Ext_Zabha) && (← (currentlyEnabled Ext_Zaamo))))
  | .Ext_Zacas => (pure ((hartSupports Ext_Zacas) && (← (currentlyEnabled Ext_Zaamo))))
  | .Ext_Ziccamoa => (pure (hartSupports Ext_Ziccamoa))
  | .Ext_Ziccamoc => (pure (hartSupports Ext_Ziccamoc))
  | .Ext_Zalrsc => (pure ((hartSupports Ext_Zalrsc) || (← (currentlyEnabled Ext_A))))
  | .Ext_Za64rs => (pure ((hartSupports Ext_Za64rs) && (← (currentlyEnabled Ext_Zalrsc))))
  | .Ext_Za128rs => (pure ((hartSupports Ext_Za128rs) && (← (currentlyEnabled Ext_Zalrsc))))
  | .Ext_Ziccrse => (pure (hartSupports Ext_Ziccrse))
  | .Ext_M => (pure ((hartSupports Ext_M) && ((_get_Misa_M (← readReg misa)) == 1#1)))
  | .Ext_Zmmul => (pure ((hartSupports Ext_Zmmul) || (← (currentlyEnabled Ext_M))))
  | .Ext_B => (pure ((hartSupports Ext_B) && ((_get_Misa_B (← readReg misa)) == 1#1)))
  | .Ext_Zba => (pure ((hartSupports Ext_Zba) || (← (currentlyEnabled Ext_B))))
  | .Ext_Zbb => (pure ((hartSupports Ext_Zbb) || (← (currentlyEnabled Ext_B))))
  | .Ext_Zbkb => (pure (hartSupports Ext_Zbkb))
  | .Ext_Zbc => (pure (hartSupports Ext_Zbc))
  | .Ext_Zbkc => (pure (hartSupports Ext_Zbkc))
  | .Ext_Zbs => (pure ((hartSupports Ext_Zbs) || (← (currentlyEnabled Ext_B))))
  | .Ext_Zcb => (pure ((hartSupports Ext_Zcb) && (← (currentlyEnabled Ext_Zca))))
  | .Ext_Zfh => (pure ((hartSupports Ext_Zfh) && (← (currentlyEnabled Ext_F))))
  | .Ext_Zfhmin =>
    (pure (((hartSupports Ext_Zfhmin) && (← (currentlyEnabled Ext_F))) || (← (currentlyEnabled
            Ext_Zfh))))
  | .Ext_Zcf =>
    (pure ((hartSupports Ext_Zcf) && ((← (currentlyEnabled Ext_F)) && ((← (currentlyEnabled
                Ext_Zca)) && ((← (currentlyEnabled Ext_C)) || (not (hartSupports Ext_C)))))))
  | .Ext_Zdinx => (pure ((hartSupports Ext_Zdinx) && (← (currentlyEnabled Ext_Zfinx))))
  | .Ext_Zcd =>
    (pure ((hartSupports Ext_Zcd) && ((← (currentlyEnabled Ext_D)) && ((← (currentlyEnabled
                Ext_Zca)) && ((← (currentlyEnabled Ext_C)) || (not (hartSupports Ext_C)))))))
  | .Ext_Zhinx => (pure ((hartSupports Ext_Zhinx) && (← (currentlyEnabled Ext_Zfinx))))
  | .Ext_Zhinxmin =>
    (pure (((hartSupports Ext_Zhinxmin) && (← (currentlyEnabled Ext_Zfinx))) || (← (currentlyEnabled
            Ext_Zhinx))))
  | .Ext_Zfa => (pure ((hartSupports Ext_Zfa) && (← (currentlyEnabled Ext_F))))
  | .Ext_Zknh => (pure (hartSupports Ext_Zknh))
  | .Ext_Zkne => (pure (hartSupports Ext_Zkne))
  | .Ext_Zknd => (pure (hartSupports Ext_Zknd))
  | .Ext_Zksh => (pure (hartSupports Ext_Zksh))
  | .Ext_Zksed => (pure (hartSupports Ext_Zksed))
  | .Ext_Zkr => (pure (hartSupports Ext_Zkr))
  | .Ext_Zbkx => (pure (hartSupports Ext_Zbkx))
  | .Ext_Zvbb => (pure ((hartSupports Ext_Zvbb) && (← (currentlyEnabled Ext_Zve32x))))
  | .Ext_Zvkb =>
    (pure (((hartSupports Ext_Zvkb) && (← (currentlyEnabled Ext_Zve32x))) || (← (currentlyEnabled
            Ext_Zvbb))))
  | .Ext_Zvbc => (pure ((hartSupports Ext_Zvbc) && (← (currentlyEnabled Ext_Zve64x))))
  | .Ext_Zvkg => (pure ((hartSupports Ext_Zvkg) && (← (currentlyEnabled Ext_Zve32x))))
  | .Ext_Zvkned => (pure ((hartSupports Ext_Zvkned) && (← (currentlyEnabled Ext_Zve32x))))
  | .Ext_Zvksed => (pure ((hartSupports Ext_Zvksed) && (← (currentlyEnabled Ext_Zve32x))))
  | .Ext_Zvknha => (pure ((hartSupports Ext_Zvknha) && (← (currentlyEnabled Ext_Zve32x))))
  | .Ext_Zvknhb => (pure ((hartSupports Ext_Zvknhb) && (← (currentlyEnabled Ext_Zve64x))))
  | .Ext_Zvksh => (pure ((hartSupports Ext_Zvksh) && (← (currentlyEnabled Ext_Zve32x))))
  | .Ext_Zvabd => (pure ((hartSupports Ext_Zvabd) && (← (currentlyEnabled Ext_Zve32x))))
  | .Ext_Zicsr => (pure (hartSupports Ext_Zicsr))
  | .Ext_Svinval => (pure (hartSupports Ext_Svinval))
  | .Ext_Zihpm => (pure ((hartSupports Ext_Zihpm) && (← (currentlyEnabled Ext_Zicsr))))
  | .Ext_Sscofpmf => (pure ((hartSupports Ext_Sscofpmf) && (← (currentlyEnabled Ext_Zihpm))))
  | .Ext_Zawrs => (pure (hartSupports Ext_Zawrs))
  | .Ext_Zicfiss =>
    (pure ((hartSupports Ext_Zicfiss) && ((← (currentlyEnabled Ext_Zicsr)) && ((← (currentlyEnabled
                Ext_Zimop)) && (← (currentlyEnabled Ext_Zaamo))))))
  | .Ext_Zicond => (pure (hartSupports Ext_Zicond))
  | .Ext_Zicntr => (pure ((hartSupports Ext_Zicntr) && (← (currentlyEnabled Ext_Zicsr))))
  | .Ext_Zicbom => (pure (hartSupports Ext_Zicbom))
  | .Ext_Zibi => (pure (hartSupports Ext_Zibi))
  | .Ext_Zicboz => (pure (hartSupports Ext_Zicboz))
  | .Ext_Zifencei => (pure (hartSupports Ext_Zifencei))
  | .Ext_Zilx => (pure (hartSupports Ext_Zilx))
  | .Ext_Ssqosid => (pure ((hartSupports Ext_Ssqosid) && (← (currentlyEnabled Ext_Zicsr))))
  | .Ext_Zfbfmin => (pure ((hartSupports Ext_Zfbfmin) && (← (currentlyEnabled Ext_F))))
  | .Ext_Zvfbfmin => (pure ((hartSupports Ext_Zvfbfmin) && (← (currentlyEnabled Ext_Zve32f))))
  | .Ext_Zvfbfwma =>
    (pure ((hartSupports Ext_Zvfbfwma) && ((← (currentlyEnabled Ext_Zvfbfmin)) && (← (currentlyEnabled
              Ext_Zfbfmin)))))
  | .Ext_Zimop => (pure (hartSupports Ext_Zimop))
  | .Ext_Zcmop => (pure ((hartSupports Ext_Zcmop) && (← (currentlyEnabled Ext_Zca))))
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

def legalize_henvcfg (h : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_HEnvcfg v)
  (pure (_update_HEnvcfg_FIOM
      (_update_HEnvcfg_LPE
        (_update_HEnvcfg_SSE
          (_update_HEnvcfg_CBIE
            (_update_HEnvcfg_CBCFE
              (_update_HEnvcfg_CBZE
                (_update_HEnvcfg_PMM
                  (_update_HEnvcfg_DTE
                    (_update_HEnvcfg_ADUE
                      (_update_HEnvcfg_PBMTE
                        (_update_HEnvcfg_STCE h
                          (← do
                            if (((← (currentlyEnabled Ext_Sstc)) && ((_get_MEnvcfg_STCE
                                     (← readReg menvcfg)) == 1#1)) : Bool)
                            then (pure (_get_HEnvcfg_STCE v))
                            else (pure 0#1)))
                        (← do
                          if (((← (currentlyEnabled Ext_Svpbmt)) && ((_get_MEnvcfg_PBMTE
                                   (← readReg menvcfg)) == 1#1)) : Bool)
                          then (pure (_get_HEnvcfg_PBMTE v))
                          else (pure 0#1)))
                      (← do
                        if (((← (currentlyEnabled Ext_Svadu)) && ((_get_MEnvcfg_ADUE
                                 (← readReg menvcfg)) == 1#1)) : Bool)
                        then (pure (_get_HEnvcfg_ADUE v))
                        else (pure 0#1)))
                    (← do
                      if ((← (currentlyEnabled Ext_Ssdbltrp)) : Bool)
                      then (pure (_get_HEnvcfg_DTE v))
                      else (pure 0#1)))
                  (← do
                    if (((← (currentlyEnabled Ext_Ssnpm)) && (is_supported_pmm PM_SSNPM
                           (pmm_mode_backwards (_get_HEnvcfg_PMM v)))) : Bool)
                    then (pure (_get_HEnvcfg_PMM v))
                    else (pure (_get_HEnvcfg_PMM h))))
                (← do
                  if ((← (currentlyEnabled Ext_Zicboz)) : Bool)
                  then (pure (_get_HEnvcfg_CBZE v))
                  else (pure 0#1)))
              (← do
                if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
                then (pure (_get_HEnvcfg_CBCFE v))
                else (pure 0#1)))
            (← do
              if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
              then (legalize_xenvcfg_cbie (_get_HEnvcfg_CBIE h) (_get_HEnvcfg_CBIE v))
              else (pure 0b00#2)))
          (← do
            if (((← (currentlyEnabled Ext_Zicfiss)) && ((_get_MEnvcfg_SSE (← readReg menvcfg)) == 1#1)) : Bool)
            then (pure (_get_HEnvcfg_SSE v))
            else (pure 0#1)))
        (if ((hartSupports Ext_Zicfilp) : Bool)
        then (_get_HEnvcfg_LPE v)
        else 0#1))
      (if (sys_enable_writable_fiom : Bool)
      then (_get_HEnvcfg_FIOM v)
      else 0#1)))

def legalize_menvcfg (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_MEnvcfg v)
  (pure (_update_MEnvcfg_PBMTE
      (_update_MEnvcfg_ADUE
        (_update_MEnvcfg_DTE
          (_update_MEnvcfg_PMM
            (_update_MEnvcfg_STCE
              (_update_MEnvcfg_CBIE
                (_update_MEnvcfg_CBCFE
                  (_update_MEnvcfg_CBZE
                    (_update_MEnvcfg_SSE
                      (_update_MEnvcfg_LPE
                        (_update_MEnvcfg_FIOM o
                          (if (sys_enable_writable_fiom : Bool)
                          then (_get_MEnvcfg_FIOM v)
                          else 0#1))
                        (if ((hartSupports Ext_Zicfilp) : Bool)
                        then (_get_MEnvcfg_LPE v)
                        else 0#1))
                      (if ((hartSupports Ext_Zicfiss) : Bool)
                      then (_get_MEnvcfg_SSE v)
                      else 0#1))
                    (← do
                      if ((← (currentlyEnabled Ext_Zicboz)) : Bool)
                      then (pure (_get_MEnvcfg_CBZE v))
                      else (pure 0#1)))
                  (← do
                    if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
                    then (pure (_get_MEnvcfg_CBCFE v))
                    else (pure 0#1)))
                (← do
                  if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
                  then (legalize_xenvcfg_cbie (_get_MEnvcfg_CBIE o) (_get_MEnvcfg_CBIE v))
                  else (pure 0b00#2)))
              (← do
                if ((← (currentlyEnabled Ext_Sstc)) : Bool)
                then (pure (_get_MEnvcfg_STCE v))
                else (pure 0#1)))
            (← do
              if (((← (currentlyEnabled Ext_Smnpm)) && (is_supported_pmm PM_SMNPM
                     (pmm_mode_backwards (_get_MEnvcfg_PMM v)))) : Bool)
              then (pure (_get_MEnvcfg_PMM v))
              else (pure (_get_MEnvcfg_PMM o))))
          (if ((hartSupports Ext_Ssdbltrp) : Bool)
          then (_get_MEnvcfg_DTE v)
          else 0#1))
        (← do
          if ((← (currentlyEnabled Ext_Svadu)) : Bool)
          then (pure (_get_MEnvcfg_ADUE v))
          else (pure 0#1)))
      (← do
        if ((← (currentlyEnabled Ext_Svpbmt)) : Bool)
        then (pure (_get_MEnvcfg_PBMTE v))
        else (pure 0#1))))

def legalize_mseccfg (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let sseed_read_only_zero ← do
    (pure ((false : Bool) || ((not (← (currentlyEnabled Ext_S))) || (not
            (← (currentlyEnabled Ext_Zkr))))))
  let useed_read_only_zero ← do
    (pure ((false : Bool) || ((not (← (currentlyEnabled Ext_U))) || (not
            (← (currentlyEnabled Ext_Zkr))))))
  let v := (Mk_Seccfg v)
  (pure (_update_Seccfg_USEED
      (_update_Seccfg_SSEED
        (_update_Seccfg_MLPE
          (_update_Seccfg_PMM o
            (← do
              if (((← (currentlyEnabled Ext_Smmpm)) && (is_supported_pmm PM_SMMPM
                     (pmm_mode_backwards (_get_Seccfg_PMM v)))) : Bool)
              then (pure (_get_Seccfg_PMM v))
              else (pure (_get_Seccfg_PMM o))))
          (if ((hartSupports Ext_Zicfilp) : Bool)
          then (_get_Seccfg_MLPE v)
          else 0#1))
        (if (sseed_read_only_zero : Bool)
        then 0#1
        else (_get_Seccfg_SSEED v)))
      (if (useed_read_only_zero : Bool)
      then 0#1
      else (_get_Seccfg_USEED v))))

def legalize_senvcfg (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_SEnvcfg v)
  (pure (_update_SEnvcfg_UKTE
      (_update_SEnvcfg_PMM
        (_update_SEnvcfg_CBIE
          (_update_SEnvcfg_CBCFE
            (_update_SEnvcfg_CBZE
              (_update_SEnvcfg_SSE
                (_update_SEnvcfg_LPE
                  (_update_SEnvcfg_FIOM o
                    (if (sys_enable_writable_fiom : Bool)
                    then (_get_SEnvcfg_FIOM v)
                    else 0#1))
                  (if ((hartSupports Ext_Zicfilp) : Bool)
                  then (_get_SEnvcfg_LPE v)
                  else 0#1))
                (if ((hartSupports Ext_Zicfiss) : Bool)
                then (_get_SEnvcfg_SSE v)
                else 0#1))
              (← do
                if ((← (currentlyEnabled Ext_Zicboz)) : Bool)
                then (pure (_get_SEnvcfg_CBZE v))
                else (pure 0#1)))
            (← do
              if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
              then (pure (_get_SEnvcfg_CBCFE v))
              else (pure 0#1)))
          (← do
            if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
            then (legalize_xenvcfg_cbie (_get_SEnvcfg_CBIE o) (_get_SEnvcfg_CBIE v))
            else (pure 0b00#2)))
        (← do
          if (((← (currentlyEnabled Ext_Ssnpm)) && (is_supported_pmm PM_SSNPM
                 (pmm_mode_backwards (_get_SEnvcfg_PMM v)))) : Bool)
          then (pure (_get_SEnvcfg_PMM v))
          else (pure (_get_SEnvcfg_PMM o))))
      (← do
        if ((← (currentlyEnabled Ext_Svukte)) : Bool)
        then (pure (_get_SEnvcfg_UKTE v))
        else (pure 0#1))))

def amocas_odd_register_reserved_behavior : AmocasOddRegisterReservedBehavior := AMOCAS_Illegal

/-- Type quantifiers: width : Nat, List.elem width [1, 2, 4, 8, 16] -/
def amo_encoding_valid (width : Nat) (op : amoop) (typ_2 : regidx) (typ_3 : regidx) : SailM Bool := do
  let .Regidx rs2 : regidx := typ_2
  let .Regidx rd : regidx := typ_3
  (pure ((← do
        if ((op == AMOCAS) : Bool)
        then (currentlyEnabled Ext_Zacas)
        else (currentlyEnabled Ext_Zaamo)) && (← do
        if ((width <b 4) : Bool)
        then (currentlyEnabled Ext_Zabha)
        else
          (pure ((width ≤b xlen_bytes) || (((op == AMOCAS) && (width ≤b (xlen_bytes *i 2))) && (← do
                  if ((((BitVec.access rs2 0) == 1#1) || ((BitVec.access rd 0) == 1#1)) : Bool)
                  then
                    (do
                      match amocas_odd_register_reserved_behavior with
                      | .AMOCAS_Fatal =>
                        (reserved_behavior
                          (HAppend.hAppend "AMOCAS.D/Q used an odd-numbered register (rs2 = "
                            (HAppend.hAppend (Int.repr (BitVec.toNatInt rs2))
                              (HAppend.hAppend ", rd = "
                                (HAppend.hAppend (Int.repr (BitVec.toNatInt rd)) ").")))))
                      | .AMOCAS_Illegal => (pure false))
                  else (pure true))))))))

def encdec_amoop_forwards (arg_ : amoop) : (BitVec 5) :=
  match arg_ with
  | .AMOSWAP => 0b00001#5
  | .AMOADD => 0b00000#5
  | .AMOXOR => 0b00100#5
  | .AMOAND => 0b01100#5
  | .AMOOR => 0b01000#5
  | .AMOMIN => 0b10000#5
  | .AMOMAX => 0b10100#5
  | .AMOMINU => 0b11000#5
  | .AMOMAXU => 0b11100#5
  | .AMOCAS => 0b00101#5

def encdec_biop_forwards (arg_ : biop) : (BitVec 3) :=
  match arg_ with
  | .BEQI => 0b010#3
  | .BNEI => 0b011#3

def encdec_bop_forwards (arg_ : bop) : (BitVec 3) :=
  match arg_ with
  | .BEQ => 0b000#3
  | .BNE => 0b001#3
  | .BLT => 0b100#3
  | .BGE => 0b101#3
  | .BLTU => 0b110#3
  | .BGEU => 0b111#3

def encdec_cbop_forwards (arg_ : cbop_zicbom) : (BitVec 12) :=
  match arg_ with
  | .CBO_CLEAN => 0b000000000001#12
  | .CBO_FLUSH => 0b000000000010#12
  | .CBO_INVAL => 0b000000000000#12

def encdec_cbop_zicbop_forwards (arg_ : cbop_zicbop) : (BitVec 5) :=
  match arg_ with
  | .PREFETCH_I => 0b00000#5
  | .PREFETCH_R => 0b00001#5
  | .PREFETCH_W => 0b00011#5

def encdec_csrop_forwards (arg_ : csrop) : (BitVec 2) :=
  match arg_ with
  | .CSRRW => 0b01#2
  | .CSRRS => 0b10#2
  | .CSRRC => 0b11#2

def encdec_freg_forwards (arg_ : fregidx) : (BitVec 5) :=
  match arg_ with
  | .Fregidx r => r

def encdec_fvffunct6_forwards (arg_ : fvffunct6) : (BitVec 6) :=
  match arg_ with
  | .VF_VADD => 0b000000#6
  | .VF_VSUB => 0b000010#6
  | .VF_VMIN => 0b000100#6
  | .VF_VMAX => 0b000110#6
  | .VF_VSGNJ => 0b001000#6
  | .VF_VSGNJN => 0b001001#6
  | .VF_VSGNJX => 0b001010#6
  | .VF_VSLIDE1UP => 0b001110#6
  | .VF_VSLIDE1DOWN => 0b001111#6
  | .VF_VDIV => 0b100000#6
  | .VF_VRDIV => 0b100001#6
  | .VF_VMUL => 0b100100#6
  | .VF_VRSUB => 0b100111#6

def encdec_fvfmafunct6_forwards (arg_ : fvfmafunct6) : (BitVec 6) :=
  match arg_ with
  | .VF_VMADD => 0b101000#6
  | .VF_VNMADD => 0b101001#6
  | .VF_VMSUB => 0b101010#6
  | .VF_VNMSUB => 0b101011#6
  | .VF_VMACC => 0b101100#6
  | .VF_VNMACC => 0b101101#6
  | .VF_VMSAC => 0b101110#6
  | .VF_VNMSAC => 0b101111#6

def encdec_fvfmfunct6_forwards (arg_ : fvfmfunct6) : (BitVec 6) :=
  match arg_ with
  | .VFM_VMFEQ => 0b011000#6
  | .VFM_VMFLE => 0b011001#6
  | .VFM_VMFLT => 0b011011#6
  | .VFM_VMFNE => 0b011100#6
  | .VFM_VMFGT => 0b011101#6
  | .VFM_VMFGE => 0b011111#6

def encdec_fvvfunct6_forwards (arg_ : fvvfunct6) : (BitVec 6) :=
  match arg_ with
  | .FVV_VADD => 0b000000#6
  | .FVV_VSUB => 0b000010#6
  | .FVV_VMIN => 0b000100#6
  | .FVV_VMAX => 0b000110#6
  | .FVV_VSGNJ => 0b001000#6
  | .FVV_VSGNJN => 0b001001#6
  | .FVV_VSGNJX => 0b001010#6
  | .FVV_VDIV => 0b100000#6
  | .FVV_VMUL => 0b100100#6

def encdec_fvvmafunct6_forwards (arg_ : fvvmafunct6) : (BitVec 6) :=
  match arg_ with
  | .FVV_VMADD => 0b101000#6
  | .FVV_VNMADD => 0b101001#6
  | .FVV_VMSUB => 0b101010#6
  | .FVV_VNMSUB => 0b101011#6
  | .FVV_VMACC => 0b101100#6
  | .FVV_VNMACC => 0b101101#6
  | .FVV_VMSAC => 0b101110#6
  | .FVV_VNMSAC => 0b101111#6

def encdec_fvvmfunct6_forwards (arg_ : fvvmfunct6) : (BitVec 6) :=
  match arg_ with
  | .FVVM_VMFEQ => 0b011000#6
  | .FVVM_VMFLE => 0b011001#6
  | .FVVM_VMFLT => 0b011011#6
  | .FVVM_VMFNE => 0b011100#6

def encdec_fwffunct6_forwards (arg_ : fwffunct6) : (BitVec 6) :=
  match arg_ with
  | .FWF_VADD => 0b110100#6
  | .FWF_VSUB => 0b110110#6

def encdec_fwvffunct6_forwards (arg_ : fwvffunct6) : (BitVec 6) :=
  match arg_ with
  | .FWVF_VADD => 0b110000#6
  | .FWVF_VSUB => 0b110010#6
  | .FWVF_VMUL => 0b111000#6

def encdec_fwvfmafunct6_forwards (arg_ : fwvfmafunct6) : (BitVec 6) :=
  match arg_ with
  | .FWVF_VMACC => 0b111100#6
  | .FWVF_VNMACC => 0b111101#6
  | .FWVF_VMSAC => 0b111110#6
  | .FWVF_VNMSAC => 0b111111#6

def encdec_fwvfunct6_forwards (arg_ : fwvfunct6) : (BitVec 6) :=
  match arg_ with
  | .FWV_VADD => 0b110100#6
  | .FWV_VSUB => 0b110110#6

def encdec_fwvvfunct6_forwards (arg_ : fwvvfunct6) : (BitVec 6) :=
  match arg_ with
  | .FWVV_VADD => 0b110000#6
  | .FWVV_VSUB => 0b110010#6
  | .FWVV_VMUL => 0b111000#6

def encdec_fwvvmafunct6_forwards (arg_ : fwvvmafunct6) : (BitVec 6) :=
  match arg_ with
  | .FWVV_VMACC => 0b111100#6
  | .FWVV_VNMACC => 0b111101#6
  | .FWVV_VMSAC => 0b111110#6
  | .FWVV_VNMSAC => 0b111111#6

def encdec_indexed_mop_forwards (arg_ : indexed_mop) : (BitVec 2) :=
  match arg_ with
  | .INDEXED_UNORDERED => 0b01#2
  | .INDEXED_ORDERED => 0b11#2

def encdec_iop_forwards (arg_ : iop) : (BitVec 3) :=
  match arg_ with
  | .ADDI => 0b000#3
  | .SLTI => 0b010#3
  | .SLTIU => 0b011#3
  | .ANDI => 0b111#3
  | .ORI => 0b110#3
  | .XORI => 0b100#3

def encdec_lsop_forwards (arg_ : vmlsop) : (BitVec 7) :=
  match arg_ with
  | .VLM => 0b0000111#7
  | .VSM => 0b0100111#7

def encdec_mmfunct6_forwards (arg_ : mmfunct6) : (BitVec 6) :=
  match arg_ with
  | .MM_VMAND => 0b011001#6
  | .MM_VMNAND => 0b011101#6
  | .MM_VMANDN => 0b011000#6
  | .MM_VMXOR => 0b011011#6
  | .MM_VMOR => 0b011010#6
  | .MM_VMNOR => 0b011110#6
  | .MM_VMORN => 0b011100#6
  | .MM_VMXNOR => 0b011111#6

def encdec_mul_op_forwards (arg_ : mul_op) : SailM (BitVec 3) := do
  match arg_ with
  | { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed } => (pure 0b000#3)
  | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed } => (pure 0b001#3)
  | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned } => (pure 0b010#3)
  | { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned } => (pure 0b011#3)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_mvvfunct6_forwards (arg_ : mvvfunct6) : (BitVec 6) :=
  match arg_ with
  | .MVV_VAADDU => 0b001000#6
  | .MVV_VAADD => 0b001001#6
  | .MVV_VASUBU => 0b001010#6
  | .MVV_VASUB => 0b001011#6
  | .MVV_VMUL => 0b100101#6
  | .MVV_VMULH => 0b100111#6
  | .MVV_VMULHU => 0b100100#6
  | .MVV_VMULHSU => 0b100110#6
  | .MVV_VDIVU => 0b100000#6
  | .MVV_VDIV => 0b100001#6
  | .MVV_VREMU => 0b100010#6
  | .MVV_VREM => 0b100011#6

def encdec_mvvmafunct6_forwards (arg_ : mvvmafunct6) : (BitVec 6) :=
  match arg_ with
  | .MVV_VMACC => 0b101101#6
  | .MVV_VNMSAC => 0b101111#6
  | .MVV_VMADD => 0b101001#6
  | .MVV_VNMSUB => 0b101011#6

def encdec_mvxfunct6_forwards (arg_ : mvxfunct6) : (BitVec 6) :=
  match arg_ with
  | .MVX_VAADDU => 0b001000#6
  | .MVX_VAADD => 0b001001#6
  | .MVX_VASUBU => 0b001010#6
  | .MVX_VASUB => 0b001011#6
  | .MVX_VSLIDE1UP => 0b001110#6
  | .MVX_VSLIDE1DOWN => 0b001111#6
  | .MVX_VMUL => 0b100101#6
  | .MVX_VMULH => 0b100111#6
  | .MVX_VMULHU => 0b100100#6
  | .MVX_VMULHSU => 0b100110#6
  | .MVX_VDIVU => 0b100000#6
  | .MVX_VDIV => 0b100001#6
  | .MVX_VREMU => 0b100010#6
  | .MVX_VREM => 0b100011#6

def encdec_mvxmafunct6_forwards (arg_ : mvxmafunct6) : (BitVec 6) :=
  match arg_ with
  | .MVX_VMACC => 0b101101#6
  | .MVX_VNMSAC => 0b101111#6
  | .MVX_VMADD => 0b101001#6
  | .MVX_VNMSUB => 0b101011#6

/-- Type quantifiers: arg_ : Nat, arg_ > 0 ∧ arg_ ≤ 8 -/
def encdec_nfields_backwards (arg_ : Nat) : (BitVec 3) :=
  match arg_ with
  | 1 => 0b000#3
  | 2 => 0b001#3
  | 3 => 0b010#3
  | 4 => 0b011#3
  | 5 => 0b100#3
  | 6 => 0b101#3
  | 7 => 0b110#3
  | _ => 0b111#3

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8] -/
def encdec_nfields_pow2_backwards (arg_ : Nat) : (BitVec 3) :=
  match arg_ with
  | 1 => 0b000#3
  | 2 => 0b001#3
  | 4 => 0b011#3
  | _ => 0b111#3

def encdec_nifunct6_forwards (arg_ : nifunct6) : (BitVec 6) :=
  match arg_ with
  | .NI_VNCLIPU => 0b101110#6
  | .NI_VNCLIP => 0b101111#6

def encdec_nisfunct6_forwards (arg_ : nisfunct6) : (BitVec 6) :=
  match arg_ with
  | .NIS_VNSRL => 0b101100#6
  | .NIS_VNSRA => 0b101101#6

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8] -/
def encdec_nreg_backwards (arg_ : Nat) : (BitVec 5) :=
  match arg_ with
  | 1 => 0b00000#5
  | 2 => 0b00001#5
  | 4 => 0b00011#5
  | _ => 0b00111#5

def encdec_ntl_forwards (arg_ : ntl_type) : (BitVec 5) :=
  match arg_ with
  | .NTL_P1 => 0b00010#5
  | .NTL_PALL => 0b00011#5
  | .NTL_S1 => 0b00100#5
  | .NTL_ALL => 0b00101#5

def encdec_nvfunct6_forwards (arg_ : nvfunct6) : (BitVec 6) :=
  match arg_ with
  | .NV_VNCLIPU => 0b101110#6
  | .NV_VNCLIP => 0b101111#6

def encdec_nvsfunct6_forwards (arg_ : nvsfunct6) : (BitVec 6) :=
  match arg_ with
  | .NVS_VNSRL => 0b101100#6
  | .NVS_VNSRA => 0b101101#6

def encdec_nxfunct6_forwards (arg_ : nxfunct6) : (BitVec 6) :=
  match arg_ with
  | .NX_VNCLIPU => 0b101110#6
  | .NX_VNCLIP => 0b101111#6

def encdec_nxsfunct6_forwards (arg_ : nxsfunct6) : (BitVec 6) :=
  match arg_ with
  | .NXS_VNSRL => 0b101100#6
  | .NXS_VNSRA => 0b101101#6

def encdec_rfvvfunct6_forwards (arg_ : rfvvfunct6) : (BitVec 6) :=
  match arg_ with
  | .FVV_VFREDOSUM => 0b000011#6
  | .FVV_VFREDUSUM => 0b000001#6
  | .FVV_VFREDMAX => 0b000111#6
  | .FVV_VFREDMIN => 0b000101#6

def encdec_rfwvvfunct6_forwards (arg_ : rfwvvfunct6) : (BitVec 6) :=
  match arg_ with
  | .FVV_VFWREDOSUM => 0b110011#6
  | .FVV_VFWREDUSUM => 0b110001#6

def encdec_rivvfunct6_forwards (arg_ : rivvfunct6) : (BitVec 6) :=
  match arg_ with
  | .IVV_VWREDSUMU => 0b110000#6
  | .IVV_VWREDSUM => 0b110001#6

def encdec_rmvvfunct6_forwards (arg_ : rmvvfunct6) : (BitVec 6) :=
  match arg_ with
  | .MVV_VREDSUM => 0b000000#6
  | .MVV_VREDAND => 0b000001#6
  | .MVV_VREDOR => 0b000010#6
  | .MVV_VREDXOR => 0b000011#6
  | .MVV_VREDMINU => 0b000100#6
  | .MVV_VREDMIN => 0b000101#6
  | .MVV_VREDMAXU => 0b000110#6
  | .MVV_VREDMAX => 0b000111#6

def encdec_rounding_mode_forwards (arg_ : rounding_mode) : (BitVec 3) :=
  match arg_ with
  | .RM_RNE => 0b000#3
  | .RM_RTZ => 0b001#3
  | .RM_RDN => 0b010#3
  | .RM_RUP => 0b011#3
  | .RM_RMM => 0b100#3
  | .RM_DYN => 0b111#3

def encdec_uop_forwards (arg_ : uop) : (BitVec 7) :=
  match arg_ with
  | .LUI => 0b0110111#7
  | .AUIPC => 0b0010111#7

def encdec_vaesdf_forwards (arg_ : zvk_vaesdf_funct6) : (BitVec 6) :=
  match arg_ with
  | .ZVK_VAESDF_VV => 0b101000#6
  | .ZVK_VAESDF_VS => 0b101001#6

def encdec_vaesdm_forwards (arg_ : zvk_vaesdm_funct6) : (BitVec 6) :=
  match arg_ with
  | .ZVK_VAESDM_VV => 0b101000#6
  | .ZVK_VAESDM_VS => 0b101001#6

def encdec_vaesef_forwards (arg_ : zvk_vaesef_funct6) : (BitVec 6) :=
  match arg_ with
  | .ZVK_VAESEF_VV => 0b101000#6
  | .ZVK_VAESEF_VS => 0b101001#6

def encdec_vaesem_forwards (arg_ : zvk_vaesem_funct6) : (BitVec 6) :=
  match arg_ with
  | .ZVK_VAESEM_VV => 0b101000#6
  | .ZVK_VAESEM_VS => 0b101001#6

def encdec_vfnunary0_vs1_forwards (arg_ : vfnunary0) : (BitVec 5) :=
  match arg_ with
  | .FNV_CVT_XU_F => 0b10000#5
  | .FNV_CVT_X_F => 0b10001#5
  | .FNV_CVT_F_XU => 0b10010#5
  | .FNV_CVT_F_X => 0b10011#5
  | .FNV_CVT_F_F => 0b10100#5
  | .FNV_CVT_ROD_F_F => 0b10101#5
  | .FNV_CVT_RTZ_XU_F => 0b10110#5
  | .FNV_CVT_RTZ_X_F => 0b10111#5

def encdec_vfunary0_vs1_forwards (arg_ : vfunary0) : (BitVec 5) :=
  match arg_ with
  | .FV_CVT_XU_F => 0b00000#5
  | .FV_CVT_X_F => 0b00001#5
  | .FV_CVT_F_XU => 0b00010#5
  | .FV_CVT_F_X => 0b00011#5
  | .FV_CVT_RTZ_XU_F => 0b00110#5
  | .FV_CVT_RTZ_X_F => 0b00111#5

def encdec_vfunary1_vs1_forwards (arg_ : vfunary1) : (BitVec 5) :=
  match arg_ with
  | .FVV_VSQRT => 0b00000#5
  | .FVV_VRSQRT7 => 0b00100#5
  | .FVV_VREC7 => 0b00101#5
  | .FVV_VCLASS => 0b10000#5

def encdec_vfwunary0_vs1_forwards (arg_ : vfwunary0) : (BitVec 5) :=
  match arg_ with
  | .FWV_CVT_XU_F => 0b01000#5
  | .FWV_CVT_X_F => 0b01001#5
  | .FWV_CVT_F_XU => 0b01010#5
  | .FWV_CVT_F_X => 0b01011#5
  | .FWV_CVT_F_F => 0b01100#5
  | .FWV_CVT_RTZ_XU_F => 0b01110#5
  | .FWV_CVT_RTZ_X_F => 0b01111#5

def encdec_vicmpfunct6_forwards (arg_ : vicmpfunct6) : (BitVec 6) :=
  match arg_ with
  | .VICMP_VMSEQ => 0b011000#6
  | .VICMP_VMSNE => 0b011001#6
  | .VICMP_VMSLEU => 0b011100#6
  | .VICMP_VMSLE => 0b011101#6
  | .VICMP_VMSGTU => 0b011110#6
  | .VICMP_VMSGT => 0b011111#6

def encdec_vifunct6_forwards (arg_ : vifunct6) : (BitVec 6) :=
  match arg_ with
  | .VI_VADD => 0b000000#6
  | .VI_VRSUB => 0b000011#6
  | .VI_VAND => 0b001001#6
  | .VI_VOR => 0b001010#6
  | .VI_VXOR => 0b001011#6
  | .VI_VSADDU => 0b100000#6
  | .VI_VSADD => 0b100001#6
  | .VI_VSLL => 0b100101#6
  | .VI_VSRL => 0b101000#6
  | .VI_VSRA => 0b101001#6
  | .VI_VSSRL => 0b101010#6
  | .VI_VSSRA => 0b101011#6

def encdec_vimcfunct6_forwards (arg_ : vimcfunct6) : (BitVec 6) :=
  match arg_ with
  | .VIMC_VMADC => 0b010001#6

def encdec_vimfunct6_forwards (arg_ : vimfunct6) : (BitVec 6) :=
  match arg_ with
  | .VIM_VMADC => 0b010001#6

def encdec_vimsfunct6_forwards (arg_ : vimsfunct6) : (BitVec 6) :=
  match arg_ with
  | .VIMS_VADC => 0b010000#6

def encdec_visgfunct6_forwards (arg_ : visgfunct6) : (BitVec 6) :=
  match arg_ with
  | .VI_VSLIDEUP => 0b001110#6
  | .VI_VSLIDEDOWN => 0b001111#6
  | .VI_VRGATHER => 0b001100#6

def encdec_vlewidth_forwards (arg_ : vlewidth) : (BitVec 3) :=
  match arg_ with
  | .VLE8 => 0b000#3
  | .VLE16 => 0b101#3
  | .VLE32 => 0b110#3
  | .VLE64 => 0b111#3

def encdec_vreg_forwards (arg_ : vregidx) : (BitVec 5) :=
  match arg_ with
  | .Vregidx r => r

def encdec_vsha2_forwards (arg_ : zvk_vsha2_funct6) : (BitVec 6) :=
  match arg_ with
  | .ZVK_VSHA2CH_VV => 0b101110#6
  | .ZVK_VSHA2CL_VV => 0b101111#6

def encdec_vvcmpfunct6_forwards (arg_ : vvcmpfunct6) : (BitVec 6) :=
  match arg_ with
  | .VVCMP_VMSEQ => 0b011000#6
  | .VVCMP_VMSNE => 0b011001#6
  | .VVCMP_VMSLTU => 0b011010#6
  | .VVCMP_VMSLT => 0b011011#6
  | .VVCMP_VMSLEU => 0b011100#6
  | .VVCMP_VMSLE => 0b011101#6

def encdec_vvfunct6_forwards (arg_ : vvfunct6) : (BitVec 6) :=
  match arg_ with
  | .VV_VADD => 0b000000#6
  | .VV_VSUB => 0b000010#6
  | .VV_VMINU => 0b000100#6
  | .VV_VMIN => 0b000101#6
  | .VV_VMAXU => 0b000110#6
  | .VV_VMAX => 0b000111#6
  | .VV_VAND => 0b001001#6
  | .VV_VOR => 0b001010#6
  | .VV_VXOR => 0b001011#6
  | .VV_VRGATHER => 0b001100#6
  | .VV_VRGATHEREI16 => 0b001110#6
  | .VV_VSADDU => 0b100000#6
  | .VV_VSADD => 0b100001#6
  | .VV_VSSUBU => 0b100010#6
  | .VV_VSSUB => 0b100011#6
  | .VV_VSLL => 0b100101#6
  | .VV_VSMUL => 0b100111#6
  | .VV_VSRL => 0b101000#6
  | .VV_VSRA => 0b101001#6
  | .VV_VSSRL => 0b101010#6
  | .VV_VSSRA => 0b101011#6

def encdec_vvmcfunct6_forwards (arg_ : vvmcfunct6) : (BitVec 6) :=
  match arg_ with
  | .VVMC_VMADC => 0b010001#6
  | .VVMC_VMSBC => 0b010011#6

def encdec_vvmfunct6_forwards (arg_ : vvmfunct6) : (BitVec 6) :=
  match arg_ with
  | .VVM_VMADC => 0b010001#6
  | .VVM_VMSBC => 0b010011#6

def encdec_vvmsfunct6_forwards (arg_ : vvmsfunct6) : (BitVec 6) :=
  match arg_ with
  | .VVMS_VADC => 0b010000#6
  | .VVMS_VSBC => 0b010010#6

def encdec_vxcmpfunct6_forwards (arg_ : vxcmpfunct6) : (BitVec 6) :=
  match arg_ with
  | .VXCMP_VMSEQ => 0b011000#6
  | .VXCMP_VMSNE => 0b011001#6
  | .VXCMP_VMSLTU => 0b011010#6
  | .VXCMP_VMSLT => 0b011011#6
  | .VXCMP_VMSLEU => 0b011100#6
  | .VXCMP_VMSLE => 0b011101#6
  | .VXCMP_VMSGTU => 0b011110#6
  | .VXCMP_VMSGT => 0b011111#6

def encdec_vxfunct6_forwards (arg_ : vxfunct6) : (BitVec 6) :=
  match arg_ with
  | .VX_VADD => 0b000000#6
  | .VX_VSUB => 0b000010#6
  | .VX_VRSUB => 0b000011#6
  | .VX_VMINU => 0b000100#6
  | .VX_VMIN => 0b000101#6
  | .VX_VMAXU => 0b000110#6
  | .VX_VMAX => 0b000111#6
  | .VX_VAND => 0b001001#6
  | .VX_VOR => 0b001010#6
  | .VX_VXOR => 0b001011#6
  | .VX_VSADDU => 0b100000#6
  | .VX_VSADD => 0b100001#6
  | .VX_VSSUBU => 0b100010#6
  | .VX_VSSUB => 0b100011#6
  | .VX_VSLL => 0b100101#6
  | .VX_VSMUL => 0b100111#6
  | .VX_VSRL => 0b101000#6
  | .VX_VSRA => 0b101001#6
  | .VX_VSSRL => 0b101010#6
  | .VX_VSSRA => 0b101011#6

def encdec_vxmcfunct6_forwards (arg_ : vxmcfunct6) : (BitVec 6) :=
  match arg_ with
  | .VXMC_VMADC => 0b010001#6
  | .VXMC_VMSBC => 0b010011#6

def encdec_vxmfunct6_forwards (arg_ : vxmfunct6) : (BitVec 6) :=
  match arg_ with
  | .VXM_VMADC => 0b010001#6
  | .VXM_VMSBC => 0b010011#6

def encdec_vxmsfunct6_forwards (arg_ : vxmsfunct6) : (BitVec 6) :=
  match arg_ with
  | .VXMS_VADC => 0b010000#6
  | .VXMS_VSBC => 0b010010#6

def encdec_vxsgfunct6_forwards (arg_ : vxsgfunct6) : (BitVec 6) :=
  match arg_ with
  | .VX_VSLIDEUP => 0b001110#6
  | .VX_VSLIDEDOWN => 0b001111#6
  | .VX_VRGATHER => 0b001100#6

def encdec_wmvvfunct6_forwards (arg_ : wmvvfunct6) : (BitVec 6) :=
  match arg_ with
  | .WMVV_VWMACCU => 0b111100#6
  | .WMVV_VWMACC => 0b111101#6
  | .WMVV_VWMACCSU => 0b111111#6

def encdec_wmvxfunct6_forwards (arg_ : wmvxfunct6) : (BitVec 6) :=
  match arg_ with
  | .WMVX_VWMACCU => 0b111100#6
  | .WMVX_VWMACC => 0b111101#6
  | .WMVX_VWMACCUS => 0b111110#6
  | .WMVX_VWMACCSU => 0b111111#6

def encdec_wrsop_forwards (arg_ : wrsop) : (BitVec 12) :=
  match arg_ with
  | .WRS_STO => 0b000000011101#12
  | .WRS_NTO => 0b000000001101#12

def encdec_wvfunct6_forwards (arg_ : wvfunct6) : (BitVec 6) :=
  match arg_ with
  | .WV_VADD => 0b110101#6
  | .WV_VSUB => 0b110111#6
  | .WV_VADDU => 0b110100#6
  | .WV_VSUBU => 0b110110#6

def encdec_wvvfunct6_forwards (arg_ : wvvfunct6) : (BitVec 6) :=
  match arg_ with
  | .WVV_VADD => 0b110001#6
  | .WVV_VSUB => 0b110011#6
  | .WVV_VADDU => 0b110000#6
  | .WVV_VSUBU => 0b110010#6
  | .WVV_VWMUL => 0b111011#6
  | .WVV_VWMULU => 0b111000#6
  | .WVV_VWMULSU => 0b111010#6

def encdec_wvxfunct6_forwards (arg_ : wvxfunct6) : (BitVec 6) :=
  match arg_ with
  | .WVX_VADD => 0b110001#6
  | .WVX_VSUB => 0b110011#6
  | .WVX_VADDU => 0b110000#6
  | .WVX_VSUBU => 0b110010#6
  | .WVX_VWMUL => 0b111011#6
  | .WVX_VWMULU => 0b111000#6
  | .WVX_VWMULSU => 0b111010#6

def encdec_wxfunct6_forwards (arg_ : wxfunct6) : (BitVec 6) :=
  match arg_ with
  | .WX_VADD => 0b110101#6
  | .WX_VSUB => 0b110111#6
  | .WX_VADDU => 0b110100#6
  | .WX_VSUBU => 0b110110#6

def encdec_zicondop_forwards (arg_ : zicondop) : (BitVec 3) :=
  match arg_ with
  | .CZERO_EQZ => 0b101#3
  | .CZERO_NEZ => 0b111#3

def encdec_zilx_mode_forwards (arg_ : zilx_mode) : (BitVec 5) :=
  match arg_ with
  | .ZILX_UNSCALED => 0b10010#5
  | .ZILX_SCALED => 0b11010#5
  | .ZILX_SCALED_UW => 0b11110#5

def encdec_zvabd_vabd_func6_forwards (arg_ : zvabd_vabd_func6) : (BitVec 6) :=
  match arg_ with
  | .VABD => 0b010101#6
  | .VABDU => 0b010110#6

def encdec_zvabd_vwabda_func6_forwards (arg_ : zvabd_vwabda_func6) : (BitVec 6) :=
  match arg_ with
  | .VWABDA => 0b111101#6
  | .VWABDAU => 0b111110#6

/-- Type quantifiers: width : Nat, List.elem width [1, 2, 4, 8] -/
def float_load_store_width_supported (width : Nat) : SailM Bool := do
  match width with
  | 1 => (pure false)
  | 2 => (pure ((← (currentlyEnabled Ext_Zfhmin)) || (← (currentlyEnabled Ext_Zfbfmin))))
  | 4 => (currentlyEnabled Ext_F)
  | _ => (currentlyEnabled Ext_D)

def _get_Vtype_vlmul (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def get_lmul_pow (_ : Unit) : SailM Int := do
  let lmul_pow ← do (pure (BitVec.toInt (_get_Vtype_vlmul (← readReg vtype))))
  «assert» (lmul_pow >b (Neg.neg 4)) "Reserved LMUL stored in vtype register. This should be impossible."
  (pure lmul_pow)

def _get_Vtype_vsew (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 5 3)

def get_sew_pow (_ : Unit) : SailM Nat := do
  let sew_pow ← do (pure (BitVec.toNatInt (_get_Vtype_vsew (← readReg vtype))))
  «assert» (sew_pow <b 4) "Reserved SEW stored in vtype register. This should be impossible."
  (pure (sew_pow +i 3))

def get_sew (_ : Unit) : SailM Int := do
  (pure (2 ^i (← (get_sew_pow ()))))

def haveDoubleFPU (_ : Unit) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_D)) || (← (currentlyEnabled Ext_Zdinx))))

def haveHalfFPU (_ : Unit) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_Zfh)) || (← (currentlyEnabled Ext_Zhinx))))

def haveHalfMin (_ : Unit) : SailM Bool := do
  (pure ((← (haveHalfFPU ())) || ((← (currentlyEnabled Ext_Zfhmin)) || (← (currentlyEnabled
            Ext_Zhinxmin)))))

def haveSingleFPU (_ : Unit) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_F)) || (← (currentlyEnabled Ext_Zfinx))))

def architecture_bits_backwards (arg_ : (BitVec 2)) : SailM Architecture := do
  match arg_ with
  | 0b01 => (pure RV32)
  | 0b10 => (pure RV64)
  | 0b11 => (pure RV128)
  | _ => (internal_error "core/types.sail" 62 "architecture(0b00) is invalid")

def architecture (priv : Privilege) : SailM Architecture := SailME.run do
  SailME.throw (RV32 : Architecture)
  (architecture_bits_backwards
    (← do
      «assert» false "Pattern match failure at core/sys_regs.sail:1281.20-1287.3"
      throw Error.Exit))

def in32BitMode (_ : Unit) : SailM Bool := do
  (pure ((← (architecture (← readReg cur_privilege))) == RV32))

/-- Type quantifiers: width : Nat, List.elem width [1, 2, 4, 8] -/
def lrsc_width_valid (width : Nat) : Bool :=
  match width with
  | 4 => true
  | 8 => (xlen ≥b 64)
  | _ => false

def fregidx_bits (app_0 : fregidx) : (BitVec 5) :=
  let .Fregidx r := app_0
  r

def rv32zdinx_odd_register_reserved_behavior : RV32ZdinxOddRegisterReservedBehavior := Zdinx_Illegal

/-- Type quantifiers: n : Nat, n ≥ 0, n > 0 -/
def validDoubleRegs {n : _} (regs : (Vector fregidx n)) : SailM Bool := SailME.run do
  if (((← (currentlyEnabled Ext_Zdinx)) && (xlen == 32)) : Bool)
  then
    (do
      let loop_i_lower := 0
      let loop_i_upper := (n -i 1)
      let mut loop_vars := ()
      for i in [loop_i_lower:loop_i_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          if (((BitVec.access (fregidx_bits (GetElem?.getElem! regs i)) 0) == 1#1) : Bool)
          then
            (do
              match rv32zdinx_odd_register_reserved_behavior with
              | .Zdinx_Fatal =>
                (reserved_behavior
                  (HAppend.hAppend "RV32Zdinx used odd-numbered register "
                    (Int.repr (BitVec.toNatInt (fregidx_bits (GetElem?.getElem! regs i))))))
              | .Zdinx_Illegal => SailME.throw (false : Bool))
          else (pure ())
      (pure loop_vars))
  else (pure ())
  (pure true)

def valid_narrowing_fp_conversion (cvt : vfnunary0) : SailM Bool := do
  match cvt with
  | .FNV_CVT_F_F =>
    (pure (((← (currentlyEnabled Ext_Zvfhmin)) && (← do
            (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
            (pure ((← (get_sew ())) == 32))))))
  | .FNV_CVT_ROD_F_F =>
    (pure (((← (currentlyEnabled Ext_Zvfh)) && (← do
            (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
            (pure ((← (get_sew ())) == 32))))))
  | .FNV_CVT_F_XU =>
    (pure (((← (currentlyEnabled Ext_Zvfh)) && (← do
            (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64f)) && (← do
            (pure ((← (get_sew ())) == 32))))))
  | .FNV_CVT_F_X =>
    (pure (((← (currentlyEnabled Ext_Zvfh)) && (← do
            (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64f)) && (← do
            (pure ((← (get_sew ())) == 32))))))
  | _ =>
    (pure (((← (currentlyEnabled Ext_Zvfh)) && (← do
            (pure ((← (get_sew ())) == 8)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
              (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
              (pure ((← (get_sew ())) == 32)))))))

def valid_wide_mvvtype (mvvtype : mvvfunct6) : SailM Bool := do
  match mvvtype with
  | .MVV_VMULH =>
    (pure ((hartSupports Ext_V) && (((_get_Misa_V (← readReg misa)) == 1#1) && (← (currentlyEnabled
              Ext_Zvl128b)))))
  | .MVV_VMULHU =>
    (pure ((hartSupports Ext_V) && (((_get_Misa_V (← readReg misa)) == 1#1) && (← (currentlyEnabled
              Ext_Zvl128b)))))
  | .MVV_VMULHSU =>
    (pure ((hartSupports Ext_V) && (((_get_Misa_V (← readReg misa)) == 1#1) && (← (currentlyEnabled
              Ext_Zvl128b)))))
  | _ => (pure true)

def valid_wide_mvxtype (mvxtype : mvxfunct6) : SailM Bool := do
  match mvxtype with
  | .MVX_VMULH =>
    (pure ((hartSupports Ext_V) && (((_get_Misa_V (← readReg misa)) == 1#1) && (← (currentlyEnabled
              Ext_Zvl128b)))))
  | .MVX_VMULHU =>
    (pure ((hartSupports Ext_V) && (((_get_Misa_V (← readReg misa)) == 1#1) && (← (currentlyEnabled
              Ext_Zvl128b)))))
  | .MVX_VMULHSU =>
    (pure ((hartSupports Ext_V) && (((_get_Misa_V (← readReg misa)) == 1#1) && (← (currentlyEnabled
              Ext_Zvl128b)))))
  | _ => (pure true)

def valid_wide_vvtype (vvtype : vvfunct6) : SailM Bool := do
  match vvtype with
  | .VV_VSMUL =>
    (pure ((hartSupports Ext_V) && (((_get_Misa_V (← readReg misa)) == 1#1) && (← (currentlyEnabled
              Ext_Zvl128b)))))
  | _ => (pure true)

def valid_wide_vxtype (vxtype : vxfunct6) : SailM Bool := do
  match vxtype with
  | .VX_VSMUL =>
    (pure ((hartSupports Ext_V) && (((_get_Misa_V (← readReg misa)) == 1#1) && (← (currentlyEnabled
              Ext_Zvl128b)))))
  | _ => (pure true)

def valid_widening_fp_conversion (cvt : vfwunary0) : SailM Bool := do
  match cvt with
  | .FWV_CVT_F_F =>
    (pure (((← (currentlyEnabled Ext_Zvfhmin)) && (← do
            (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
            (pure ((← (get_sew ())) == 32))))))
  | .FWV_CVT_F_XU =>
    (pure (((← (currentlyEnabled Ext_Zvfh)) && (← do
            (pure ((← (get_sew ())) == 8)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
              (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
              (pure ((← (get_sew ())) == 32)))))))
  | .FWV_CVT_F_X =>
    (pure (((← (currentlyEnabled Ext_Zvfh)) && (← do
            (pure ((← (get_sew ())) == 8)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
              (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
              (pure ((← (get_sew ())) == 32)))))))
  | _ =>
    (pure (((← (currentlyEnabled Ext_Zvfh)) && (← do
            (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64f)) && (← do
            (pure ((← (get_sew ())) == 32))))))

/-- Type quantifiers: sew : Nat, List.elem sew [8, 16, 32, 64] -/
def valid_zvwabda_sew (sew : Nat) : Bool :=
  ((sew == 8) || (sew == 16))

def vext_vs1_forwards (arg_ : vextfunct6) : (BitVec 5) :=
  match arg_ with
  | .VEXT2_ZVF2 => 0b00110#5
  | .VEXT2_SVF2 => 0b00111#5
  | .VEXT4_ZVF4 => 0b00100#5
  | .VEXT4_SVF4 => 0b00101#5
  | .VEXT8_ZVF8 => 0b00010#5
  | .VEXT8_SVF8 => 0b00011#5

def virtual_memory_supported (_ : Unit) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_Sv32)) || ((← (currentlyEnabled Ext_Sv39)) || ((← (currentlyEnabled
              Ext_Sv48)) || (← (currentlyEnabled Ext_Sv57))))))

def vlewidth_pow_forwards (arg_ : vlewidth) : Int :=
  match arg_ with
  | .VLE8 => 3
  | .VLE16 => 4
  | .VLE32 => 5
  | .VLE64 => 6

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8] -/
def width_enc_forwards (arg_ : Nat) : (BitVec 2) :=
  match arg_ with
  | 1 => 0b00#2
  | 2 => 0b01#2
  | 4 => 0b10#2
  | _ => 0b11#2

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8, 16] -/
def width_enc_wide_forwards (arg_ : Nat) : (BitVec 3) :=
  match arg_ with
  | 1 => 0b000#3
  | 2 => 0b001#3
  | 4 => 0b010#3
  | 8 => 0b011#3
  | _ => 0b100#3

def zicfiss_xSSE (priv : Privilege) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_S)) && (← do
        match priv with
        | .Machine => (pure false)
        | .Supervisor => (pure (bool_bit_backwards (_get_MEnvcfg_SSE (← readReg menvcfg))))
        | .VirtualSupervisor =>
          (pure (((_get_MEnvcfg_SSE (← readReg menvcfg)) == 1#1) && ((_get_HEnvcfg_SSE
                  (← (read_henvcfg ()))) == 1#1)))
        | .User => (pure (bool_bit_backwards (_get_SEnvcfg_SSE (← (read_senvcfg ())))))
        | .VirtualUser => (pure (bool_bit_backwards (_get_SEnvcfg_SSE (← (read_senvcfg ()))))))))

def vstart_reserved_behavior : OOBVstartReservedBehavior := Vstart_Illegal

/-- Type quantifiers: EGS : Nat, EGW : Nat, 0 ≤ EGW, EGS > 0 -/
def zvk_check_encdec (EGW : Nat) (EGS : Nat) : SailM Bool := do
  let LMUL_pow ← do (get_lmul_pow ())
  let LMUL_times_VLEN :=
    if ((LMUL_pow <b 0) : Bool)
    then (Int.tdiv vlen (2 ^i (Int.natAbs LMUL_pow)))
    else ((2 ^i LMUL_pow) *i vlen)
  let VLMAX ← do (pure (Int.tdiv LMUL_times_VLEN (← (get_sew ()))))
  let vstart_in_bounds ← (( do
    match vstart_reserved_behavior with
    | .Vstart_Illegal => (pure ((BitVec.toNatInt (← readReg vstart)) <b VLMAX))
    | .Vstart_Ignore => (pure true) ) : SailM Bool )
  (pure (((Int.tmod (BitVec.toNatInt (← readReg vl)) EGS) == 0) && (← do
        (pure (((Int.tmod (BitVec.toNatInt (← readReg vstart)) EGS) == 0) && ((LMUL_times_VLEN ≥b EGW) && vstart_in_bounds))))))

def vregidx_bits (app_0 : vregidx) : (BitVec 5) :=
  let .Vregidx b := app_0
  b

/-- Type quantifiers: emul_pow : Int -/
def zvk_valid_reg_overlap (rs : vregidx) (rd : vregidx) (emul_pow : Int) : Bool :=
  let reg_group_size :=
    if ((emul_pow >b 0) : Bool)
    then (2 ^i emul_pow)
    else 1
  let rs_int := (BitVec.toNatInt (vregidx_bits rs))
  let rd_int := (BitVec.toNatInt (vregidx_bits rd))
  (((rs_int +i reg_group_size) ≤b rd_int) || ((rd_int +i reg_group_size) ≤b rs_int))

def zvknhab_check_encdec (vs2 : vregidx) (vs1 : vregidx) (vd : vregidx) : SailM Bool := do
  let SEW ← do (get_sew ())
  let LMUL_pow ← do (get_lmul_pow ())
  (pure ((← (zvk_check_encdec SEW 4)) && ((zvk_valid_reg_overlap vs1 vd LMUL_pow) && (zvk_valid_reg_overlap
          vs2 vd LMUL_pow))))

def max_index_eew_exp : Nat := 5

def ra : regidx := (Regidx (zero_extend (m := 5) 0b01#2))

def t0 : regidx := (Regidx (zero_extend (m := 5) 0b101#3))

noncomputable def encdec_forwards (arg_ : instruction) : SailM (BitVec 32) := do
  match arg_ with
  | .ZICBOP (cbop, rs1, v__12) =>
    (do
      if (((← (currentlyEnabled Ext_Zicbop)) && ((Sail.BitVec.extractLsb v__12 4 0) == (0b00000#5 : (BitVec 5)))) : Bool)
      then
        (let offset11_5 : (BitVec 7) := (Sail.BitVec.extractLsb v__12 11 5)
        let offset11_5 : (BitVec 7) := (Sail.BitVec.extractLsb v__12 11 5)
        (pure ((offset11_5 : (BitVec 7)) +++ ((encdec_cbop_zicbop_forwards cbop) +++ ((encdec_reg_forwards
                  rs1) +++ (0b110#3 +++ (0b00000#5 +++ 0b0010011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .NTL op =>
    (do
      if ((← (currentlyEnabled Ext_Zihintntl)) : Bool)
      then
        (pure (0b0000000#7 +++ ((encdec_ntl_forwards op) +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .PAUSE () =>
    (do
      if ((← (currentlyEnabled Ext_Zihintpause)) : Bool)
      then
        (pure (0b0000#4 +++ (0b0001#4 +++ (0b0000#4 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b0001111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .LPAD lpl =>
    (do
      if ((← (currentlyEnabled Ext_Zicfilp)) : Bool)
      then (pure ((lpl : (BitVec 20)) +++ (0b00000#5 +++ 0b0010111#7)))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .UTYPE (imm, rd, op) =>
    (pure ((imm : (BitVec 20)) +++ ((encdec_reg_forwards rd) +++ (encdec_uop_forwards op))))
  | .JAL (v__14, rd) =>
    (do
      if (((Sail.BitVec.extractLsb v__14 0 0) == (0#1 : (BitVec 1))) : Bool)
      then
        (let imm := (Sail.BitVec.extractLsb v__14 20 1)
        let imm := (Sail.BitVec.extractLsb v__14 20 1)
        (pure ((Sail.BitVec.extractLsb imm 19 19) +++ ((Sail.BitVec.extractLsb imm 9 0) +++ ((Sail.BitVec.extractLsb
                  imm 10 10) +++ ((Sail.BitVec.extractLsb imm 18 11) +++ ((encdec_reg_forwards rd) +++ 0b1101111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .JALR (imm, rs1, rd) =>
    (pure ((imm : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                rd) +++ 0b1100111#7)))))
  | .BTYPE (v__16, rs2, rs1, op) =>
    (do
      if (((Sail.BitVec.extractLsb v__16 0 0) == (0#1 : (BitVec 1))) : Bool)
      then
        (let imm := (Sail.BitVec.extractLsb v__16 12 1)
        let imm := (Sail.BitVec.extractLsb v__16 12 1)
        (pure ((Sail.BitVec.extractLsb imm 11 11) +++ ((Sail.BitVec.extractLsb imm 9 4) +++ ((encdec_reg_forwards
                  rs2) +++ ((encdec_reg_forwards rs1) +++ ((encdec_bop_forwards op) +++ ((Sail.BitVec.extractLsb
                        imm 3 0) +++ ((Sail.BitVec.extractLsb imm 10 10) +++ 0b1100011#7)))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ITYPE (imm, rs1, rd, op) =>
    (pure ((imm : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ ((encdec_iop_forwards op) +++ ((encdec_reg_forwards
                rd) +++ 0b0010011#7)))))
  | .SHIFTIOP (shamt, rs1, rd, .SLLI) =>
    (do
      if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
      then
        (pure (0b000000#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIOP (shamt, rs1, rd, .SRLI) =>
    (do
      if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
      then
        (pure (0b000000#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIOP (shamt, rs1, rd, .SRAI) =>
    (do
      if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
      then
        (pure (0b010000#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPE (rs2, rs1, rd, .ADD) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SLT) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b010#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SLTU) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b011#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .AND) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b111#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .OR) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b110#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .XOR) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SLL) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SRL) =>
    (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SUB) =>
    (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, .SRA) =>
    (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                  rd) +++ 0b0110011#7))))))
  | .LOAD (imm, rs1, rd, is_unsigned, width) =>
    (do
      if ((valid_load_encdec width is_unsigned) : Bool)
      then
        (pure ((imm : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ ((bool_bit_forwards
                  is_unsigned) +++ ((width_enc_forwards width) +++ ((encdec_reg_forwards rd) +++ 0b0000011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .STORE (imm, rs2, rs1, width) =>
    (do
      if ((width ≤b xlen_bytes) : Bool)
      then
        (pure ((Sail.BitVec.extractLsb imm 11 5) +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards
                  rs1) +++ (0#1 +++ ((width_enc_forwards width) +++ ((Sail.BitVec.extractLsb imm 4 0) +++ 0b0100011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ADDIW (imm, rs1, rd) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure ((imm : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                    rd) +++ 0b0011011#7)))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, .ADDW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0111011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, .SUBW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0111011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, .SLLW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0111011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, .SRLW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0111011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, .SRAW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0111011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIWOP (shamt, rs1, rd, .SLLIW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0000000#7 +++ ((shamt : (BitVec 5)) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0011011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIWOP (shamt, rs1, rd, .SRLIW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0000000#7 +++ ((shamt : (BitVec 5)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0011011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIWOP (shamt, rs1, rd, .SRAIW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0100000#7 +++ ((shamt : (BitVec 5)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0011011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FENCE_TSO () =>
    (pure (0b1000#4 +++ (0b0011#4 +++ (0b0011#4 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b0001111#7)))))))
  | .FENCE (fm, pred, succ, rs, rd) =>
    (pure ((fm : (BitVec 4)) +++ ((pred : (BitVec 4)) +++ ((succ : (BitVec 4)) +++ ((encdec_reg_forwards
                rs) +++ (0b000#3 +++ ((encdec_reg_forwards rd) +++ 0b0001111#7)))))))
  | .ECALL () =>
    (pure (0b000000000000#12 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7)))))
  | .MRET () =>
    (pure (0b0011000#7 +++ (0b00010#5 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
  | .SRET () =>
    (pure (0b0001000#7 +++ (0b00010#5 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
  | .EBREAK () =>
    (pure (0b000000000001#12 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7)))))
  | .WFI () =>
    (pure (0b000100000101#12 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7)))))
  | .SFENCE_VMA (rs1, rs2) =>
    (do
      if (((← (virtual_memory_supported ())) || (not (true : Bool))) : Bool)
      then
        (pure (0b0001001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .AMO (op, aq, rl, rs2, rs1, size, rd) =>
    (do
      if ((← (amo_encoding_valid size op rs2 rd)) : Bool)
      then
        (pure ((encdec_amoop_forwards op) +++ ((bool_bit_forwards aq) +++ ((bool_bit_forwards rl) +++ ((encdec_reg_forwards
                    rs2) +++ ((encdec_reg_forwards rs1) +++ ((width_enc_wide_forwards size) +++ ((encdec_reg_forwards
                          rd) +++ 0b0101111#7))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .LOADRES (aq, rl, rs1, width, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zalrsc)) && (lrsc_width_valid width)) : Bool)
      then
        (pure (0b00010#5 +++ ((bool_bit_forwards aq) +++ ((bool_bit_forwards rl) +++ (0b00000#5 +++ ((encdec_reg_forwards
                      rs1) +++ (0#1 +++ ((width_enc_forwards width) +++ ((encdec_reg_forwards rd) +++ 0b0101111#7)))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .STORECON (aq, rl, rs2, rs1, width, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zalrsc)) && (lrsc_width_valid width)) : Bool)
      then
        (pure (0b00011#5 +++ ((bool_bit_forwards aq) +++ ((bool_bit_forwards rl) +++ ((encdec_reg_forwards
                    rs2) +++ ((encdec_reg_forwards rs1) +++ (0#1 +++ ((width_enc_forwards width) +++ ((encdec_reg_forwards
                            rd) +++ 0b0101111#7)))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MUL (rs2, rs1, rd, mul_op) =>
    (do
      if (((← (currentlyEnabled Ext_M)) || (← (currentlyEnabled Ext_Zmmul))) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ ((← (encdec_mul_op_forwards
                      mul_op)) +++ ((encdec_reg_forwards rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .DIV (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((← (currentlyEnabled Ext_M)) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b10#2 +++ ((bool_bit_forwards
                      is_unsigned) +++ ((encdec_reg_forwards rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .REM (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((← (currentlyEnabled Ext_M)) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b11#2 +++ ((bool_bit_forwards
                      is_unsigned) +++ ((encdec_reg_forwards rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MULW (rs2, rs1, rd) =>
    (do
      if (((xlen == 64) && ((← (currentlyEnabled Ext_M)) || (← (currentlyEnabled Ext_Zmmul)))) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0111011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_M))) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b10#2 +++ ((bool_bit_forwards
                      is_unsigned) +++ ((encdec_reg_forwards rd) +++ 0b0111011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_M))) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b11#2 +++ ((bool_bit_forwards
                      is_unsigned) +++ ((encdec_reg_forwards rd) +++ 0b0111011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SLLIUW (shamt, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zba)) && (xlen == 64)) : Bool)
      then
        (pure (0b000010#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0011011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBA_RTYPEUW (rs2, rs1, rd, b__0) =>
    (do
      if ((((← (currentlyEnabled Ext_Zba)) && (xlen == 64)) && (b__0 == (0b00#2 : (BitVec 2)))) : Bool)
      then
        (pure (0b0000100#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b00#2 +++ (0#1 +++ ((encdec_reg_forwards
                        rd) +++ 0b0111011#7)))))))
      else
        (do
          if (((← (currentlyEnabled Ext_Zba)) && ((xlen == 64) && (b__0 != 0b00#2))) : Bool)
          then
            (pure (0b0010000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ ((b__0 : (BitVec 2)) +++ (0#1 +++ ((encdec_reg_forwards
                            rd) +++ 0b0111011#7)))))))
          else
            (do
              «assert» false "Pattern match failure at unknown location"
              throw Error.Exit)))
  | .ZBA_RTYPE (rs2, rs1, rd, shamt) =>
    (do
      if (((shamt != 0b00#2) && (← (currentlyEnabled Ext_Zba))) : Bool)
      then
        (pure (0b0010000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ ((shamt : (BitVec 2)) +++ (0#1 +++ ((encdec_reg_forwards
                        rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RORIW (shamt, rs1, rd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zbb)) || (← (currentlyEnabled Ext_Zbkb))) && (xlen == 64)) : Bool)
      then
        (pure (0b0110000#7 +++ ((shamt : (BitVec 5)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0011011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RORI (shamt, rs1, rd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zbb)) || (← (currentlyEnabled Ext_Zbkb))) && ((xlen == 64) || ((BitVec.access
                 shamt 5) == 0#1))) : Bool)
      then
        (pure (0b011000#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPEW (rs2, rs1, rd, .ROLW) =>
    (do
      if ((((← (currentlyEnabled Ext_Zbb)) || (← (currentlyEnabled Ext_Zbkb))) && (xlen == 64)) : Bool)
      then
        (pure (0b0110000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0111011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPEW (rs2, rs1, rd, .RORW) =>
    (do
      if ((((← (currentlyEnabled Ext_Zbb)) || (← (currentlyEnabled Ext_Zbkb))) && (xlen == 64)) : Bool)
      then
        (pure (0b0110000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0111011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .ANDN) =>
    (do
      if (((← (currentlyEnabled Ext_Zbb)) || (← (currentlyEnabled Ext_Zbkb))) : Bool)
      then
        (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b111#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .ORN) =>
    (do
      if (((← (currentlyEnabled Ext_Zbb)) || (← (currentlyEnabled Ext_Zbkb))) : Bool)
      then
        (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b110#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .XNOR) =>
    (do
      if (((← (currentlyEnabled Ext_Zbb)) || (← (currentlyEnabled Ext_Zbkb))) : Bool)
      then
        (pure (0b0100000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .MAX) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0000101#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b110#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .MAXU) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0000101#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b111#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .MIN) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0000101#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .MINU) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0000101#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .ROL) =>
    (do
      if (((← (currentlyEnabled Ext_Zbb)) || (← (currentlyEnabled Ext_Zbkb))) : Bool)
      then
        (pure (0b0110000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_RTYPE (rs2, rs1, rd, .ROR) =>
    (do
      if (((← (currentlyEnabled Ext_Zbb)) || (← (currentlyEnabled Ext_Zbkb))) : Bool)
      then
        (pure (0b0110000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_EXTOP (rs1, rd, .SEXTB) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00100#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_EXTOP (rs1, rd, .SEXTH) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00101#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBB_EXTOP (rs1, rd, .ZEXTH) =>
    (do
      if (((← (currentlyEnabled Ext_Zbb)) && (xlen == 32)) : Bool)
      then
        (pure (0b0000100#7 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          if (((← (currentlyEnabled Ext_Zbb)) && (xlen == 64)) : Bool)
          then
            (pure (0b0000100#7 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                          rd) +++ 0b0111011#7))))))
          else
            (do
              «assert» false "Pattern match failure at unknown location"
              throw Error.Exit)))
  | .REV8 (rs1, rd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zbb)) || (← (currentlyEnabled Ext_Zbkb))) && (xlen == 32)) : Bool)
      then
        (pure (0b011010011000#12 +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                    rd) +++ 0b0010011#7)))))
      else
        (do
          if ((((← (currentlyEnabled Ext_Zbb)) || (← (currentlyEnabled Ext_Zbkb))) && (xlen == 64)) : Bool)
          then
            (pure (0b011010111000#12 +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0010011#7)))))
          else
            (do
              «assert» false "Pattern match failure at unknown location"
              throw Error.Exit)))
  | .ORCB (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b001010000111#12 +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                    rd) +++ 0b0010011#7)))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CPOP (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00010#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CPOPW (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zbb)) && (xlen == 64)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00010#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0011011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CLZ (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CLZW (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zbb)) && (xlen == 64)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0011011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CTZ (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zbb)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00001#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CTZW (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zbb)) && (xlen == 64)) : Bool)
      then
        (pure (0b0110000#7 +++ (0b00001#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0011011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CLMUL (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zbc)) || (← (currentlyEnabled Ext_Zbkc))) : Bool)
      then
        (pure (0b0000101#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CLMULH (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zbc)) || (← (currentlyEnabled Ext_Zbkc))) : Bool)
      then
        (pure (0b0000101#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b011#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CLMULR (rs2, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zbc)) : Bool)
      then
        (pure (0b0000101#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b010#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBS_IOP (shamt, rs1, rd, .BCLRI) =>
    (do
      if (((← (currentlyEnabled Ext_Zbs)) && ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))) : Bool)
      then
        (pure (0b010010#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBS_IOP (shamt, rs1, rd, .BEXTI) =>
    (do
      if (((← (currentlyEnabled Ext_Zbs)) && ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))) : Bool)
      then
        (pure (0b010010#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBS_IOP (shamt, rs1, rd, .BINVI) =>
    (do
      if (((← (currentlyEnabled Ext_Zbs)) && ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))) : Bool)
      then
        (pure (0b011010#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBS_IOP (shamt, rs1, rd, .BSETI) =>
    (do
      if (((← (currentlyEnabled Ext_Zbs)) && ((xlen == 64) || ((BitVec.access shamt 5) == 0#1))) : Bool)
      then
        (pure (0b001010#6 +++ ((shamt : (BitVec 6)) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBS_RTYPE (rs2, rs1, rd, .BCLR) =>
    (do
      if ((← (currentlyEnabled Ext_Zbs)) : Bool)
      then
        (pure (0b0100100#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBS_RTYPE (rs2, rs1, rd, .BEXT) =>
    (do
      if ((← (currentlyEnabled Ext_Zbs)) : Bool)
      then
        (pure (0b0100100#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBS_RTYPE (rs2, rs1, rd, .BINV) =>
    (do
      if ((← (currentlyEnabled Ext_Zbs)) : Bool)
      then
        (pure (0b0110100#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBS_RTYPE (rs2, rs1, rd, .BSET) =>
    (do
      if ((← (currentlyEnabled Ext_Zbs)) : Bool)
      then
        (pure (0b0010100#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .HLVTYPE (width, .HLV, is_unsigned, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_H)) && (valid_load_encdec width is_unsigned)) : Bool)
      then
        (pure (0b0110#4 +++ ((width_enc_forwards width) +++ (0b00000#5 +++ ((bool_bit_forwards
                    is_unsigned) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                          rd) +++ 0b1110011#7))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .HLVTYPE (width, .HLVX, true, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_H)) && ((width == 2) || (width == 4))) : Bool)
      then
        (pure (0b0110#4 +++ ((width_enc_forwards width) +++ (0b000011#6 +++ ((encdec_reg_forwards
                    rs1) +++ (0b100#3 +++ ((encdec_reg_forwards rd) +++ 0b1110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .HSV (width, rs1, rs2) =>
    (do
      if (((← (currentlyEnabled Ext_H)) && (width ≤b xlen_bytes)) : Bool)
      then
        (pure (0b0110#4 +++ ((width_enc_forwards width) +++ (1#1 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards
                      rs1) +++ (0b100#3 +++ (0b00000#5 +++ 0b1110011#7))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .HFENCE_VVMA (rs1, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_H)) : Bool)
      then
        (pure (0b0010001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .HFENCE_GVMA (rs1, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_H)) : Bool)
      then
        (pure (0b0110001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .LOAD_FP (imm, rs1, rd, width) =>
    (do
      if ((← (float_load_store_width_supported width)) : Bool)
      then
        (pure ((imm : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ (0#1 +++ ((width_enc_forwards
                    width) +++ ((encdec_freg_forwards rd) +++ 0b0000111#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .STORE_FP (imm, rs2, rs1, width) =>
    (do
      if ((← (float_load_store_width_supported width)) : Bool)
      then
        (pure ((Sail.BitVec.extractLsb imm 11 5) +++ ((encdec_freg_forwards rs2) +++ ((encdec_reg_forwards
                  rs1) +++ (0#1 +++ ((width_enc_forwards width) +++ ((Sail.BitVec.extractLsb imm 4 0) +++ 0b0100111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_MADD_TYPE_S (rs3, rs2, rs1, rm, rd, .FMADD_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure ((encdec_freg_forwards rs3) +++ (0b00#2 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards
                    rs1) +++ ((encdec_rounding_mode_forwards rm) +++ ((encdec_freg_forwards rd) +++ 0b1000011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_MADD_TYPE_S (rs3, rs2, rs1, rm, rd, .FMSUB_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure ((encdec_freg_forwards rs3) +++ (0b00#2 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards
                    rs1) +++ ((encdec_rounding_mode_forwards rm) +++ ((encdec_freg_forwards rd) +++ 0b1000111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_MADD_TYPE_S (rs3, rs2, rs1, rm, rd, .FNMSUB_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure ((encdec_freg_forwards rs3) +++ (0b00#2 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards
                    rs1) +++ ((encdec_rounding_mode_forwards rm) +++ ((encdec_freg_forwards rd) +++ 0b1001011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_MADD_TYPE_S (rs3, rs2, rs1, rm, rd, .FNMADD_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure ((encdec_freg_forwards rs3) +++ (0b00#2 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards
                    rs1) +++ ((encdec_rounding_mode_forwards rm) +++ ((encdec_freg_forwards rd) +++ 0b1001111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_RM_TYPE_S (rs2, rs1, rm, rd, .FADD_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b0000000#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_RM_TYPE_S (rs2, rs1, rm, rd, .FSUB_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b0000100#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_RM_TYPE_S (rs2, rs1, rm, rd, .FMUL_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b0001000#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_RM_TYPE_S (rs2, rs1, rm, rd, .FDIV_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b0001100#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FF_TYPE_S (rs1, rm, rd, .FSQRT_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b0101100#7 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FX_TYPE_S (rs1, rm, rd, .FCVT_W_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b1100000#7 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_reg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FX_TYPE_S (rs1, rm, rd, .FCVT_WU_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b1100000#7 +++ (0b00001#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_reg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_XF_TYPE_S (rs1, rm, rd, .FCVT_S_W) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b1101000#7 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_XF_TYPE_S (rs1, rm, rd, .FCVT_S_WU) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b1101000#7 +++ (0b00001#5 +++ ((encdec_reg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FX_TYPE_S (rs1, rm, rd, .FCVT_L_S) =>
    (do
      if (((← (haveSingleFPU ())) && (xlen ≥b 64)) : Bool)
      then
        (pure (0b1100000#7 +++ (0b00010#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_reg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FX_TYPE_S (rs1, rm, rd, .FCVT_LU_S) =>
    (do
      if (((← (haveSingleFPU ())) && (xlen ≥b 64)) : Bool)
      then
        (pure (0b1100000#7 +++ (0b00011#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_reg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_XF_TYPE_S (rs1, rm, rd, .FCVT_S_L) =>
    (do
      if (((← (haveSingleFPU ())) && (xlen ≥b 64)) : Bool)
      then
        (pure (0b1101000#7 +++ (0b00010#5 +++ ((encdec_reg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_XF_TYPE_S (rs1, rm, rd, .FCVT_S_LU) =>
    (do
      if (((← (haveSingleFPU ())) && (xlen ≥b 64)) : Bool)
      then
        (pure (0b1101000#7 +++ (0b00011#5 +++ ((encdec_reg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_TYPE_F_S (rs2, rs1, rd, .FSGNJ_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b0010000#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b000#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_TYPE_F_S (rs2, rs1, rd, .FSGNJN_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b0010000#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b001#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_TYPE_F_S (rs2, rs1, rd, .FSGNJX_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b0010000#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b010#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_TYPE_F_S (rs2, rs1, rd, .FMIN_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b0010100#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b000#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_TYPE_F_S (rs2, rs1, rd, .FMAX_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b0010100#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b001#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_TYPE_X_S (rs2, rs1, rd, .FEQ_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b1010000#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b010#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_TYPE_X_S (rs2, rs1, rd, .FLT_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b1010000#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_TYPE_X_S (rs2, rs1, rd, .FLE_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b1010000#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_TYPE_X_S (rs1, rd, .FCLASS_S) =>
    (do
      if ((← (haveSingleFPU ())) : Bool)
      then
        (pure (0b1110000#7 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_TYPE_X_S (rs1, rd, .FMV_X_W) =>
    (do
      if ((← (currentlyEnabled Ext_F)) : Bool)
      then
        (pure (0b1110000#7 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_TYPE_F_S (rs1, rd, .FMV_W_X) =>
    (do
      if ((← (currentlyEnabled Ext_F)) : Bool)
      then
        (pure (0b1111000#7 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_MADD_TYPE_D (rs3, rs2, rs1, rm, rd, .FMADD_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 4) #v[rd, rs1, rs2, rs3]))) : Bool)
      then
        (pure ((encdec_freg_forwards rs3) +++ (0b01#2 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards
                    rs1) +++ ((encdec_rounding_mode_forwards rm) +++ ((encdec_freg_forwards rd) +++ 0b1000011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_MADD_TYPE_D (rs3, rs2, rs1, rm, rd, .FMSUB_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 4) #v[rd, rs1, rs2, rs3]))) : Bool)
      then
        (pure ((encdec_freg_forwards rs3) +++ (0b01#2 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards
                    rs1) +++ ((encdec_rounding_mode_forwards rm) +++ ((encdec_freg_forwards rd) +++ 0b1000111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_MADD_TYPE_D (rs3, rs2, rs1, rm, rd, .FNMSUB_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 4) #v[rd, rs1, rs2, rs3]))) : Bool)
      then
        (pure ((encdec_freg_forwards rs3) +++ (0b01#2 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards
                    rs1) +++ ((encdec_rounding_mode_forwards rm) +++ ((encdec_freg_forwards rd) +++ 0b1001011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_MADD_TYPE_D (rs3, rs2, rs1, rm, rd, .FNMADD_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 4) #v[rd, rs1, rs2, rs3]))) : Bool)
      then
        (pure ((encdec_freg_forwards rs3) +++ (0b01#2 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards
                    rs1) +++ ((encdec_rounding_mode_forwards rm) +++ ((encdec_freg_forwards rd) +++ 0b1001111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_RM_TYPE_D (rs2, rs1, rm, rd, .FADD_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 3) #v[rd, rs1, rs2]))) : Bool)
      then
        (pure (0b0000001#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_RM_TYPE_D (rs2, rs1, rm, rd, .FSUB_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 3) #v[rd, rs1, rs2]))) : Bool)
      then
        (pure (0b0000101#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_RM_TYPE_D (rs2, rs1, rm, rd, .FMUL_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 3) #v[rd, rs1, rs2]))) : Bool)
      then
        (pure (0b0001001#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_RM_TYPE_D (rs2, rs1, rm, rd, .FDIV_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 3) #v[rd, rs1, rs2]))) : Bool)
      then
        (pure (0b0001101#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FF_TYPE_D (rs1, rm, rd, .FSQRT_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 2) #v[rd, rs1]))) : Bool)
      then
        (pure (0b0101101#7 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FX_TYPE_D (rs1, rm, rd, .FCVT_W_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 1) #v[rs1]))) : Bool)
      then
        (pure (0b1100001#7 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_reg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FX_TYPE_D (rs1, rm, rd, .FCVT_WU_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 1) #v[rs1]))) : Bool)
      then
        (pure (0b1100001#7 +++ (0b00001#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_reg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_XF_TYPE_D (rs1, rm, rd, .FCVT_D_W) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 1) #v[rd]))) : Bool)
      then
        (pure (0b1101001#7 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_XF_TYPE_D (rs1, rm, rd, .FCVT_D_WU) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 1) #v[rd]))) : Bool)
      then
        (pure (0b1101001#7 +++ (0b00001#5 +++ ((encdec_reg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FF_TYPE_D (rs1, rm, rd, .FCVT_S_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 1) #v[rs1]))) : Bool)
      then
        (pure (0b0100000#7 +++ (0b00001#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FF_TYPE_D (rs1, rm, rd, .FCVT_D_S) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 1) #v[rd]))) : Bool)
      then
        (pure (0b0100001#7 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FX_TYPE_D (rs1, rm, rd, .FCVT_L_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (xlen ≥b 64)) : Bool)
      then
        (pure (0b1100001#7 +++ (0b00010#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_reg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FX_TYPE_D (rs1, rm, rd, .FCVT_LU_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (xlen ≥b 64)) : Bool)
      then
        (pure (0b1100001#7 +++ (0b00011#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_reg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_XF_TYPE_D (rs1, rm, rd, .FCVT_D_L) =>
    (do
      if (((← (haveDoubleFPU ())) && (xlen ≥b 64)) : Bool)
      then
        (pure (0b1101001#7 +++ (0b00010#5 +++ ((encdec_reg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_XF_TYPE_D (rs1, rm, rd, .FCVT_D_LU) =>
    (do
      if (((← (haveDoubleFPU ())) && (xlen ≥b 64)) : Bool)
      then
        (pure (0b1101001#7 +++ (0b00011#5 +++ ((encdec_reg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_F_TYPE_D (rs2, rs1, rd, .FSGNJ_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 3) #v[rd, rs1, rs2]))) : Bool)
      then
        (pure (0b0010001#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b000#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_F_TYPE_D (rs2, rs1, rd, .FSGNJN_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 3) #v[rd, rs1, rs2]))) : Bool)
      then
        (pure (0b0010001#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b001#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_F_TYPE_D (rs2, rs1, rd, .FSGNJX_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 3) #v[rd, rs1, rs2]))) : Bool)
      then
        (pure (0b0010001#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b010#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_F_TYPE_D (rs2, rs1, rd, .FMIN_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 3) #v[rd, rs1, rs2]))) : Bool)
      then
        (pure (0b0010101#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b000#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_F_TYPE_D (rs2, rs1, rd, .FMAX_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 3) #v[rd, rs1, rs2]))) : Bool)
      then
        (pure (0b0010101#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b001#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_X_TYPE_D (rs2, rs1, rd, .FEQ_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 2) #v[rs1, rs2]))) : Bool)
      then
        (pure (0b1010001#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b010#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_X_TYPE_D (rs2, rs1, rd, .FLT_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 2) #v[rs1, rs2]))) : Bool)
      then
        (pure (0b1010001#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_X_TYPE_D (rs2, rs1, rd, .FLE_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 2) #v[rs1, rs2]))) : Bool)
      then
        (pure (0b1010001#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_X_TYPE_D (rs1, rd, .FCLASS_D) =>
    (do
      if (((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 1) #v[rs1]))) : Bool)
      then
        (pure (0b1110001#7 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_X_TYPE_D (rs1, rd, .FMV_X_D) =>
    (do
      if (((← (currentlyEnabled Ext_D)) && (xlen ≥b 64)) : Bool)
      then
        (pure (0b1110001#7 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_F_TYPE_D (rs1, rd, .FMV_D_X) =>
    (do
      if (((← (currentlyEnabled Ext_D)) && (xlen ≥b 64)) : Bool)
      then
        (pure (0b1111001#7 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_RM_TYPE_H (rs2, rs1, rm, rd, .FADD_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b0000010#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_RM_TYPE_H (rs2, rs1, rm, rd, .FSUB_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b0000110#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_RM_TYPE_H (rs2, rs1, rm, rd, .FMUL_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b0001010#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_RM_TYPE_H (rs2, rs1, rm, rd, .FDIV_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b0001110#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_MADD_TYPE_H (rs3, rs2, rs1, rm, rd, .FMADD_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure ((encdec_freg_forwards rs3) +++ (0b10#2 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards
                    rs1) +++ ((encdec_rounding_mode_forwards rm) +++ ((encdec_freg_forwards rd) +++ 0b1000011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_MADD_TYPE_H (rs3, rs2, rs1, rm, rd, .FMSUB_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure ((encdec_freg_forwards rs3) +++ (0b10#2 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards
                    rs1) +++ ((encdec_rounding_mode_forwards rm) +++ ((encdec_freg_forwards rd) +++ 0b1000111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_MADD_TYPE_H (rs3, rs2, rs1, rm, rd, .FNMSUB_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure ((encdec_freg_forwards rs3) +++ (0b10#2 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards
                    rs1) +++ ((encdec_rounding_mode_forwards rm) +++ ((encdec_freg_forwards rd) +++ 0b1001011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_MADD_TYPE_H (rs3, rs2, rs1, rm, rd, .FNMADD_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure ((encdec_freg_forwards rs3) +++ (0b10#2 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards
                    rs1) +++ ((encdec_rounding_mode_forwards rm) +++ ((encdec_freg_forwards rd) +++ 0b1001111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_F_TYPE_H (rs2, rs1, rd, .FSGNJ_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b0010010#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b000#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_F_TYPE_H (rs2, rs1, rd, .FSGNJN_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b0010010#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b001#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_F_TYPE_H (rs2, rs1, rd, .FSGNJX_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b0010010#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b010#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_F_TYPE_H (rs2, rs1, rd, .FMIN_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b0010110#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b000#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_F_TYPE_H (rs2, rs1, rd, .FMAX_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b0010110#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b001#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_X_TYPE_H (rs2, rs1, rd, .FEQ_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b1010010#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b010#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_X_TYPE_H (rs2, rs1, rd, .FLT_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b1010010#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_BIN_X_TYPE_H (rs2, rs1, rd, .FLE_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b1010010#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FF_TYPE_H (rs1, rm, rd, .FSQRT_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b0101110#7 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FX_TYPE_H (rs1, rm, rd, .FCVT_W_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b1100010#7 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_reg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FX_TYPE_H (rs1, rm, rd, .FCVT_WU_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b1100010#7 +++ (0b00001#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_reg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_XF_TYPE_H (rs1, rm, rd, .FCVT_H_W) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b1101010#7 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_XF_TYPE_H (rs1, rm, rd, .FCVT_H_WU) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b1101010#7 +++ (0b00001#5 +++ ((encdec_reg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FF_TYPE_H (rs1, rm, rd, .FCVT_H_S) =>
    (do
      if ((← (haveHalfMin ())) : Bool)
      then
        (pure (0b0100010#7 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FF_TYPE_H (rs1, rm, rd, .FCVT_H_D) =>
    (do
      if (((← (haveHalfMin ())) && ((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 1)
                 #v[rs1])))) : Bool)
      then
        (pure (0b0100010#7 +++ (0b00001#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FF_TYPE_H (rs1, rm, rd, .FCVT_S_H) =>
    (do
      if ((← (haveHalfMin ())) : Bool)
      then
        (pure (0b0100000#7 +++ (0b00010#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FF_TYPE_H (rs1, rm, rd, .FCVT_D_H) =>
    (do
      if (((← (haveHalfMin ())) && ((← (haveDoubleFPU ())) && (← (validDoubleRegs (n := 1)
                 #v[rd])))) : Bool)
      then
        (pure (0b0100001#7 +++ (0b00010#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FX_TYPE_H (rs1, rm, rd, .FCVT_L_H) =>
    (do
      if (((← (haveHalfFPU ())) && (xlen ≥b 64)) : Bool)
      then
        (pure (0b1100010#7 +++ (0b00010#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_reg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_FX_TYPE_H (rs1, rm, rd, .FCVT_LU_H) =>
    (do
      if (((← (haveHalfFPU ())) && (xlen ≥b 64)) : Bool)
      then
        (pure (0b1100010#7 +++ (0b00011#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_reg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_XF_TYPE_H (rs1, rm, rd, .FCVT_H_L) =>
    (do
      if (((← (haveHalfFPU ())) && (xlen ≥b 64)) : Bool)
      then
        (pure (0b1101010#7 +++ (0b00010#5 +++ ((encdec_reg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_RM_XF_TYPE_H (rs1, rm, rd, .FCVT_H_LU) =>
    (do
      if (((← (haveHalfFPU ())) && (xlen ≥b 64)) : Bool)
      then
        (pure (0b1101010#7 +++ (0b00011#5 +++ ((encdec_reg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_X_TYPE_H (rs1, rd, .FCLASS_H) =>
    (do
      if ((← (haveHalfFPU ())) : Bool)
      then
        (pure (0b1110010#7 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_X_TYPE_H (rs1, rd, .FMV_X_H) =>
    (do
      if (((← (currentlyEnabled Ext_Zfhmin)) || (← (currentlyEnabled Ext_Zfbfmin))) : Bool)
      then
        (pure (0b1110010#7 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_UN_F_TYPE_H (rs1, rd, .FMV_H_X) =>
    (do
      if (((← (currentlyEnabled Ext_Zfhmin)) || (← (currentlyEnabled Ext_Zfbfmin))) : Bool)
      then
        (pure (0b1111010#7 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FLI_H (constantidx, rd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zfh)) || (← (currentlyEnabled Ext_Zvfh))) && (← (currentlyEnabled
               Ext_Zfa))) : Bool)
      then
        (pure (0b1111010#7 +++ (0b00001#5 +++ ((constantidx : (BitVec 5)) +++ (0b000#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FLI_S (constantidx, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zfa)) : Bool)
      then
        (pure (0b1111000#7 +++ (0b00001#5 +++ ((constantidx : (BitVec 5)) +++ (0b000#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FLI_D (constantidx, rd) =>
    (do
      if (((← (currentlyEnabled Ext_D)) && (← (currentlyEnabled Ext_Zfa))) : Bool)
      then
        (pure (0b1111001#7 +++ (0b00001#5 +++ ((constantidx : (BitVec 5)) +++ (0b000#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FMINM_H (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zfh)) && (← (currentlyEnabled Ext_Zfa))) : Bool)
      then
        (pure (0b0010110#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b010#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FMAXM_H (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zfh)) && (← (currentlyEnabled Ext_Zfa))) : Bool)
      then
        (pure (0b0010110#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b011#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FMINM_S (rs2, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zfa)) : Bool)
      then
        (pure (0b0010100#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b010#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FMAXM_S (rs2, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zfa)) : Bool)
      then
        (pure (0b0010100#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b011#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FMINM_D (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_D)) && (← (currentlyEnabled Ext_Zfa))) : Bool)
      then
        (pure (0b0010101#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b010#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FMAXM_D (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_D)) && (← (currentlyEnabled Ext_Zfa))) : Bool)
      then
        (pure (0b0010101#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b011#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FROUND_H (rs1, rm, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zfh)) && (← (currentlyEnabled Ext_Zfa))) : Bool)
      then
        (pure (0b0100010#7 +++ (0b00100#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FROUNDNX_H (rs1, rm, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zfh)) && (← (currentlyEnabled Ext_Zfa))) : Bool)
      then
        (pure (0b0100010#7 +++ (0b00101#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FROUND_S (rs1, rm, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zfa)) : Bool)
      then
        (pure (0b0100000#7 +++ (0b00100#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FROUNDNX_S (rs1, rm, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zfa)) : Bool)
      then
        (pure (0b0100000#7 +++ (0b00101#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FROUND_D (rs1, rm, rd) =>
    (do
      if (((← (currentlyEnabled Ext_D)) && (← (currentlyEnabled Ext_Zfa))) : Bool)
      then
        (pure (0b0100001#7 +++ (0b00100#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FROUNDNX_D (rs1, rm, rd) =>
    (do
      if (((← (currentlyEnabled Ext_D)) && (← (currentlyEnabled Ext_Zfa))) : Bool)
      then
        (pure (0b0100001#7 +++ (0b00101#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                    rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FMVH_X_D (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_D)) && ((← (currentlyEnabled Ext_Zfa)) && (← (in32BitMode
                 ())))) : Bool)
      then
        (pure (0b1110001#7 +++ (0b00001#5 +++ ((encdec_freg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FMVP_D_X (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_D)) && ((← (currentlyEnabled Ext_Zfa)) && (← (in32BitMode
                 ())))) : Bool)
      then
        (pure (0b1011001#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_freg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FLEQ_H (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zfh)) && (← (currentlyEnabled Ext_Zfa))) : Bool)
      then
        (pure (0b1010010#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FLTQ_H (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zfh)) && (← (currentlyEnabled Ext_Zfa))) : Bool)
      then
        (pure (0b1010010#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FLEQ_S (rs2, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zfa)) : Bool)
      then
        (pure (0b1010000#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FLTQ_S (rs2, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zfa)) : Bool)
      then
        (pure (0b1010000#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FLEQ_D (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_D)) && (← (currentlyEnabled Ext_Zfa))) : Bool)
      then
        (pure (0b1010001#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FLTQ_D (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_D)) && (← (currentlyEnabled Ext_Zfa))) : Bool)
      then
        (pure (0b1010001#7 +++ ((encdec_freg_forwards rs2) +++ ((encdec_freg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FCVTMOD_W_D (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_D)) && (← (currentlyEnabled Ext_Zfa))) : Bool)
      then
        (pure (0b1100001#7 +++ (0b01000#5 +++ ((encdec_freg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VSETVLI (vtr, ma, ta, sew, lmul, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zve32x)) : Bool)
      then
        (pure (0#1 +++ ((vtr : (BitVec 3)) +++ ((ma : (BitVec 1)) +++ ((ta : (BitVec 1)) +++ ((sew : (BitVec 3)) +++ ((lmul : (BitVec 3)) +++ ((encdec_reg_forwards
                          rs1) +++ (0b111#3 +++ ((encdec_reg_forwards rd) +++ 0b1010111#7))))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VSETVL (rs2, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zve32x)) : Bool)
      then
        (pure (0b1000000#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b111#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b1010111#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VSETIVLI (v__18, ma, ta, sew, lmul, uimm, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zve32x)) && ((Sail.BitVec.extractLsb v__18 2 2) == (0#1 : (BitVec 1)))) : Bool)
      then
        (let vtr : (BitVec 2) := (Sail.BitVec.extractLsb v__18 1 0)
        (pure (0b11#2 +++ ((vtr : (BitVec 2)) +++ ((ma : (BitVec 1)) +++ ((ta : (BitVec 1)) +++ ((sew : (BitVec 3)) +++ ((lmul : (BitVec 3)) +++ ((uimm : (BitVec 5)) +++ (0b111#3 +++ ((encdec_reg_forwards
                              rd) +++ 0b1010111#7)))))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VVTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure (((← (get_sew ())) ≤b 64) && (← (valid_wide_vvtype funct6))))))) : Bool)
      then
        (pure ((encdec_vvfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .NVSTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 16)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 32))))) : Bool)
      then
        (pure ((encdec_nvsfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .NVTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 16)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 32))))) : Bool)
      then
        (pure ((encdec_nvfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MASKTYPEV (vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010111#6 +++ (0#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MOVETYPEV (vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010111#6 +++ (1#1 +++ (0b00000#5 +++ ((encdec_vreg_forwards vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VXTYPE (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure (((← (get_sew ())) ≤b 64) && (← (valid_wide_vxtype funct6))))))) : Bool)
      then
        (pure ((encdec_vxfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .NXSTYPE (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 16)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 32))))) : Bool)
      then
        (pure ((encdec_nxsfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .NXTYPE (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 16)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 32))))) : Bool)
      then
        (pure ((encdec_nxfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VXSG (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_vxsgfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MASKTYPEX (vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010111#6 +++ (0#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MOVETYPEX (rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010111#6 +++ (1#1 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VITYPE (funct6, vm, vs2, simm, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_vifunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((simm : (BitVec 5)) +++ (0b011#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .NISTYPE (funct6, vm, vs2, uimm, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 16)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 32))))) : Bool)
      then
        (pure ((encdec_nisfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((uimm : (BitVec 5)) +++ (0b011#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .NITYPE (funct6, vm, vs2, uimm, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 16)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 32))))) : Bool)
      then
        (pure ((encdec_nifunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((uimm : (BitVec 5)) +++ (0b011#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VISG (funct6, vm, vs2, simm, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_visgfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((simm : (BitVec 5)) +++ (0b011#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MASKTYPEI (vs2, simm, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010111#6 +++ (0#1 +++ ((encdec_vreg_forwards vs2) +++ ((simm : (BitVec 5)) +++ (0b011#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MOVETYPEI (vd, simm) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010111#6 +++ (1#1 +++ (0b00000#5 +++ ((simm : (BitVec 5)) +++ (0b011#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VMVRTYPE (vs2, nreg, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b100111#6 +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_nreg_backwards nreg) +++ (0b011#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure (((← (get_sew ())) ≤b 64) && (← (valid_wide_mvvtype funct6))))))) : Bool)
      then
        (pure ((encdec_mvvfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MVVMATYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_mvvmafunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .WVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 16)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 32))))) : Bool)
      then
        (pure ((encdec_wvvfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .WVTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 16)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 32))))) : Bool)
      then
        (pure ((encdec_wvfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .WMVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 16)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 32))))) : Bool)
      then
        (pure ((encdec_wmvvfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VEXTTYPE (funct6, vm, vs2, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010010#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((vext_vs1_forwards
                    funct6) +++ (0b010#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VMVXS (vs2, rd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010000#6 +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ (0b00000#5 +++ (0b010#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MVVCOMPRESS (vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010111#6 +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MVXTYPE (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure (((← (get_sew ())) ≤b 64) && (← (valid_wide_mvxtype funct6))))))) : Bool)
      then
        (pure ((encdec_mvxfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_reg_forwards rs1) +++ (0b110#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MVXMATYPE (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_mvxmafunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_reg_forwards rs1) +++ (0b110#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .WVXTYPE (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 16)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 32))))) : Bool)
      then
        (pure ((encdec_wvxfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_reg_forwards rs1) +++ (0b110#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .WXTYPE (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 16)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 32))))) : Bool)
      then
        (pure ((encdec_wxfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_reg_forwards rs1) +++ (0b110#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .WMVXTYPE (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 16)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 32))))) : Bool)
      then
        (pure ((encdec_wmvxfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_reg_forwards rs1) +++ (0b110#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VMVSX (rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010000#6 +++ (1#1 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b110#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
                 (pure ((← (get_sew ())) == 64)))))) : Bool)
      then
        (pure ((encdec_fvvfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b001#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FVVMATYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
                 (pure ((← (get_sew ())) == 64)))))) : Bool)
      then
        (pure ((encdec_fvvmafunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b001#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FWVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
               (pure ((← (get_sew ())) == 32))))) : Bool)
      then
        (pure ((encdec_fwvvfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b001#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FWVVMATYPE (funct6, vm, vs1, vs2, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
               (pure ((← (get_sew ())) == 32))))) : Bool)
      then
        (pure ((encdec_fwvvmafunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs1) +++ ((encdec_vreg_forwards vs2) +++ (0b001#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FWVTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
               (pure ((← (get_sew ())) == 32))))) : Bool)
      then
        (pure ((encdec_fwvfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b001#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VFUNARY0 (vm, vs2, vfunary0, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
                 (pure ((← (get_sew ())) == 64)))))) : Bool)
      then
        (pure (0b010010#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vfunary0_vs1_forwards
                    vfunary0) +++ (0b001#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VFWUNARY0 (vm, vs2, vfwunary0, vd) =>
    (do
      if ((← (valid_widening_fp_conversion vfwunary0)) : Bool)
      then
        (pure (0b010010#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vfwunary0_vs1_forwards
                    vfwunary0) +++ (0b001#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VFNUNARY0 (vm, vs2, vfnunary0, vd) =>
    (do
      if ((← (valid_narrowing_fp_conversion vfnunary0)) : Bool)
      then
        (pure (0b010010#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vfnunary0_vs1_forwards
                    vfnunary0) +++ (0b001#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VFUNARY1 (vm, vs2, vfunary1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
                 (pure ((← (get_sew ())) == 64)))))) : Bool)
      then
        (pure (0b010011#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vfunary1_vs1_forwards
                    vfunary1) +++ (0b001#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VFMVFS (vs2, rd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
                 (pure ((← (get_sew ())) == 64)))))) : Bool)
      then
        (pure (0b010000#6 +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ (0b00000#5 +++ (0b001#3 +++ ((encdec_freg_forwards
                        rd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FVFTYPE (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
                 (pure ((← (get_sew ())) == 64)))))) : Bool)
      then
        (pure ((encdec_fvffunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_freg_forwards rs1) +++ (0b101#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FVFMATYPE (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
                 (pure ((← (get_sew ())) == 64)))))) : Bool)
      then
        (pure ((encdec_fvfmafunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_freg_forwards rs1) +++ (0b101#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FWVFTYPE (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
               (pure ((← (get_sew ())) == 32))))) : Bool)
      then
        (pure ((encdec_fwvffunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_freg_forwards rs1) +++ (0b101#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FWVFMATYPE (funct6, vm, rs1, vs2, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
               (pure ((← (get_sew ())) == 32))))) : Bool)
      then
        (pure ((encdec_fwvfmafunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_freg_forwards rs1) +++ (0b101#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FWFTYPE (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
               (pure ((← (get_sew ())) == 32))))) : Bool)
      then
        (pure ((encdec_fwffunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_freg_forwards rs1) +++ (0b101#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VFMERGE (vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
                 (pure ((← (get_sew ())) == 64)))))) : Bool)
      then
        (pure (0b010111#6 +++ (0#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_freg_forwards rs1) +++ (0b101#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VFMV (rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
                 (pure ((← (get_sew ())) == 64)))))) : Bool)
      then
        (pure (0b010111#6 +++ (1#1 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ (0b101#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VFMVSF (rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
                 (pure ((← (get_sew ())) == 64)))))) : Bool)
      then
        (pure (0b010000#6 +++ (1#1 +++ (0b00000#5 +++ ((encdec_freg_forwards rs1) +++ (0b101#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VLSEGTYPE (nf, vm, rs1, width, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (((vlewidth_pow_forwards width) ≤b 5) : Bool)) || ((← (currentlyEnabled
                 Ext_Zve64x)) && (((vlewidth_pow_forwards width) ≤b 6) : Bool))) : Bool)
      then
        (pure ((encdec_nfields_backwards nf) +++ (0#1 +++ (0b00#2 +++ ((vm : (BitVec 1)) +++ (0b00000#5 +++ ((encdec_reg_forwards
                        rs1) +++ ((encdec_vlewidth_forwards width) +++ ((encdec_vreg_forwards vd) +++ 0b0000111#7)))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VLSEGFFTYPE (nf, vm, rs1, width, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (((vlewidth_pow_forwards width) ≤b 5) : Bool)) || ((← (currentlyEnabled
                 Ext_Zve64x)) && (((vlewidth_pow_forwards width) ≤b 6) : Bool))) : Bool)
      then
        (pure ((encdec_nfields_backwards nf) +++ (0#1 +++ (0b00#2 +++ ((vm : (BitVec 1)) +++ (0b10000#5 +++ ((encdec_reg_forwards
                        rs1) +++ ((encdec_vlewidth_forwards width) +++ ((encdec_vreg_forwards vd) +++ 0b0000111#7)))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VSSEGTYPE (nf, vm, rs1, width, vs3) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (((vlewidth_pow_forwards width) ≤b 5) : Bool)) || ((← (currentlyEnabled
                 Ext_Zve64x)) && (((vlewidth_pow_forwards width) ≤b 6) : Bool))) : Bool)
      then
        (pure ((encdec_nfields_backwards nf) +++ (0#1 +++ (0b00#2 +++ ((vm : (BitVec 1)) +++ (0b00000#5 +++ ((encdec_reg_forwards
                        rs1) +++ ((encdec_vlewidth_forwards width) +++ ((encdec_vreg_forwards vs3) +++ 0b0100111#7)))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VLSSEGTYPE (nf, vm, rs2, rs1, width, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (((vlewidth_pow_forwards width) ≤b 5) : Bool)) || ((← (currentlyEnabled
                 Ext_Zve64x)) && (((vlewidth_pow_forwards width) ≤b 6) : Bool))) : Bool)
      then
        (pure ((encdec_nfields_backwards nf) +++ (0#1 +++ (0b10#2 +++ ((vm : (BitVec 1)) +++ ((encdec_reg_forwards
                      rs2) +++ ((encdec_reg_forwards rs1) +++ ((encdec_vlewidth_forwards width) +++ ((encdec_vreg_forwards
                            vd) +++ 0b0000111#7)))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VSSSEGTYPE (nf, vm, rs2, rs1, width, vs3) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (((vlewidth_pow_forwards width) ≤b 5) : Bool)) || ((← (currentlyEnabled
                 Ext_Zve64x)) && (((vlewidth_pow_forwards width) ≤b 6) : Bool))) : Bool)
      then
        (pure ((encdec_nfields_backwards nf) +++ (0#1 +++ (0b10#2 +++ ((vm : (BitVec 1)) +++ ((encdec_reg_forwards
                      rs2) +++ ((encdec_reg_forwards rs1) +++ ((encdec_vlewidth_forwards width) +++ ((encdec_vreg_forwards
                            vs3) +++ 0b0100111#7)))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VLXSEGTYPE (nf, vm, vs2, rs1, width, vd, mop) =>
    (do
      if (((← (currentlyEnabled Ext_Zve32x)) && (((vlewidth_pow_forwards width) ≤b max_index_eew_exp) : Bool)) : Bool)
      then
        (pure ((encdec_nfields_backwards nf) +++ (0#1 +++ ((encdec_indexed_mop_forwards mop) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                      vs2) +++ ((encdec_reg_forwards rs1) +++ ((encdec_vlewidth_forwards width) +++ ((encdec_vreg_forwards
                            vd) +++ 0b0000111#7)))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VSXSEGTYPE (nf, vm, vs2, rs1, width, vs3, mop) =>
    (do
      if (((← (currentlyEnabled Ext_Zve32x)) && (((vlewidth_pow_forwards width) ≤b max_index_eew_exp) : Bool)) : Bool)
      then
        (pure ((encdec_nfields_backwards nf) +++ (0#1 +++ ((encdec_indexed_mop_forwards mop) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                      vs2) +++ ((encdec_reg_forwards rs1) +++ ((encdec_vlewidth_forwards width) +++ ((encdec_vreg_forwards
                            vs3) +++ 0b0100111#7)))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VLRETYPE (nf, rs1, width, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (((vlewidth_pow_forwards width) ≤b 5) : Bool)) || ((← (currentlyEnabled
                 Ext_Zve64x)) && (((vlewidth_pow_forwards width) ≤b 6) : Bool))) : Bool)
      then
        (pure ((encdec_nfields_pow2_backwards nf) +++ (0#1 +++ (0b00#2 +++ (1#1 +++ (0b01000#5 +++ ((encdec_reg_forwards
                        rs1) +++ ((encdec_vlewidth_forwards width) +++ ((encdec_vreg_forwards vd) +++ 0b0000111#7)))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VSRETYPE (nf, rs1, vs3) =>
    (do
      if ((← (currentlyEnabled Ext_Zve32x)) : Bool)
      then
        (pure ((encdec_nfields_pow2_backwards nf) +++ (0#1 +++ (0b00#2 +++ (1#1 +++ (0b01000#5 +++ ((encdec_reg_forwards
                        rs1) +++ (0b000#3 +++ ((encdec_vreg_forwards vs3) +++ 0b0100111#7)))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VMTYPE (rs1, vd_or_vs3, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zve32x)) : Bool)
      then
        (pure (0b000#3 +++ (0#1 +++ (0b00#2 +++ (1#1 +++ (0b01011#5 +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_vreg_forwards
                            vd_or_vs3) +++ (encdec_lsop_forwards op))))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MMTYPE (funct6, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_mmfunct6_forwards funct6) +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards
                    vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VCPOP_M (vm, vs2, rd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010000#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ (0b10000#5 +++ (0b010#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VFIRST_M (vm, vs2, rd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010000#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ (0b10001#5 +++ (0b010#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VMSBF_M (vm, vs2, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010100#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ (0b00001#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VMSIF_M (vm, vs2, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010100#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ (0b00011#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VMSOF_M (vm, vs2, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010100#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ (0b00010#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VIOTA_M (vm, vs2, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010100#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ (0b10000#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VID_V (vm, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure (0b010100#6 +++ ((vm : (BitVec 1)) +++ (0b00000#5 +++ (0b10001#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VVMTYPE (funct6, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_vvmfunct6_forwards funct6) +++ (0#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards
                    vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VVMCTYPE (funct6, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_vvmcfunct6_forwards funct6) +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards
                    vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VVMSTYPE (funct6, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_vvmsfunct6_forwards funct6) +++ (0#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards
                    vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VVCMPTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_vvcmpfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VXMTYPE (funct6, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_vxmfunct6_forwards funct6) +++ (0#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VXMCTYPE (funct6, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_vxmcfunct6_forwards funct6) +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VXMSTYPE (funct6, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_vxmsfunct6_forwards funct6) +++ (0#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VXCMPTYPE (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_vxcmpfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VIMTYPE (funct6, vs2, simm, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_vimfunct6_forwards funct6) +++ (0#1 +++ ((encdec_vreg_forwards vs2) +++ ((simm : (BitVec 5)) +++ (0b011#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VIMCTYPE (funct6, vs2, simm, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_vimcfunct6_forwards funct6) +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ ((simm : (BitVec 5)) +++ (0b011#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VIMSTYPE (funct6, vs2, simm, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_vimsfunct6_forwards funct6) +++ (0#1 +++ ((encdec_vreg_forwards vs2) +++ ((simm : (BitVec 5)) +++ (0b011#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VICMPTYPE (funct6, vm, vs2, simm, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_vicmpfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((simm : (BitVec 5)) +++ (0b011#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FVVMTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
                 (pure ((← (get_sew ())) == 64)))))) : Bool)
      then
        (pure ((encdec_fvvmfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b001#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FVFMTYPE (funct6, vm, vs2, rs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
                 (pure ((← (get_sew ())) == 64)))))) : Bool)
      then
        (pure ((encdec_fvfmfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_freg_forwards rs1) +++ (0b101#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RIVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 16)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 32))))) : Bool)
      then
        (pure ((encdec_rivvfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RMVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zve32x)) && (← do
               (pure ((← (get_sew ())) ≤b 32)))) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
               (pure ((← (get_sew ())) ≤b 64))))) : Bool)
      then
        (pure ((encdec_rmvvfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RFVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || (((← (currentlyEnabled Ext_Zve32f)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
                 (pure ((← (get_sew ())) == 64)))))) : Bool)
      then
        (pure ((encdec_rfvvfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b001#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RFWVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zvfh)) && (← do
               (pure ((← (get_sew ())) == 16)))) || ((← (currentlyEnabled Ext_Zve64d)) && (← do
               (pure ((← (get_sew ())) == 32))))) : Bool)
      then
        (pure ((encdec_rfwvvfunct6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b001#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHA256SUM0 (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zknh)) : Bool)
      then
        (pure (0b00#2 +++ (0b01000#5 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0010011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHA256SUM1 (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zknh)) : Bool)
      then
        (pure (0b00#2 +++ (0b01000#5 +++ (0b00001#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0010011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHA256SIG0 (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zknh)) : Bool)
      then
        (pure (0b00#2 +++ (0b01000#5 +++ (0b00010#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0010011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHA256SIG1 (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zknh)) : Bool)
      then
        (pure (0b00#2 +++ (0b01000#5 +++ (0b00011#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0010011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .AES32ESMI (bs, rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zkne)) && (xlen == 32)) : Bool)
      then
        (pure ((bs : (BitVec 2)) +++ (0b10011#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b000#3 +++ ((encdec_reg_forwards rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .AES32ESI (bs, rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zkne)) && (xlen == 32)) : Bool)
      then
        (pure ((bs : (BitVec 2)) +++ (0b10001#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b000#3 +++ ((encdec_reg_forwards rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .AES32DSMI (bs, rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknd)) && (xlen == 32)) : Bool)
      then
        (pure ((bs : (BitVec 2)) +++ (0b10111#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b000#3 +++ ((encdec_reg_forwards rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .AES32DSI (bs, rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknd)) && (xlen == 32)) : Bool)
      then
        (pure ((bs : (BitVec 2)) +++ (0b10101#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b000#3 +++ ((encdec_reg_forwards rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHA512SUM0R (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknh)) && (xlen == 32)) : Bool)
      then
        (pure (0b01#2 +++ (0b01000#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHA512SUM1R (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknh)) && (xlen == 32)) : Bool)
      then
        (pure (0b01#2 +++ (0b01001#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHA512SIG0L (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknh)) && (xlen == 32)) : Bool)
      then
        (pure (0b01#2 +++ (0b01010#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHA512SIG0H (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknh)) && (xlen == 32)) : Bool)
      then
        (pure (0b01#2 +++ (0b01110#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHA512SIG1L (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknh)) && (xlen == 32)) : Bool)
      then
        (pure (0b01#2 +++ (0b01011#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHA512SIG1H (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknh)) && (xlen == 32)) : Bool)
      then
        (pure (0b01#2 +++ (0b01111#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .AES64KS1I (rnum, rs1, rd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zkne)) || (← (currentlyEnabled Ext_Zknd))) && ((xlen == 64) && (zopz0zI_u
               rnum 0xB#4))) : Bool)
      then
        (pure (0b00#2 +++ (0b11000#5 +++ (1#1 +++ ((rnum : (BitVec 4)) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                          rd) +++ 0b0010011#7))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .AES64IM (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknd)) && (xlen == 64)) : Bool)
      then
        (pure (0b00#2 +++ (0b11000#5 +++ (0b00000#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0010011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .AES64KS2 (rs2, rs1, rd) =>
    (do
      if ((((← (currentlyEnabled Ext_Zkne)) || (← (currentlyEnabled Ext_Zknd))) && (xlen == 64)) : Bool)
      then
        (pure (0b01#2 +++ (0b11111#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .AES64ESM (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zkne)) && (xlen == 64)) : Bool)
      then
        (pure (0b00#2 +++ (0b11011#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .AES64ES (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zkne)) && (xlen == 64)) : Bool)
      then
        (pure (0b00#2 +++ (0b11001#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .AES64DSM (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknd)) && (xlen == 64)) : Bool)
      then
        (pure (0b00#2 +++ (0b11111#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .AES64DS (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknd)) && (xlen == 64)) : Bool)
      then
        (pure (0b00#2 +++ (0b11101#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHA512SUM0 (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknh)) && (xlen == 64)) : Bool)
      then
        (pure (0b00#2 +++ (0b01000#5 +++ (0b00100#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0010011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHA512SUM1 (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknh)) && (xlen == 64)) : Bool)
      then
        (pure (0b00#2 +++ (0b01000#5 +++ (0b00101#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0010011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHA512SIG0 (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknh)) && (xlen == 64)) : Bool)
      then
        (pure (0b00#2 +++ (0b01000#5 +++ (0b00110#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0010011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHA512SIG1 (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zknh)) && (xlen == 64)) : Bool)
      then
        (pure (0b00#2 +++ (0b01000#5 +++ (0b00111#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0010011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SM3P0 (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zksh)) : Bool)
      then
        (pure (0b00#2 +++ (0b01000#5 +++ (0b01000#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0010011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SM3P1 (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zksh)) : Bool)
      then
        (pure (0b00#2 +++ (0b01000#5 +++ (0b01001#5 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                        rd) +++ 0b0010011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SM4ED (bs, rs2, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zksed)) : Bool)
      then
        (pure ((bs : (BitVec 2)) +++ (0b11000#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b000#3 +++ ((encdec_reg_forwards rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SM4KS (bs, rs2, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zksed)) : Bool)
      then
        (pure ((bs : (BitVec 2)) +++ (0b11010#5 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b000#3 +++ ((encdec_reg_forwards rd) +++ 0b0110011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBKB_RTYPE (rs2, rs1, rd, .PACK) =>
    (do
      if ((← (currentlyEnabled Ext_Zbkb)) : Bool)
      then
        (pure (0b0000100#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBKB_RTYPE (rs2, rs1, rd, .PACKH) =>
    (do
      if ((← (currentlyEnabled Ext_Zbkb)) : Bool)
      then
        (pure (0b0000100#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b111#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZBKB_PACKW (rs2, rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zbkb)) && (xlen == 64)) : Bool)
      then
        (pure (0b0000100#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0111011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZIP (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zbkb)) && (xlen == 32)) : Bool)
      then
        (pure (0b000010001111#12 +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                    rd) +++ 0b0010011#7)))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .UNZIP (rs1, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zbkb)) && (xlen == 32)) : Bool)
      then
        (pure (0b000010001111#12 +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                    rd) +++ 0b0010011#7)))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .BREV8 (rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zbkb)) : Bool)
      then
        (pure (0b011010000111#12 +++ ((encdec_reg_forwards rs1) +++ (0b101#3 +++ ((encdec_reg_forwards
                    rd) +++ 0b0010011#7)))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .XPERM8 (rs2, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zbkx)) : Bool)
      then
        (pure (0b0010100#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .XPERM4 (rs2, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zbkx)) : Bool)
      then
        (pure (0b0010100#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b010#3 +++ ((encdec_reg_forwards
                      rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VANDN_VV (vm, vs1, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b000001#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards
                    vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VANDN_VX (vm, vs2, rs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b000001#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VBREV_V (vm, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvbb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b010010#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ (0b01010#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VBREV8_V (vm, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b010010#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ (0b01000#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VREV8_V (vm, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b010010#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ (0b01001#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VCLZ_V (vm, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvbb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b010010#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ (0b01100#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VCTZ_V (vm, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvbb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b010010#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ (0b01101#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VCPOP_V (vm, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvbb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b010010#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ (0b01110#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VROL_VV (vm, vs1, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b010101#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards
                    vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VROL_VX (vm, vs2, rs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b010101#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VROR_VV (vm, vs1, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b010100#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards
                    vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VROR_VX (vm, vs2, rs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b010100#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VROR_VI (vm, vs2, uimm, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b01010#5 +++ ((Sail.BitVec.extractLsb uimm 5 5) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                    vs2) +++ ((Sail.BitVec.extractLsb uimm 4 0) +++ (0b011#3 +++ ((encdec_vreg_forwards
                          vd) +++ 0b1010111#7))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VWSLL_VV (vm, vs2, vs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvbb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b110101#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards
                    vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VWSLL_VX (vm, vs2, rs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvbb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b110101#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VWSLL_VI (vm, vs2, uimm, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvbb)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || (← do
                   (pure (((← (get_sew ())) == 64) && (← (currentlyEnabled Ext_Zve64x))))))))) : Bool)
      then
        (pure (0b110101#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((uimm : (BitVec 5)) +++ (0b011#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VCLMUL_VV (vm, vs2, vs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvbc)) && (← do
             (pure ((← (get_sew ())) == 64)))) : Bool)
      then
        (pure (0b001100#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards
                    vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VCLMUL_VX (vm, vs2, rs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvbc)) && (← do
             (pure ((← (get_sew ())) == 64)))) : Bool)
      then
        (pure (0b001100#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b110#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VCLMULH_VV (vm, vs2, vs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvbc)) && (← do
             (pure ((← (get_sew ())) == 64)))) : Bool)
      then
        (pure (0b001101#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards
                    vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VCLMULH_VX (vm, vs2, rs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvbc)) && (← do
             (pure ((← (get_sew ())) == 64)))) : Bool)
      then
        (pure (0b001101#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_reg_forwards
                    rs1) +++ (0b110#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VGHSH_VV (vs2, vs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkg)) && (← do
             (pure (((← (get_sew ())) == 32) && (← (zvk_check_encdec 128 4)))))) : Bool)
      then
        (pure (0b1011001#7 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards
                      vd) +++ 0b1110111#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VGMUL_VV (vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkg)) && (← do
             (pure (((← (get_sew ())) == 32) && (← (zvk_check_encdec 128 4)))))) : Bool)
      then
        (pure (0b1010001#7 +++ ((encdec_vreg_forwards vs2) +++ (0b10001#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                      vd) +++ 0b1110111#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VAESDF (funct6, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkned)) && (← do
             (pure (((← (get_sew ())) == 32) && ((← (zvk_check_encdec 128 4)) && ((funct6 == ZVK_VAESDF_VV) || (zvk_valid_reg_overlap
                       vs2 vd (← (get_lmul_pow ()))))))))) : Bool)
      then
        (pure ((encdec_vaesdf_forwards funct6) +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ (0b00001#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1110111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VAESDM (funct6, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkned)) && (← do
             (pure (((← (get_sew ())) == 32) && ((← (zvk_check_encdec 128 4)) && ((funct6 == ZVK_VAESDM_VV) || (zvk_valid_reg_overlap
                       vs2 vd (← (get_lmul_pow ()))))))))) : Bool)
      then
        (pure ((encdec_vaesdm_forwards funct6) +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ (0b00000#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1110111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VAESEF (funct6, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkned)) && (← do
             (pure (((← (get_sew ())) == 32) && ((← (zvk_check_encdec 128 4)) && ((funct6 == ZVK_VAESEF_VV) || (zvk_valid_reg_overlap
                       vs2 vd (← (get_lmul_pow ()))))))))) : Bool)
      then
        (pure ((encdec_vaesef_forwards funct6) +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ (0b00011#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1110111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VAESEM (funct6, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkned)) && (← do
             (pure (((← (get_sew ())) == 32) && ((← (zvk_check_encdec 128 4)) && ((funct6 == ZVK_VAESEM_VV) || (zvk_valid_reg_overlap
                       vs2 vd (← (get_lmul_pow ()))))))))) : Bool)
      then
        (pure ((encdec_vaesem_forwards funct6) +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ (0b00010#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1110111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VAESKF1_VI (vs2, rnd, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkned)) && (← do
             (pure (((← (get_sew ())) == 32) && (← (zvk_check_encdec 128 4)))))) : Bool)
      then
        (pure (0b1000101#7 +++ ((encdec_vreg_forwards vs2) +++ ((rnd : (BitVec 5)) +++ (0b010#3 +++ ((encdec_vreg_forwards
                      vd) +++ 0b1110111#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VAESKF2_VI (vs2, rnd, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkned)) && (← do
             (pure (((← (get_sew ())) == 32) && (← (zvk_check_encdec 128 4)))))) : Bool)
      then
        (pure (0b101010#6 +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ ((rnd : (BitVec 5)) +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1110111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VAESZ_VS (vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvkned)) && (← do
             (pure (((← (get_sew ())) == 32) && ((← (zvk_check_encdec 128 4)) && (zvk_valid_reg_overlap
                     vs2 vd (← (get_lmul_pow ())))))))) : Bool)
      then
        (pure (0b101001#6 +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ (0b00111#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1110111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VSM4K_VI (vs2, uimm, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvksed)) && (← do
             (pure (((← (get_sew ())) == 32) && (← (zvk_check_encdec 128 4)))))) : Bool)
      then
        (pure (0b100001#6 +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ ((uimm : (BitVec 5)) +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1110111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZVKSM4RTYPE (.ZVK_VSM4R_VV, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvksed)) && (← do
             (pure (((← (get_sew ())) == 32) && (← (zvk_check_encdec 128 4)))))) : Bool)
      then
        (pure (0b101000#6 +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ (0b10000#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1110111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZVKSM4RTYPE (.ZVK_VSM4R_VS, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvksed)) && (← do
             (pure (((← (get_sew ())) == 32) && ((← (zvk_check_encdec 128 4)) && (zvk_valid_reg_overlap
                     vs2 vd (← (get_lmul_pow ())))))))) : Bool)
      then
        (pure (0b101001#6 +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ (0b10000#5 +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1110111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VSHA2MS_VV (vs2, vs1, vd) =>
    (do
      if (((((← (currentlyEnabled Ext_Zvknha)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zvknhb)) && (← do
                 (pure (((← (get_sew ())) == 32) || (← do
                       (pure ((← (get_sew ())) == 64)))))))) && (← (zvknhab_check_encdec vs2 vs1
               vd))) : Bool)
      then
        (pure (0b101101#6 +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1110111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZVKSHA2TYPE (funct6, vs2, vs1, vd) =>
    (do
      if (((((← (currentlyEnabled Ext_Zvknha)) && (← do
                 (pure ((← (get_sew ())) == 32)))) || ((← (currentlyEnabled Ext_Zvknhb)) && (← do
                 (pure (((← (get_sew ())) == 32) || (← do
                       (pure ((← (get_sew ())) == 64)))))))) && (← (zvknhab_check_encdec vs2 vs1
               vd))) : Bool)
      then
        (pure ((encdec_vsha2_forwards funct6) +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards
                    vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards vd) +++ 0b1110111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VSM3ME_VV (vs2, vs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvksh)) && (← do
             (pure (((← (get_sew ())) == 32) && ((← (zvk_check_encdec 256 8)) && (zvk_valid_reg_overlap
                     vs2 vd (← (get_lmul_pow ())))))))) : Bool)
      then
        (pure (0b100000#6 +++ (1#1 +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1110111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VSM3C_VI (vs2, uimm, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvksh)) && (← do
             (pure (((← (get_sew ())) == 32) && ((← (zvk_check_encdec 256 8)) && (zvk_valid_reg_overlap
                     vs2 vd (← (get_lmul_pow ())))))))) : Bool)
      then
        (pure (0b1010111#7 +++ ((encdec_vreg_forwards vs2) +++ ((uimm : (BitVec 5)) +++ (0b010#3 +++ ((encdec_vreg_forwards
                      vd) +++ 0b1110111#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZVABD_VV (funct6, vm, vs2, vs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvabd)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
                     (pure ((← (get_sew ())) ≤b 64)))))))) : Bool)
      then
        (pure ((encdec_zvabd_vabd_func6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b010#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZVABD_VX (funct6, vm, vs2, rs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvabd)) && (← do
             (pure (((← (get_sew ())) ≤b 32) || ((← (currentlyEnabled Ext_Zve64x)) && (← do
                     (pure ((← (get_sew ())) ≤b 64)))))))) : Bool)
      then
        (pure ((encdec_zvabd_vabd_func6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_reg_forwards rs1) +++ (0b110#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZVWABDA_VV (funct6, vm, vs2, vs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvabd)) && (valid_zvwabda_sew (← (get_sew ())))) : Bool)
      then
        (pure ((encdec_zvabd_vwabda_func6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_vreg_forwards vs1) +++ (0b000#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZVWABDA_VX (funct6, vm, vs2, rs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvabd)) && (valid_zvwabda_sew (← (get_sew ())))) : Bool)
      then
        (pure ((encdec_zvabd_vwabda_func6_forwards funct6) +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards
                  vs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CSRReg (csr, rs1, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicsr)) : Bool)
      then
        (pure ((csr : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ (0#1 +++ ((encdec_csrop_forwards
                    op) +++ ((encdec_reg_forwards rd) +++ 0b1110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CSRImm (csr, imm, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicsr)) : Bool)
      then
        (pure ((csr : (BitVec 12)) +++ ((imm : (BitVec 5)) +++ (1#1 +++ ((encdec_csrop_forwards op) +++ ((encdec_reg_forwards
                      rd) +++ 0b1110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SINVAL_VMA (rs1, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Svinval)) : Bool)
      then
        (pure (0b0001011#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SFENCE_W_INVAL () =>
    (do
      if ((← (currentlyEnabled Ext_Svinval)) : Bool)
      then
        (pure (0b0001100#7 +++ (0b00000#5 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SFENCE_INVAL_IR () =>
    (do
      if ((← (currentlyEnabled Ext_Svinval)) : Bool)
      then
        (pure (0b0001100#7 +++ (0b00001#5 +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .HINVAL_VVMA (rs1, rs2) =>
    (do
      if (((← (currentlyEnabled Ext_Svinval)) && (← (currentlyEnabled Ext_H))) : Bool)
      then
        (pure (0b0010011#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .HINVAL_GVMA (rs1, rs2) =>
    (do
      if (((← (currentlyEnabled Ext_Svinval)) && (← (currentlyEnabled Ext_H))) : Bool)
      then
        (pure (0b0110011#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .WRS op =>
    (do
      if ((← (currentlyEnabled Ext_Zawrs)) : Bool)
      then
        (pure ((encdec_wrsop_forwards op) +++ (0b00000#5 +++ (0b000#3 +++ (0b00000#5 +++ 0b1110011#7)))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SSPUSH rs2 =>
    (do
      if ((((rs2 == ra) || (rs2 == t0)) && ((← (currentlyEnabled Ext_Zicfiss)) && (← (zicfiss_xSSE
                 (← readReg cur_privilege))))) : Bool)
      then
        (pure (0b1100111#7 +++ ((encdec_reg_forwards rs2) +++ (0b00000#5 +++ (0b100#3 +++ (0b00000#5 +++ 0b1110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SSPOPCHK rs1 =>
    (do
      if ((((rs1 == ra) || (rs1 == t0)) && ((← (currentlyEnabled Ext_Zicfiss)) && (← (zicfiss_xSSE
                 (← readReg cur_privilege))))) : Bool)
      then
        (pure (0b110011011100#12 +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ (0b00000#5 +++ 0b1110011#7)))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SSRDP rd =>
    (do
      if (((← (currentlyEnabled Ext_Zicfiss)) && (← (zicfiss_xSSE (← readReg cur_privilege)))) : Bool)
      then
        (pure (0b110011011100#12 +++ (0b00000#5 +++ (0b100#3 +++ ((encdec_reg_forwards rd) +++ 0b1110011#7)))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SSAMOSWAP (aq, rl, rs2, rs1, width, rd) =>
    (do
      if ((((width == 4) || ((xlen == 64) && (width == 8))) && (← (currentlyEnabled Ext_Zicfiss))) : Bool)
      then
        (pure (0b01001#5 +++ ((bool_bit_forwards aq) +++ ((bool_bit_forwards rl) +++ ((encdec_reg_forwards
                    rs2) +++ ((encdec_reg_forwards rs1) +++ (0#1 +++ ((width_enc_forwards width) +++ ((encdec_reg_forwards
                            rd) +++ 0b0101111#7)))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZICOND_RTYPE (rs2, rs1, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicond)) : Bool)
      then
        (pure (0b0000111#7 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards rs1) +++ ((encdec_zicondop_forwards
                    op) +++ ((encdec_reg_forwards rd) +++ 0b0110011#7))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZICBOM (cbop, rs1) =>
    (do
      if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
      then
        (pure ((encdec_cbop_forwards cbop) +++ ((encdec_reg_forwards rs1) +++ (0b010#3 +++ (0b00000#5 +++ 0b0001111#7)))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .BITYPE (v__20, cimm, rs1, op) =>
    (do
      if (((← (currentlyEnabled Ext_Zibi)) && ((Sail.BitVec.extractLsb v__20 0 0) == (0#1 : (BitVec 1)))) : Bool)
      then
        (let imm := (Sail.BitVec.extractLsb v__20 12 1)
        let imm := (Sail.BitVec.extractLsb v__20 12 1)
        (pure ((Sail.BitVec.extractLsb imm 11 11) +++ ((Sail.BitVec.extractLsb imm 9 4) +++ ((cimm : (BitVec 5)) +++ ((encdec_reg_forwards
                    rs1) +++ ((encdec_biop_forwards op) +++ ((Sail.BitVec.extractLsb imm 3 0) +++ ((Sail.BitVec.extractLsb
                          imm 10 10) +++ 0b1100011#7)))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZICBOZ rs1 =>
    (do
      if ((← (currentlyEnabled Ext_Zicboz)) : Bool)
      then
        (pure (0b000000000100#12 +++ ((encdec_reg_forwards rs1) +++ (0b010#3 +++ (0b00000#5 +++ 0b0001111#7)))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FENCEI (funct12, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zifencei)) : Bool)
      then
        (pure ((funct12 : (BitVec 12)) +++ ((encdec_reg_forwards rs1) +++ (0b001#3 +++ ((encdec_reg_forwards
                    rd) +++ 0b0001111#7)))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZILX_LOAD (mode, rs2, rs1, is_unsigned, width, rd) =>
    (do
      if (((← (currentlyEnabled Ext_Zilx)) && (zilx_encoding_valid mode width is_unsigned)) : Bool)
      then
        (pure ((encdec_zilx_mode_forwards mode) +++ (0b00#2 +++ ((encdec_reg_forwards rs2) +++ ((encdec_reg_forwards
                    rs1) +++ ((bool_bit_forwards is_unsigned) +++ ((width_enc_forwards width) +++ ((encdec_reg_forwards
                          rd) +++ 0b0101111#7))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FCVT_BF16_S (rs1, rm, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zfbfmin)) : Bool)
      then
        (pure (0b01000#5 +++ (0b10#2 +++ (0b01000#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                      rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FCVT_S_BF16 (rs1, rm, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zfbfmin)) : Bool)
      then
        (pure (0b01000#5 +++ (0b00#2 +++ (0b00110#5 +++ ((encdec_freg_forwards rs1) +++ ((encdec_rounding_mode_forwards
                      rm) +++ ((encdec_freg_forwards rd) +++ 0b1010011#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VFNCVTBF16_F_F_W (vm, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvfbfmin)) && (← do
             (pure ((← (get_sew ())) == 16)))) : Bool)
      then
        (pure (0b010010#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ (0b11101#5 +++ (0b001#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VFWCVTBF16_F_F_V (vm, vs2, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvfbfmin)) && (← do
             (pure ((← (get_sew ())) == 16)))) : Bool)
      then
        (pure (0b010010#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ (0b01101#5 +++ (0b001#3 +++ ((encdec_vreg_forwards
                        vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VFWMACCBF16_VV (vm, vs2, vs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvfbfwma)) && (← do
             (pure ((← (get_sew ())) == 16)))) : Bool)
      then
        (pure (0b111011#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_vreg_forwards
                    vs1) +++ (0b001#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .VFWMACCBF16_VF (vm, vs2, rs1, vd) =>
    (do
      if (((← (currentlyEnabled Ext_Zvfbfwma)) && (← do
             (pure ((← (get_sew ())) == 16)))) : Bool)
      then
        (pure (0b111011#6 +++ ((vm : (BitVec 1)) +++ ((encdec_vreg_forwards vs2) +++ ((encdec_freg_forwards
                    rs1) +++ (0b101#3 +++ ((encdec_vreg_forwards vd) +++ 0b1010111#7)))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZIMOP_MOP_R (v__22, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zimop)) : Bool)
      then
        (let mop_30 : (BitVec 1) := (Sail.BitVec.extractLsb v__22 4 4)
        let mop_30 : (BitVec 1) := (Sail.BitVec.extractLsb v__22 4 4)
        let mop_27_26 : (BitVec 2) := (Sail.BitVec.extractLsb v__22 3 2)
        let mop_21_20 : (BitVec 2) := (Sail.BitVec.extractLsb v__22 1 0)
        (pure (1#1 +++ ((mop_30 : (BitVec 1)) +++ (0b00#2 +++ ((mop_27_26 : (BitVec 2)) +++ (0b0111#4 +++ ((mop_21_20 : (BitVec 2)) +++ ((encdec_reg_forwards
                          rs1) +++ (0b100#3 +++ ((encdec_reg_forwards rd) +++ 0b1110011#7)))))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ZIMOP_MOP_RR (v__23, rs2, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zimop)) : Bool)
      then
        (let mop_30 : (BitVec 1) := (Sail.BitVec.extractLsb v__23 2 2)
        let mop_30 : (BitVec 1) := (Sail.BitVec.extractLsb v__23 2 2)
        let mop_27_26 : (BitVec 2) := (Sail.BitVec.extractLsb v__23 1 0)
        (pure (1#1 +++ ((mop_30 : (BitVec 1)) +++ (0b00#2 +++ ((mop_27_26 : (BitVec 2)) +++ (1#1 +++ ((encdec_reg_forwards
                        rs2) +++ ((encdec_reg_forwards rs1) +++ (0b100#3 +++ ((encdec_reg_forwards
                              rd) +++ 0b1110011#7)))))))))))
      else
        (do
          «assert» false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ILLEGAL s => (pure s)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def instruction_to_str (insn : instruction) : SailM String := do
  if ((assembly_forwards_matches insn) : Bool)
  then (assembly_forwards insn)
  else (pure (HAppend.hAppend ".insn " (BitVec.toFormatted (← (encdec_forwards insn)))))

def interruptType_to_str (i : InterruptType) : String :=
  match i with
  | .I_Reserved_0 => "reserved-interrupt-0"
  | .I_S_Software => "supervisor-software-interrupt"
  | .I_VS_Software => "virtual-supervisor-software-interrupt"
  | .I_M_Software => "machine-software-interrupt"
  | .I_Reserved_4 => "reserved-interrupt-4"
  | .I_S_Timer => "supervisor-timer-interrupt"
  | .I_VS_Timer => "virtual-supervisor-timer-interrupt"
  | .I_M_Timer => "machine-timer-interrupt"
  | .I_Reserved_8 => "reserved-interrupt-8"
  | .I_S_External => "supervisor-external-interrupt"
  | .I_VS_External => "virtual-supervisor-external-interrupt"
  | .I_M_External => "machine-external-interrupt"
  | .I_SG_External => "supervisor guest-external-interrupt"
  | .I_COF => "counter-overflow interrupt"
  | .I_Reserved_14 => "reserved-interrupt-14"
  | .I_Reserved_15 => "reserved-interrupt-15"

def memory_region_type_str_backwards (arg_ : String) : SailM MemoryRegionType := do
  match arg_ with
  | "main memory" => (pure MainMemory)
  | "IO memory" => (pure IOMemory)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def memory_region_type_str_forwards (arg_ : MemoryRegionType) : String :=
  match arg_ with
  | .MainMemory => "main memory"
  | .IOMemory => "IO memory"

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

def pma_region_to_str (region : PMA_Region) : String :=
  (HAppend.hAppend "base: "
    (HAppend.hAppend (BitVec.toFormatted region.base)
      (HAppend.hAppend " size: "
        (HAppend.hAppend (BitVec.toFormatted region.size) (pma_attributes_to_str region.attributes)))))

def privLevel_to_str (p : Privilege) : SailM String := do
  match p with
  | .User => (pure "U")
  | .VirtualUser => (pure "VU")
  | .Supervisor =>
    (do
      if ((← (currentlyEnabled Ext_H)) : Bool)
      then (pure "HS")
      else (pure "S"))
  | .VirtualSupervisor => (pure "VS")
  | .Machine => (pure "M")

def ptw_error_to_str (e : PTW_Error) : String :=
  match e with
  | .PTW_Invalid_Addr () => "invalid-source-addr"
  | .PTW_No_Access () => "mem-access-error"
  | .PTW_Invalid_PTE () => "invalid-pte"
  | .PTW_No_Permission () => "no-permission"
  | .PTW_Misaligned () => "misaligned-superpage"
  | .PTW_PTE_Needs_Update () => "pte-update-needed"
  | .PTW_Implicit_Error _ => "implicit-pte-vs-stage-fault"
  | .PTW_Ext_Error _ => "extension-error"

def reservability_str_backwards (arg_ : String) : SailM Reservability := do
  match arg_ with
  | "RsrvNone" => (pure RsrvNone)
  | "RsrvNonEventual" => (pure RsrvNonEventual)
  | "RsrvEventual" => (pure RsrvEventual)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def translationStage_to_str (stage : TranslationStage) : String :=
  match stage with
  | .S_Stage => "S_Stage"
  | .VS_Stage => "VS_Stage"
  | .G_Stage => "G_Stage"

def trapCause_to_str (t : TrapCause) : String :=
  match t with
  | .Interrupt i => (HAppend.hAppend "int#" (interruptType_to_str i))
  | .Exception e => (HAppend.hAppend "exc#" (exceptionType_to_str e.trap))

def wait_name_backwards (arg_ : String) : SailM WaitReason := do
  match arg_ with
  | "WAIT-WFI" => (pure WAIT_WFI)
  | "WAIT-WRS-STO" => (pure WAIT_WRS_STO)
  | "WAIT-WRS-NTO" => (pure WAIT_WRS_NTO)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def wait_name_forwards (arg_ : WaitReason) : String :=
  match arg_ with
  | .WAIT_WFI => "WAIT-WFI"
  | .WAIT_WRS_STO => "WAIT-WRS-STO"
  | .WAIT_WRS_NTO => "WAIT-WRS-NTO"

def misaligned_exception_is_access_fault (e : (Option misaligned_exception)) : Bool :=
  match e with
  | .some .AccessFault => true
  | _ => false

def plat_misaligned_access : GlobalMisalignedExceptions :=
  { load_store := none
    vector := none
    amo := none
    lrsc := (some AccessFault) }

def undefined_ExtContextPolicy (_ : Unit) : SailM ExtContextPolicy := do
  (internal_pick [ExtContext_Off, ExtContext_TwoState, ExtContext_FourState])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def ExtContextPolicy_of_num (arg_ : Nat) : ExtContextPolicy :=
  match arg_ with
  | 0 => ExtContext_Off
  | 1 => ExtContext_TwoState
  | _ => ExtContext_FourState

def num_of_ExtContextPolicy (arg_ : ExtContextPolicy) : Int :=
  match arg_ with
  | .ExtContext_Off => 0
  | .ExtContext_TwoState => 1
  | .ExtContext_FourState => 2

def plat_mstatus_legal_fs : ExtContextPolicy := ExtContext_FourState

def plat_mstatus_legal_vs : ExtContextPolicy := ExtContext_FourState

def plat_hpmcounter_width_bits := 64

def plat_hpmevent_width_bits := 56

def plat_hpmcounter_increments_in_self_hpmevent_write : Bool := false

def plat_have_clint : Bool := false

def plat_clint_base : physaddrbits := unwrapValue ((to_bits_checked (l := 34) (33554432 : Int)))

def plat_clint_size : physaddrbits := unwrapValue ((to_bits_checked (l := 34) (49152 : Int)))

def plat_have_sig : Bool := false

def plat_sig_base : physaddrbits := unwrapValue ((to_bits_checked (l := 34) (201326592 : Int)))

def plat_sig_size : physaddrbits := (zero_extend (m := 34) 0x20#8)

def plat_insns_per_tick : nat1 := 2

def plat_wfi_available_to_usermode : Bool := false

def max_wait_time : Nat := 10

def plat_has_msi : Bool := true

def plat_has_mti : Bool := true

def plat_has_mei : Bool := true

def plat_has_ssi : Bool := true

def plat_has_sti : Bool := true

def plat_has_sei : Bool := true

def illegal_instruction_writes_xtval : Bool := true

def virtual_instruction_writes_xtval : Bool := true

def software_breakpoint_writes_xtval : Bool := true

def hardware_breakpoint_writes_xtval : Bool := true

def misaligned_load_writes_xtval : Bool := true

def load_access_fault_writes_xtval : Bool := true

def load_page_fault_writes_xtval : Bool := true

def load_guest_page_fault_writes_xtval : Bool := true

def misaligned_samo_writes_xtval : Bool := true

def samo_access_fault_writes_xtval : Bool := true

def samo_page_fault_writes_xtval : Bool := true

def samo_guest_page_fault_writes_xtval : Bool := true

def misaligned_fetch_writes_xtval : Bool := true

def fetch_access_fault_writes_xtval : Bool := true

def fetch_page_fault_writes_xtval : Bool := true

def fetch_guest_page_fault_writes_xtval : Bool := true

def software_check_exception_writes_xtval : Bool := true

def hardware_error_exception_writes_xtval : Bool := true

def reserved_exceptions_write_xtval : Bool := false

def mtval_is_readonly_zero (_ : Unit) : Bool :=
  (not
    (illegal_instruction_writes_xtval || (virtual_instruction_writes_xtval || (software_breakpoint_writes_xtval || (hardware_breakpoint_writes_xtval || (misaligned_load_writes_xtval || (load_access_fault_writes_xtval || (load_page_fault_writes_xtval || (load_guest_page_fault_writes_xtval || (misaligned_samo_writes_xtval || (samo_access_fault_writes_xtval || (samo_page_fault_writes_xtval || (samo_guest_page_fault_writes_xtval || (misaligned_fetch_writes_xtval || (fetch_access_fault_writes_xtval || (fetch_page_fault_writes_xtval || (fetch_guest_page_fault_writes_xtval || (software_check_exception_writes_xtval || (hardware_error_exception_writes_xtval || reserved_exceptions_write_xtval)))))))))))))))))))

def sdtrig_has_icount : Bool := true

def sdtrig_has_etrigger : Bool := true

def sdtrig_has_itrigger : Bool := true

def sdtrig_has_mcontext : Bool := true

def sdtrig_has_hcontext : Bool := true

def sdtrig_has_scontext : Bool := true

def num_triggers := 16

def undefined_Sdtrig_breakpoint_reentrancy (_ : Unit) : SailM Sdtrig_breakpoint_reentrancy := do
  (internal_pick [Use_tcontrol, Use_interrupt_enables, No_reentrancy_support])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Sdtrig_breakpoint_reentrancy_of_num (arg_ : Nat) : Sdtrig_breakpoint_reentrancy :=
  match arg_ with
  | 0 => Use_tcontrol
  | 1 => Use_interrupt_enables
  | _ => No_reentrancy_support

def num_of_Sdtrig_breakpoint_reentrancy (arg_ : Sdtrig_breakpoint_reentrancy) : Int :=
  match arg_ with
  | .Use_tcontrol => 0
  | .Use_interrupt_enables => 1
  | .No_reentrancy_support => 2

def sdtrig_breakpoint_reentrancy : Sdtrig_breakpoint_reentrancy := Use_interrupt_enables

def sdtrig_has_tcontrol : Bool := (sdtrig_breakpoint_reentrancy == Use_tcontrol)

def undefined_AmocasOddRegisterReservedBehavior (_ : Unit) : SailM AmocasOddRegisterReservedBehavior := do
  (internal_pick [AMOCAS_Fatal, AMOCAS_Illegal])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def AmocasOddRegisterReservedBehavior_of_num (arg_ : Nat) : AmocasOddRegisterReservedBehavior :=
  match arg_ with
  | 0 => AMOCAS_Fatal
  | _ => AMOCAS_Illegal

def num_of_AmocasOddRegisterReservedBehavior (arg_ : AmocasOddRegisterReservedBehavior) : Int :=
  match arg_ with
  | .AMOCAS_Fatal => 0
  | .AMOCAS_Illegal => 1

def undefined_FcsrRmReservedBehavior (_ : Unit) : SailM FcsrRmReservedBehavior := do
  (internal_pick [Fcsr_RM_Fatal, Fcsr_RM_Illegal])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def FcsrRmReservedBehavior_of_num (arg_ : Nat) : FcsrRmReservedBehavior :=
  match arg_ with
  | 0 => Fcsr_RM_Fatal
  | _ => Fcsr_RM_Illegal

def num_of_FcsrRmReservedBehavior (arg_ : FcsrRmReservedBehavior) : Int :=
  match arg_ with
  | .Fcsr_RM_Fatal => 0
  | .Fcsr_RM_Illegal => 1

def undefined_PmpWriteOnlyReservedBehavior (_ : Unit) : SailM PmpWriteOnlyReservedBehavior := do
  (internal_pick [PMP_Fatal, PMP_ClearPermissions, PMP_Ignore])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def PmpWriteOnlyReservedBehavior_of_num (arg_ : Nat) : PmpWriteOnlyReservedBehavior :=
  match arg_ with
  | 0 => PMP_Fatal
  | 1 => PMP_ClearPermissions
  | _ => PMP_Ignore

def num_of_PmpWriteOnlyReservedBehavior (arg_ : PmpWriteOnlyReservedBehavior) : Int :=
  match arg_ with
  | .PMP_Fatal => 0
  | .PMP_ClearPermissions => 1
  | .PMP_Ignore => 2

def undefined_XenvcfgCbieReservedBehavior (_ : Unit) : SailM XenvcfgCbieReservedBehavior := do
  (internal_pick [Xenvcfg_Fatal, Xenvcfg_ClearPermissions, Xenvcfg_Ignore])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def XenvcfgCbieReservedBehavior_of_num (arg_ : Nat) : XenvcfgCbieReservedBehavior :=
  match arg_ with
  | 0 => Xenvcfg_Fatal
  | 1 => Xenvcfg_ClearPermissions
  | _ => Xenvcfg_Ignore

def num_of_XenvcfgCbieReservedBehavior (arg_ : XenvcfgCbieReservedBehavior) : Int :=
  match arg_ with
  | .Xenvcfg_Fatal => 0
  | .Xenvcfg_ClearPermissions => 1
  | .Xenvcfg_Ignore => 2

def undefined_XtvecModeReservedBehavior (_ : Unit) : SailM XtvecModeReservedBehavior := do
  (internal_pick [Xtvec_Fatal, Xtvec_Ignore])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def XtvecModeReservedBehavior_of_num (arg_ : Nat) : XtvecModeReservedBehavior :=
  match arg_ with
  | 0 => Xtvec_Fatal
  | _ => Xtvec_Ignore

def num_of_XtvecModeReservedBehavior (arg_ : XtvecModeReservedBehavior) : Int :=
  match arg_ with
  | .Xtvec_Fatal => 0
  | .Xtvec_Ignore => 1

def undefined_RV32ZdinxOddRegisterReservedBehavior (_ : Unit) : SailM RV32ZdinxOddRegisterReservedBehavior := do
  (internal_pick [Zdinx_Fatal, Zdinx_Illegal])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def RV32ZdinxOddRegisterReservedBehavior_of_num (arg_ : Nat) : RV32ZdinxOddRegisterReservedBehavior :=
  match arg_ with
  | 0 => Zdinx_Fatal
  | _ => Zdinx_Illegal

def num_of_RV32ZdinxOddRegisterReservedBehavior (arg_ : RV32ZdinxOddRegisterReservedBehavior) : Int :=
  match arg_ with
  | .Zdinx_Fatal => 0
  | .Zdinx_Illegal => 1

def undefined_IllegalVtypeReservedBehavior (_ : Unit) : SailM IllegalVtypeReservedBehavior := do
  (internal_pick [IllegalVtype_SetVill, IllegalVtype_Illegal, IllegalVtype_Fatal])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def IllegalVtypeReservedBehavior_of_num (arg_ : Nat) : IllegalVtypeReservedBehavior :=
  match arg_ with
  | 0 => IllegalVtype_SetVill
  | 1 => IllegalVtype_Illegal
  | _ => IllegalVtype_Fatal

def num_of_IllegalVtypeReservedBehavior (arg_ : IllegalVtypeReservedBehavior) : Int :=
  match arg_ with
  | .IllegalVtype_SetVill => 0
  | .IllegalVtype_Illegal => 1
  | .IllegalVtype_Fatal => 2

def undefined_OOBVstartReservedBehavior (_ : Unit) : SailM OOBVstartReservedBehavior := do
  (internal_pick [Vstart_Illegal, Vstart_Ignore])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def OOBVstartReservedBehavior_of_num (arg_ : Nat) : OOBVstartReservedBehavior :=
  match arg_ with
  | 0 => Vstart_Illegal
  | _ => Vstart_Ignore

def num_of_OOBVstartReservedBehavior (arg_ : OOBVstartReservedBehavior) : Int :=
  match arg_ with
  | .Vstart_Illegal => 0
  | .Vstart_Ignore => 1

def fcsr_rm_reserved_behavior : FcsrRmReservedBehavior := Fcsr_RM_Illegal

def pmp_write_only_reserved_behavior : PmpWriteOnlyReservedBehavior := PMP_ClearPermissions

def xtvec_mode_reserved_behavior : XtvecModeReservedBehavior := Xtvec_Ignore

def illegal_vtype_reserved_behavior : IllegalVtypeReservedBehavior := IllegalVtype_SetVill

def undefined_FflagsDirtyPolicy (_ : Unit) : SailM FflagsDirtyPolicy := do
  (internal_pick [Fflags_Dirty_Precise, Fflags_Dirty_Flag, Fflags_Dirty_Instruction])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def FflagsDirtyPolicy_of_num (arg_ : Nat) : FflagsDirtyPolicy :=
  match arg_ with
  | 0 => Fflags_Dirty_Precise
  | 1 => Fflags_Dirty_Flag
  | _ => Fflags_Dirty_Instruction

def num_of_FflagsDirtyPolicy (arg_ : FflagsDirtyPolicy) : Int :=
  match arg_ with
  | .Fflags_Dirty_Precise => 0
  | .Fflags_Dirty_Flag => 1
  | .Fflags_Dirty_Instruction => 2

def fflags_dirty_policy : FflagsDirtyPolicy := Fflags_Dirty_Precise

