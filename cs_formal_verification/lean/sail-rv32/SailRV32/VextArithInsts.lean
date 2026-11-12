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

def encdec_vvfunct6_backwards (arg_ : (BitVec 6)) : SailM vvfunct6 := do
  match arg_ with
  | 0b000000 => (pure VV_VADD)
  | 0b000010 => (pure VV_VSUB)
  | 0b000100 => (pure VV_VMINU)
  | 0b000101 => (pure VV_VMIN)
  | 0b000110 => (pure VV_VMAXU)
  | 0b000111 => (pure VV_VMAX)
  | 0b001001 => (pure VV_VAND)
  | 0b001010 => (pure VV_VOR)
  | 0b001011 => (pure VV_VXOR)
  | 0b001100 => (pure VV_VRGATHER)
  | 0b001110 => (pure VV_VRGATHEREI16)
  | 0b100000 => (pure VV_VSADDU)
  | 0b100001 => (pure VV_VSADD)
  | 0b100010 => (pure VV_VSSUBU)
  | 0b100011 => (pure VV_VSSUB)
  | 0b100101 => (pure VV_VSLL)
  | 0b100111 => (pure VV_VSMUL)
  | 0b101000 => (pure VV_VSRL)
  | 0b101001 => (pure VV_VSRA)
  | 0b101010 => (pure VV_VSSRL)
  | 0b101011 => (pure VV_VSSRA)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_vvfunct6_forwards_matches (arg_ : vvfunct6) : Bool :=
  match arg_ with
  | .VV_VADD => true
  | .VV_VSUB => true
  | .VV_VMINU => true
  | .VV_VMIN => true
  | .VV_VMAXU => true
  | .VV_VMAX => true
  | .VV_VAND => true
  | .VV_VOR => true
  | .VV_VXOR => true
  | .VV_VRGATHER => true
  | .VV_VRGATHEREI16 => true
  | .VV_VSADDU => true
  | .VV_VSADD => true
  | .VV_VSSUBU => true
  | .VV_VSSUB => true
  | .VV_VSLL => true
  | .VV_VSMUL => true
  | .VV_VSRL => true
  | .VV_VSRA => true
  | .VV_VSSRL => true
  | .VV_VSSRA => true

def encdec_vvfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b000000 => true
  | 0b000010 => true
  | 0b000100 => true
  | 0b000101 => true
  | 0b000110 => true
  | 0b000111 => true
  | 0b001001 => true
  | 0b001010 => true
  | 0b001011 => true
  | 0b001100 => true
  | 0b001110 => true
  | 0b100000 => true
  | 0b100001 => true
  | 0b100010 => true
  | 0b100011 => true
  | 0b100101 => true
  | 0b100111 => true
  | 0b101000 => true
  | 0b101001 => true
  | 0b101010 => true
  | 0b101011 => true
  | _ => false

def vvtype_mnemonic_backwards (arg_ : String) : SailM vvfunct6 := do
  match arg_ with
  | "vadd.vv" => (pure VV_VADD)
  | "vsub.vv" => (pure VV_VSUB)
  | "vand.vv" => (pure VV_VAND)
  | "vor.vv" => (pure VV_VOR)
  | "vxor.vv" => (pure VV_VXOR)
  | "vrgather.vv" => (pure VV_VRGATHER)
  | "vrgatherei16.vv" => (pure VV_VRGATHEREI16)
  | "vsaddu.vv" => (pure VV_VSADDU)
  | "vsadd.vv" => (pure VV_VSADD)
  | "vssubu.vv" => (pure VV_VSSUBU)
  | "vssub.vv" => (pure VV_VSSUB)
  | "vsll.vv" => (pure VV_VSLL)
  | "vsmul.vv" => (pure VV_VSMUL)
  | "vsrl.vv" => (pure VV_VSRL)
  | "vsra.vv" => (pure VV_VSRA)
  | "vssrl.vv" => (pure VV_VSSRL)
  | "vssra.vv" => (pure VV_VSSRA)
  | "vminu.vv" => (pure VV_VMINU)
  | "vmin.vv" => (pure VV_VMIN)
  | "vmaxu.vv" => (pure VV_VMAXU)
  | "vmax.vv" => (pure VV_VMAX)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def vvtype_mnemonic_forwards_matches (arg_ : vvfunct6) : Bool :=
  match arg_ with
  | .VV_VADD => true
  | .VV_VSUB => true
  | .VV_VAND => true
  | .VV_VOR => true
  | .VV_VXOR => true
  | .VV_VRGATHER => true
  | .VV_VRGATHEREI16 => true
  | .VV_VSADDU => true
  | .VV_VSADD => true
  | .VV_VSSUBU => true
  | .VV_VSSUB => true
  | .VV_VSLL => true
  | .VV_VSMUL => true
  | .VV_VSRL => true
  | .VV_VSRA => true
  | .VV_VSSRL => true
  | .VV_VSSRA => true
  | .VV_VMINU => true
  | .VV_VMIN => true
  | .VV_VMAXU => true
  | .VV_VMAX => true

def vvtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vadd.vv" => true
  | "vsub.vv" => true
  | "vand.vv" => true
  | "vor.vv" => true
  | "vxor.vv" => true
  | "vrgather.vv" => true
  | "vrgatherei16.vv" => true
  | "vsaddu.vv" => true
  | "vsadd.vv" => true
  | "vssubu.vv" => true
  | "vssub.vv" => true
  | "vsll.vv" => true
  | "vsmul.vv" => true
  | "vsrl.vv" => true
  | "vsra.vv" => true
  | "vssrl.vv" => true
  | "vssra.vv" => true
  | "vminu.vv" => true
  | "vmin.vv" => true
  | "vmaxu.vv" => true
  | "vmax.vv" => true
  | _ => false

def encdec_nvsfunct6_backwards (arg_ : (BitVec 6)) : SailM nvsfunct6 := do
  match arg_ with
  | 0b101100 => (pure NVS_VNSRL)
  | 0b101101 => (pure NVS_VNSRA)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_nvsfunct6_forwards_matches (arg_ : nvsfunct6) : Bool :=
  match arg_ with
  | .NVS_VNSRL => true
  | .NVS_VNSRA => true

def encdec_nvsfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b101100 => true
  | 0b101101 => true
  | _ => false

def nvstype_mnemonic_backwards (arg_ : String) : SailM nvsfunct6 := do
  match arg_ with
  | "vnsrl.wv" => (pure NVS_VNSRL)
  | "vnsra.wv" => (pure NVS_VNSRA)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def nvstype_mnemonic_forwards_matches (arg_ : nvsfunct6) : Bool :=
  match arg_ with
  | .NVS_VNSRL => true
  | .NVS_VNSRA => true

def nvstype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vnsrl.wv" => true
  | "vnsra.wv" => true
  | _ => false

def encdec_nvfunct6_backwards (arg_ : (BitVec 6)) : SailM nvfunct6 := do
  match arg_ with
  | 0b101110 => (pure NV_VNCLIPU)
  | 0b101111 => (pure NV_VNCLIP)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_nvfunct6_forwards_matches (arg_ : nvfunct6) : Bool :=
  match arg_ with
  | .NV_VNCLIPU => true
  | .NV_VNCLIP => true

def encdec_nvfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b101110 => true
  | 0b101111 => true
  | _ => false

def nvtype_mnemonic_backwards (arg_ : String) : SailM nvfunct6 := do
  match arg_ with
  | "vnclipu.wv" => (pure NV_VNCLIPU)
  | "vnclip.wv" => (pure NV_VNCLIP)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def nvtype_mnemonic_forwards_matches (arg_ : nvfunct6) : Bool :=
  match arg_ with
  | .NV_VNCLIPU => true
  | .NV_VNCLIP => true

def nvtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vnclipu.wv" => true
  | "vnclip.wv" => true
  | _ => false

def encdec_vxfunct6_backwards (arg_ : (BitVec 6)) : SailM vxfunct6 := do
  match arg_ with
  | 0b000000 => (pure VX_VADD)
  | 0b000010 => (pure VX_VSUB)
  | 0b000011 => (pure VX_VRSUB)
  | 0b000100 => (pure VX_VMINU)
  | 0b000101 => (pure VX_VMIN)
  | 0b000110 => (pure VX_VMAXU)
  | 0b000111 => (pure VX_VMAX)
  | 0b001001 => (pure VX_VAND)
  | 0b001010 => (pure VX_VOR)
  | 0b001011 => (pure VX_VXOR)
  | 0b100000 => (pure VX_VSADDU)
  | 0b100001 => (pure VX_VSADD)
  | 0b100010 => (pure VX_VSSUBU)
  | 0b100011 => (pure VX_VSSUB)
  | 0b100101 => (pure VX_VSLL)
  | 0b100111 => (pure VX_VSMUL)
  | 0b101000 => (pure VX_VSRL)
  | 0b101001 => (pure VX_VSRA)
  | 0b101010 => (pure VX_VSSRL)
  | 0b101011 => (pure VX_VSSRA)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_vxfunct6_forwards_matches (arg_ : vxfunct6) : Bool :=
  match arg_ with
  | .VX_VADD => true
  | .VX_VSUB => true
  | .VX_VRSUB => true
  | .VX_VMINU => true
  | .VX_VMIN => true
  | .VX_VMAXU => true
  | .VX_VMAX => true
  | .VX_VAND => true
  | .VX_VOR => true
  | .VX_VXOR => true
  | .VX_VSADDU => true
  | .VX_VSADD => true
  | .VX_VSSUBU => true
  | .VX_VSSUB => true
  | .VX_VSLL => true
  | .VX_VSMUL => true
  | .VX_VSRL => true
  | .VX_VSRA => true
  | .VX_VSSRL => true
  | .VX_VSSRA => true

def encdec_vxfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b000000 => true
  | 0b000010 => true
  | 0b000011 => true
  | 0b000100 => true
  | 0b000101 => true
  | 0b000110 => true
  | 0b000111 => true
  | 0b001001 => true
  | 0b001010 => true
  | 0b001011 => true
  | 0b100000 => true
  | 0b100001 => true
  | 0b100010 => true
  | 0b100011 => true
  | 0b100101 => true
  | 0b100111 => true
  | 0b101000 => true
  | 0b101001 => true
  | 0b101010 => true
  | 0b101011 => true
  | _ => false

def vxtype_mnemonic_backwards (arg_ : String) : SailM vxfunct6 := do
  match arg_ with
  | "vadd.vx" => (pure VX_VADD)
  | "vsub.vx" => (pure VX_VSUB)
  | "vrsub.vx" => (pure VX_VRSUB)
  | "vand.vx" => (pure VX_VAND)
  | "vor.vx" => (pure VX_VOR)
  | "vxor.vx" => (pure VX_VXOR)
  | "vsaddu.vx" => (pure VX_VSADDU)
  | "vsadd.vx" => (pure VX_VSADD)
  | "vssubu.vx" => (pure VX_VSSUBU)
  | "vssub.vx" => (pure VX_VSSUB)
  | "vsll.vx" => (pure VX_VSLL)
  | "vsmul.vx" => (pure VX_VSMUL)
  | "vsrl.vx" => (pure VX_VSRL)
  | "vsra.vx" => (pure VX_VSRA)
  | "vssrl.vx" => (pure VX_VSSRL)
  | "vssra.vx" => (pure VX_VSSRA)
  | "vminu.vx" => (pure VX_VMINU)
  | "vmin.vx" => (pure VX_VMIN)
  | "vmaxu.vx" => (pure VX_VMAXU)
  | "vmax.vx" => (pure VX_VMAX)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def vxtype_mnemonic_forwards_matches (arg_ : vxfunct6) : Bool :=
  match arg_ with
  | .VX_VADD => true
  | .VX_VSUB => true
  | .VX_VRSUB => true
  | .VX_VAND => true
  | .VX_VOR => true
  | .VX_VXOR => true
  | .VX_VSADDU => true
  | .VX_VSADD => true
  | .VX_VSSUBU => true
  | .VX_VSSUB => true
  | .VX_VSLL => true
  | .VX_VSMUL => true
  | .VX_VSRL => true
  | .VX_VSRA => true
  | .VX_VSSRL => true
  | .VX_VSSRA => true
  | .VX_VMINU => true
  | .VX_VMIN => true
  | .VX_VMAXU => true
  | .VX_VMAX => true

def vxtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vadd.vx" => true
  | "vsub.vx" => true
  | "vrsub.vx" => true
  | "vand.vx" => true
  | "vor.vx" => true
  | "vxor.vx" => true
  | "vsaddu.vx" => true
  | "vsadd.vx" => true
  | "vssubu.vx" => true
  | "vssub.vx" => true
  | "vsll.vx" => true
  | "vsmul.vx" => true
  | "vsrl.vx" => true
  | "vsra.vx" => true
  | "vssrl.vx" => true
  | "vssra.vx" => true
  | "vminu.vx" => true
  | "vmin.vx" => true
  | "vmaxu.vx" => true
  | "vmax.vx" => true
  | _ => false

def encdec_nxsfunct6_backwards (arg_ : (BitVec 6)) : SailM nxsfunct6 := do
  match arg_ with
  | 0b101100 => (pure NXS_VNSRL)
  | 0b101101 => (pure NXS_VNSRA)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_nxsfunct6_forwards_matches (arg_ : nxsfunct6) : Bool :=
  match arg_ with
  | .NXS_VNSRL => true
  | .NXS_VNSRA => true

def encdec_nxsfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b101100 => true
  | 0b101101 => true
  | _ => false

def nxstype_mnemonic_backwards (arg_ : String) : SailM nxsfunct6 := do
  match arg_ with
  | "vnsrl.wx" => (pure NXS_VNSRL)
  | "vnsra.wx" => (pure NXS_VNSRA)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def nxstype_mnemonic_forwards_matches (arg_ : nxsfunct6) : Bool :=
  match arg_ with
  | .NXS_VNSRL => true
  | .NXS_VNSRA => true

def nxstype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vnsrl.wx" => true
  | "vnsra.wx" => true
  | _ => false

def encdec_nxfunct6_backwards (arg_ : (BitVec 6)) : SailM nxfunct6 := do
  match arg_ with
  | 0b101110 => (pure NX_VNCLIPU)
  | 0b101111 => (pure NX_VNCLIP)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_nxfunct6_forwards_matches (arg_ : nxfunct6) : Bool :=
  match arg_ with
  | .NX_VNCLIPU => true
  | .NX_VNCLIP => true

def encdec_nxfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b101110 => true
  | 0b101111 => true
  | _ => false

def nxtype_mnemonic_backwards (arg_ : String) : SailM nxfunct6 := do
  match arg_ with
  | "vnclipu.wx" => (pure NX_VNCLIPU)
  | "vnclip.wx" => (pure NX_VNCLIP)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def nxtype_mnemonic_forwards_matches (arg_ : nxfunct6) : Bool :=
  match arg_ with
  | .NX_VNCLIPU => true
  | .NX_VNCLIP => true

def nxtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vnclipu.wx" => true
  | "vnclip.wx" => true
  | _ => false

def encdec_vxsgfunct6_backwards (arg_ : (BitVec 6)) : SailM vxsgfunct6 := do
  match arg_ with
  | 0b001110 => (pure VX_VSLIDEUP)
  | 0b001111 => (pure VX_VSLIDEDOWN)
  | 0b001100 => (pure VX_VRGATHER)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_vxsgfunct6_forwards_matches (arg_ : vxsgfunct6) : Bool :=
  match arg_ with
  | .VX_VSLIDEUP => true
  | .VX_VSLIDEDOWN => true
  | .VX_VRGATHER => true

def encdec_vxsgfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b001110 => true
  | 0b001111 => true
  | 0b001100 => true
  | _ => false

def vxsg_mnemonic_backwards (arg_ : String) : SailM vxsgfunct6 := do
  match arg_ with
  | "vslideup.vx" => (pure VX_VSLIDEUP)
  | "vslidedown.vx" => (pure VX_VSLIDEDOWN)
  | "vrgather.vx" => (pure VX_VRGATHER)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def vxsg_mnemonic_forwards_matches (arg_ : vxsgfunct6) : Bool :=
  match arg_ with
  | .VX_VSLIDEUP => true
  | .VX_VSLIDEDOWN => true
  | .VX_VRGATHER => true

def vxsg_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vslideup.vx" => true
  | "vslidedown.vx" => true
  | "vrgather.vx" => true
  | _ => false

def encdec_vifunct6_backwards (arg_ : (BitVec 6)) : SailM vifunct6 := do
  match arg_ with
  | 0b000000 => (pure VI_VADD)
  | 0b000011 => (pure VI_VRSUB)
  | 0b001001 => (pure VI_VAND)
  | 0b001010 => (pure VI_VOR)
  | 0b001011 => (pure VI_VXOR)
  | 0b100000 => (pure VI_VSADDU)
  | 0b100001 => (pure VI_VSADD)
  | 0b100101 => (pure VI_VSLL)
  | 0b101000 => (pure VI_VSRL)
  | 0b101001 => (pure VI_VSRA)
  | 0b101010 => (pure VI_VSSRL)
  | 0b101011 => (pure VI_VSSRA)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_vifunct6_forwards_matches (arg_ : vifunct6) : Bool :=
  match arg_ with
  | .VI_VADD => true
  | .VI_VRSUB => true
  | .VI_VAND => true
  | .VI_VOR => true
  | .VI_VXOR => true
  | .VI_VSADDU => true
  | .VI_VSADD => true
  | .VI_VSLL => true
  | .VI_VSRL => true
  | .VI_VSRA => true
  | .VI_VSSRL => true
  | .VI_VSSRA => true

def encdec_vifunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b000000 => true
  | 0b000011 => true
  | 0b001001 => true
  | 0b001010 => true
  | 0b001011 => true
  | 0b100000 => true
  | 0b100001 => true
  | 0b100101 => true
  | 0b101000 => true
  | 0b101001 => true
  | 0b101010 => true
  | 0b101011 => true
  | _ => false

def vitype_mnemonic_backwards (arg_ : String) : SailM vifunct6 := do
  match arg_ with
  | "vadd.vi" => (pure VI_VADD)
  | "vrsub.vi" => (pure VI_VRSUB)
  | "vand.vi" => (pure VI_VAND)
  | "vor.vi" => (pure VI_VOR)
  | "vxor.vi" => (pure VI_VXOR)
  | "vsaddu.vi" => (pure VI_VSADDU)
  | "vsadd.vi" => (pure VI_VSADD)
  | "vsll.vi" => (pure VI_VSLL)
  | "vsrl.vi" => (pure VI_VSRL)
  | "vsra.vi" => (pure VI_VSRA)
  | "vssrl.vi" => (pure VI_VSSRL)
  | "vssra.vi" => (pure VI_VSSRA)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def vitype_mnemonic_forwards_matches (arg_ : vifunct6) : Bool :=
  match arg_ with
  | .VI_VADD => true
  | .VI_VRSUB => true
  | .VI_VAND => true
  | .VI_VOR => true
  | .VI_VXOR => true
  | .VI_VSADDU => true
  | .VI_VSADD => true
  | .VI_VSLL => true
  | .VI_VSRL => true
  | .VI_VSRA => true
  | .VI_VSSRL => true
  | .VI_VSSRA => true

def vitype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vadd.vi" => true
  | "vrsub.vi" => true
  | "vand.vi" => true
  | "vor.vi" => true
  | "vxor.vi" => true
  | "vsaddu.vi" => true
  | "vsadd.vi" => true
  | "vsll.vi" => true
  | "vsrl.vi" => true
  | "vsra.vi" => true
  | "vssrl.vi" => true
  | "vssra.vi" => true
  | _ => false

def encdec_nisfunct6_backwards (arg_ : (BitVec 6)) : SailM nisfunct6 := do
  match arg_ with
  | 0b101100 => (pure NIS_VNSRL)
  | 0b101101 => (pure NIS_VNSRA)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_nisfunct6_forwards_matches (arg_ : nisfunct6) : Bool :=
  match arg_ with
  | .NIS_VNSRL => true
  | .NIS_VNSRA => true

def encdec_nisfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b101100 => true
  | 0b101101 => true
  | _ => false

def nistype_mnemonic_backwards (arg_ : String) : SailM nisfunct6 := do
  match arg_ with
  | "vnsrl.wi" => (pure NIS_VNSRL)
  | "vnsra.wi" => (pure NIS_VNSRA)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def nistype_mnemonic_forwards_matches (arg_ : nisfunct6) : Bool :=
  match arg_ with
  | .NIS_VNSRL => true
  | .NIS_VNSRA => true

def nistype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vnsrl.wi" => true
  | "vnsra.wi" => true
  | _ => false

def encdec_nifunct6_backwards (arg_ : (BitVec 6)) : SailM nifunct6 := do
  match arg_ with
  | 0b101110 => (pure NI_VNCLIPU)
  | 0b101111 => (pure NI_VNCLIP)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_nifunct6_forwards_matches (arg_ : nifunct6) : Bool :=
  match arg_ with
  | .NI_VNCLIPU => true
  | .NI_VNCLIP => true

def encdec_nifunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b101110 => true
  | 0b101111 => true
  | _ => false

def nitype_mnemonic_backwards (arg_ : String) : SailM nifunct6 := do
  match arg_ with
  | "vnclipu.wi" => (pure NI_VNCLIPU)
  | "vnclip.wi" => (pure NI_VNCLIP)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def nitype_mnemonic_forwards_matches (arg_ : nifunct6) : Bool :=
  match arg_ with
  | .NI_VNCLIPU => true
  | .NI_VNCLIP => true

def nitype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vnclipu.wi" => true
  | "vnclip.wi" => true
  | _ => false

def encdec_visgfunct6_backwards (arg_ : (BitVec 6)) : SailM visgfunct6 := do
  match arg_ with
  | 0b001110 => (pure VI_VSLIDEUP)
  | 0b001111 => (pure VI_VSLIDEDOWN)
  | 0b001100 => (pure VI_VRGATHER)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_visgfunct6_forwards_matches (arg_ : visgfunct6) : Bool :=
  match arg_ with
  | .VI_VSLIDEUP => true
  | .VI_VSLIDEDOWN => true
  | .VI_VRGATHER => true

def encdec_visgfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b001110 => true
  | 0b001111 => true
  | 0b001100 => true
  | _ => false

def visg_mnemonic_backwards (arg_ : String) : SailM visgfunct6 := do
  match arg_ with
  | "vslideup.vi" => (pure VI_VSLIDEUP)
  | "vslidedown.vi" => (pure VI_VSLIDEDOWN)
  | "vrgather.vi" => (pure VI_VRGATHER)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def visg_mnemonic_forwards_matches (arg_ : visgfunct6) : Bool :=
  match arg_ with
  | .VI_VSLIDEUP => true
  | .VI_VSLIDEDOWN => true
  | .VI_VRGATHER => true

def visg_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vslideup.vi" => true
  | "vslidedown.vi" => true
  | "vrgather.vi" => true
  | _ => false

def encdec_nreg_forwards (arg_ : (BitVec 5)) : SailM Int := do
  match arg_ with
  | 0b00000 => (pure 1)
  | 0b00001 => (pure 2)
  | 0b00011 => (pure 4)
  | 0b00111 => (pure 8)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_nreg_forwards_matches (arg_ : (BitVec 5)) : Bool :=
  match arg_ with
  | 0b00000 => true
  | 0b00001 => true
  | 0b00011 => true
  | 0b00111 => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8] -/
def encdec_nreg_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | _ => false

def nreg_string_backwards (arg_ : String) : SailM Int := do
  match arg_ with
  | "1" => (pure 1)
  | "2" => (pure 2)
  | "4" => (pure 4)
  | "8" => (pure 8)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [1, 2, 4, 8] -/
def nreg_string_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | _ => false

def nreg_string_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "1" => true
  | "2" => true
  | "4" => true
  | "8" => true
  | _ => false

def encdec_mvvfunct6_backwards (arg_ : (BitVec 6)) : SailM mvvfunct6 := do
  match arg_ with
  | 0b001000 => (pure MVV_VAADDU)
  | 0b001001 => (pure MVV_VAADD)
  | 0b001010 => (pure MVV_VASUBU)
  | 0b001011 => (pure MVV_VASUB)
  | 0b100101 => (pure MVV_VMUL)
  | 0b100111 => (pure MVV_VMULH)
  | 0b100100 => (pure MVV_VMULHU)
  | 0b100110 => (pure MVV_VMULHSU)
  | 0b100000 => (pure MVV_VDIVU)
  | 0b100001 => (pure MVV_VDIV)
  | 0b100010 => (pure MVV_VREMU)
  | 0b100011 => (pure MVV_VREM)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_mvvfunct6_forwards_matches (arg_ : mvvfunct6) : Bool :=
  match arg_ with
  | .MVV_VAADDU => true
  | .MVV_VAADD => true
  | .MVV_VASUBU => true
  | .MVV_VASUB => true
  | .MVV_VMUL => true
  | .MVV_VMULH => true
  | .MVV_VMULHU => true
  | .MVV_VMULHSU => true
  | .MVV_VDIVU => true
  | .MVV_VDIV => true
  | .MVV_VREMU => true
  | .MVV_VREM => true

def encdec_mvvfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b001000 => true
  | 0b001001 => true
  | 0b001010 => true
  | 0b001011 => true
  | 0b100101 => true
  | 0b100111 => true
  | 0b100100 => true
  | 0b100110 => true
  | 0b100000 => true
  | 0b100001 => true
  | 0b100010 => true
  | 0b100011 => true
  | _ => false

def mvvtype_mnemonic_backwards (arg_ : String) : SailM mvvfunct6 := do
  match arg_ with
  | "vaaddu.vv" => (pure MVV_VAADDU)
  | "vaadd.vv" => (pure MVV_VAADD)
  | "vasubu.vv" => (pure MVV_VASUBU)
  | "vasub.vv" => (pure MVV_VASUB)
  | "vmul.vv" => (pure MVV_VMUL)
  | "vmulh.vv" => (pure MVV_VMULH)
  | "vmulhu.vv" => (pure MVV_VMULHU)
  | "vmulhsu.vv" => (pure MVV_VMULHSU)
  | "vdivu.vv" => (pure MVV_VDIVU)
  | "vdiv.vv" => (pure MVV_VDIV)
  | "vremu.vv" => (pure MVV_VREMU)
  | "vrem.vv" => (pure MVV_VREM)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def mvvtype_mnemonic_forwards_matches (arg_ : mvvfunct6) : Bool :=
  match arg_ with
  | .MVV_VAADDU => true
  | .MVV_VAADD => true
  | .MVV_VASUBU => true
  | .MVV_VASUB => true
  | .MVV_VMUL => true
  | .MVV_VMULH => true
  | .MVV_VMULHU => true
  | .MVV_VMULHSU => true
  | .MVV_VDIVU => true
  | .MVV_VDIV => true
  | .MVV_VREMU => true
  | .MVV_VREM => true

def mvvtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vaaddu.vv" => true
  | "vaadd.vv" => true
  | "vasubu.vv" => true
  | "vasub.vv" => true
  | "vmul.vv" => true
  | "vmulh.vv" => true
  | "vmulhu.vv" => true
  | "vmulhsu.vv" => true
  | "vdivu.vv" => true
  | "vdiv.vv" => true
  | "vremu.vv" => true
  | "vrem.vv" => true
  | _ => false

def encdec_mvvmafunct6_backwards (arg_ : (BitVec 6)) : SailM mvvmafunct6 := do
  match arg_ with
  | 0b101101 => (pure MVV_VMACC)
  | 0b101111 => (pure MVV_VNMSAC)
  | 0b101001 => (pure MVV_VMADD)
  | 0b101011 => (pure MVV_VNMSUB)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_mvvmafunct6_forwards_matches (arg_ : mvvmafunct6) : Bool :=
  match arg_ with
  | .MVV_VMACC => true
  | .MVV_VNMSAC => true
  | .MVV_VMADD => true
  | .MVV_VNMSUB => true

def encdec_mvvmafunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b101101 => true
  | 0b101111 => true
  | 0b101001 => true
  | 0b101011 => true
  | _ => false

def mvvmatype_mnemonic_backwards (arg_ : String) : SailM mvvmafunct6 := do
  match arg_ with
  | "vmacc.vv" => (pure MVV_VMACC)
  | "vnmsac.vv" => (pure MVV_VNMSAC)
  | "vmadd.vv" => (pure MVV_VMADD)
  | "vnmsub.vv" => (pure MVV_VNMSUB)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def mvvmatype_mnemonic_forwards_matches (arg_ : mvvmafunct6) : Bool :=
  match arg_ with
  | .MVV_VMACC => true
  | .MVV_VNMSAC => true
  | .MVV_VMADD => true
  | .MVV_VNMSUB => true

def mvvmatype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vmacc.vv" => true
  | "vnmsac.vv" => true
  | "vmadd.vv" => true
  | "vnmsub.vv" => true
  | _ => false

def encdec_wvvfunct6_backwards (arg_ : (BitVec 6)) : SailM wvvfunct6 := do
  match arg_ with
  | 0b110001 => (pure WVV_VADD)
  | 0b110011 => (pure WVV_VSUB)
  | 0b110000 => (pure WVV_VADDU)
  | 0b110010 => (pure WVV_VSUBU)
  | 0b111011 => (pure WVV_VWMUL)
  | 0b111000 => (pure WVV_VWMULU)
  | 0b111010 => (pure WVV_VWMULSU)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_wvvfunct6_forwards_matches (arg_ : wvvfunct6) : Bool :=
  match arg_ with
  | .WVV_VADD => true
  | .WVV_VSUB => true
  | .WVV_VADDU => true
  | .WVV_VSUBU => true
  | .WVV_VWMUL => true
  | .WVV_VWMULU => true
  | .WVV_VWMULSU => true

def encdec_wvvfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b110001 => true
  | 0b110011 => true
  | 0b110000 => true
  | 0b110010 => true
  | 0b111011 => true
  | 0b111000 => true
  | 0b111010 => true
  | _ => false

def wvvtype_mnemonic_backwards (arg_ : String) : SailM wvvfunct6 := do
  match arg_ with
  | "vwadd.vv" => (pure WVV_VADD)
  | "vwsub.vv" => (pure WVV_VSUB)
  | "vwaddu.vv" => (pure WVV_VADDU)
  | "vwsubu.vv" => (pure WVV_VSUBU)
  | "vwmul.vv" => (pure WVV_VWMUL)
  | "vwmulu.vv" => (pure WVV_VWMULU)
  | "vwmulsu.vv" => (pure WVV_VWMULSU)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def wvvtype_mnemonic_forwards_matches (arg_ : wvvfunct6) : Bool :=
  match arg_ with
  | .WVV_VADD => true
  | .WVV_VSUB => true
  | .WVV_VADDU => true
  | .WVV_VSUBU => true
  | .WVV_VWMUL => true
  | .WVV_VWMULU => true
  | .WVV_VWMULSU => true

def wvvtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vwadd.vv" => true
  | "vwsub.vv" => true
  | "vwaddu.vv" => true
  | "vwsubu.vv" => true
  | "vwmul.vv" => true
  | "vwmulu.vv" => true
  | "vwmulsu.vv" => true
  | _ => false

def encdec_wvfunct6_backwards (arg_ : (BitVec 6)) : SailM wvfunct6 := do
  match arg_ with
  | 0b110101 => (pure WV_VADD)
  | 0b110111 => (pure WV_VSUB)
  | 0b110100 => (pure WV_VADDU)
  | 0b110110 => (pure WV_VSUBU)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_wvfunct6_forwards_matches (arg_ : wvfunct6) : Bool :=
  match arg_ with
  | .WV_VADD => true
  | .WV_VSUB => true
  | .WV_VADDU => true
  | .WV_VSUBU => true

def encdec_wvfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b110101 => true
  | 0b110111 => true
  | 0b110100 => true
  | 0b110110 => true
  | _ => false

def wvtype_mnemonic_backwards (arg_ : String) : SailM wvfunct6 := do
  match arg_ with
  | "vwadd.wv" => (pure WV_VADD)
  | "vwsub.wv" => (pure WV_VSUB)
  | "vwaddu.wv" => (pure WV_VADDU)
  | "vwsubu.wv" => (pure WV_VSUBU)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def wvtype_mnemonic_forwards_matches (arg_ : wvfunct6) : Bool :=
  match arg_ with
  | .WV_VADD => true
  | .WV_VSUB => true
  | .WV_VADDU => true
  | .WV_VSUBU => true

def wvtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vwadd.wv" => true
  | "vwsub.wv" => true
  | "vwaddu.wv" => true
  | "vwsubu.wv" => true
  | _ => false

def encdec_wmvvfunct6_backwards (arg_ : (BitVec 6)) : SailM wmvvfunct6 := do
  match arg_ with
  | 0b111100 => (pure WMVV_VWMACCU)
  | 0b111101 => (pure WMVV_VWMACC)
  | 0b111111 => (pure WMVV_VWMACCSU)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_wmvvfunct6_forwards_matches (arg_ : wmvvfunct6) : Bool :=
  match arg_ with
  | .WMVV_VWMACCU => true
  | .WMVV_VWMACC => true
  | .WMVV_VWMACCSU => true

def encdec_wmvvfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b111100 => true
  | 0b111101 => true
  | 0b111111 => true
  | _ => false

def wmvvtype_mnemonic_backwards (arg_ : String) : SailM wmvvfunct6 := do
  match arg_ with
  | "vwmaccu.vv" => (pure WMVV_VWMACCU)
  | "vwmacc.vv" => (pure WMVV_VWMACC)
  | "vwmaccsu.vv" => (pure WMVV_VWMACCSU)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def wmvvtype_mnemonic_forwards_matches (arg_ : wmvvfunct6) : Bool :=
  match arg_ with
  | .WMVV_VWMACCU => true
  | .WMVV_VWMACC => true
  | .WMVV_VWMACCSU => true

def wmvvtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vwmaccu.vv" => true
  | "vwmacc.vv" => true
  | "vwmaccsu.vv" => true
  | _ => false

def vext_vs1_backwards (arg_ : (BitVec 5)) : SailM vextfunct6 := do
  match arg_ with
  | 0b00110 => (pure VEXT2_ZVF2)
  | 0b00111 => (pure VEXT2_SVF2)
  | 0b00100 => (pure VEXT4_ZVF4)
  | 0b00101 => (pure VEXT4_SVF4)
  | 0b00010 => (pure VEXT8_ZVF8)
  | 0b00011 => (pure VEXT8_SVF8)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def vext_vs1_forwards_matches (arg_ : vextfunct6) : Bool :=
  match arg_ with
  | .VEXT2_ZVF2 => true
  | .VEXT2_SVF2 => true
  | .VEXT4_ZVF4 => true
  | .VEXT4_SVF4 => true
  | .VEXT8_ZVF8 => true
  | .VEXT8_SVF8 => true

def vext_vs1_backwards_matches (arg_ : (BitVec 5)) : Bool :=
  match arg_ with
  | 0b00110 => true
  | 0b00111 => true
  | 0b00100 => true
  | 0b00101 => true
  | 0b00010 => true
  | 0b00011 => true
  | _ => false

def vexttype_mnemonic_backwards (arg_ : String) : SailM vextfunct6 := do
  match arg_ with
  | "vzext.vf2" => (pure VEXT2_ZVF2)
  | "vsext.vf2" => (pure VEXT2_SVF2)
  | "vzext.vf4" => (pure VEXT4_ZVF4)
  | "vsext.vf4" => (pure VEXT4_SVF4)
  | "vzext.vf8" => (pure VEXT8_ZVF8)
  | "vsext.vf8" => (pure VEXT8_SVF8)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def vexttype_mnemonic_forwards_matches (arg_ : vextfunct6) : Bool :=
  match arg_ with
  | .VEXT2_ZVF2 => true
  | .VEXT2_SVF2 => true
  | .VEXT4_ZVF4 => true
  | .VEXT4_SVF4 => true
  | .VEXT8_ZVF8 => true
  | .VEXT8_SVF8 => true

def vexttype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vzext.vf2" => true
  | "vsext.vf2" => true
  | "vzext.vf4" => true
  | "vsext.vf4" => true
  | "vzext.vf8" => true
  | "vsext.vf8" => true
  | _ => false

def encdec_mvxfunct6_backwards (arg_ : (BitVec 6)) : SailM mvxfunct6 := do
  match arg_ with
  | 0b001000 => (pure MVX_VAADDU)
  | 0b001001 => (pure MVX_VAADD)
  | 0b001010 => (pure MVX_VASUBU)
  | 0b001011 => (pure MVX_VASUB)
  | 0b001110 => (pure MVX_VSLIDE1UP)
  | 0b001111 => (pure MVX_VSLIDE1DOWN)
  | 0b100101 => (pure MVX_VMUL)
  | 0b100111 => (pure MVX_VMULH)
  | 0b100100 => (pure MVX_VMULHU)
  | 0b100110 => (pure MVX_VMULHSU)
  | 0b100000 => (pure MVX_VDIVU)
  | 0b100001 => (pure MVX_VDIV)
  | 0b100010 => (pure MVX_VREMU)
  | 0b100011 => (pure MVX_VREM)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_mvxfunct6_forwards_matches (arg_ : mvxfunct6) : Bool :=
  match arg_ with
  | .MVX_VAADDU => true
  | .MVX_VAADD => true
  | .MVX_VASUBU => true
  | .MVX_VASUB => true
  | .MVX_VSLIDE1UP => true
  | .MVX_VSLIDE1DOWN => true
  | .MVX_VMUL => true
  | .MVX_VMULH => true
  | .MVX_VMULHU => true
  | .MVX_VMULHSU => true
  | .MVX_VDIVU => true
  | .MVX_VDIV => true
  | .MVX_VREMU => true
  | .MVX_VREM => true

def encdec_mvxfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b001000 => true
  | 0b001001 => true
  | 0b001010 => true
  | 0b001011 => true
  | 0b001110 => true
  | 0b001111 => true
  | 0b100101 => true
  | 0b100111 => true
  | 0b100100 => true
  | 0b100110 => true
  | 0b100000 => true
  | 0b100001 => true
  | 0b100010 => true
  | 0b100011 => true
  | _ => false

def mvxtype_mnemonic_backwards (arg_ : String) : SailM mvxfunct6 := do
  match arg_ with
  | "vaaddu.vx" => (pure MVX_VAADDU)
  | "vaadd.vx" => (pure MVX_VAADD)
  | "vasubu.vx" => (pure MVX_VASUBU)
  | "vasub.vx" => (pure MVX_VASUB)
  | "vslide1up.vx" => (pure MVX_VSLIDE1UP)
  | "vslide1down.vx" => (pure MVX_VSLIDE1DOWN)
  | "vmul.vx" => (pure MVX_VMUL)
  | "vmulh.vx" => (pure MVX_VMULH)
  | "vmulhu.vx" => (pure MVX_VMULHU)
  | "vmulhsu.vx" => (pure MVX_VMULHSU)
  | "vdivu.vx" => (pure MVX_VDIVU)
  | "vdiv.vx" => (pure MVX_VDIV)
  | "vremu.vx" => (pure MVX_VREMU)
  | "vrem.vx" => (pure MVX_VREM)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def mvxtype_mnemonic_forwards_matches (arg_ : mvxfunct6) : Bool :=
  match arg_ with
  | .MVX_VAADDU => true
  | .MVX_VAADD => true
  | .MVX_VASUBU => true
  | .MVX_VASUB => true
  | .MVX_VSLIDE1UP => true
  | .MVX_VSLIDE1DOWN => true
  | .MVX_VMUL => true
  | .MVX_VMULH => true
  | .MVX_VMULHU => true
  | .MVX_VMULHSU => true
  | .MVX_VDIVU => true
  | .MVX_VDIV => true
  | .MVX_VREMU => true
  | .MVX_VREM => true

def mvxtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vaaddu.vx" => true
  | "vaadd.vx" => true
  | "vasubu.vx" => true
  | "vasub.vx" => true
  | "vslide1up.vx" => true
  | "vslide1down.vx" => true
  | "vmul.vx" => true
  | "vmulh.vx" => true
  | "vmulhu.vx" => true
  | "vmulhsu.vx" => true
  | "vdivu.vx" => true
  | "vdiv.vx" => true
  | "vremu.vx" => true
  | "vrem.vx" => true
  | _ => false

def encdec_mvxmafunct6_backwards (arg_ : (BitVec 6)) : SailM mvxmafunct6 := do
  match arg_ with
  | 0b101101 => (pure MVX_VMACC)
  | 0b101111 => (pure MVX_VNMSAC)
  | 0b101001 => (pure MVX_VMADD)
  | 0b101011 => (pure MVX_VNMSUB)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_mvxmafunct6_forwards_matches (arg_ : mvxmafunct6) : Bool :=
  match arg_ with
  | .MVX_VMACC => true
  | .MVX_VNMSAC => true
  | .MVX_VMADD => true
  | .MVX_VNMSUB => true

def encdec_mvxmafunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b101101 => true
  | 0b101111 => true
  | 0b101001 => true
  | 0b101011 => true
  | _ => false

def mvxmatype_mnemonic_backwards (arg_ : String) : SailM mvxmafunct6 := do
  match arg_ with
  | "vmacc.vx" => (pure MVX_VMACC)
  | "vnmsac.vx" => (pure MVX_VNMSAC)
  | "vmadd.vx" => (pure MVX_VMADD)
  | "vnmsub.vx" => (pure MVX_VNMSUB)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def mvxmatype_mnemonic_forwards_matches (arg_ : mvxmafunct6) : Bool :=
  match arg_ with
  | .MVX_VMACC => true
  | .MVX_VNMSAC => true
  | .MVX_VMADD => true
  | .MVX_VNMSUB => true

def mvxmatype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vmacc.vx" => true
  | "vnmsac.vx" => true
  | "vmadd.vx" => true
  | "vnmsub.vx" => true
  | _ => false

def encdec_wvxfunct6_backwards (arg_ : (BitVec 6)) : SailM wvxfunct6 := do
  match arg_ with
  | 0b110001 => (pure WVX_VADD)
  | 0b110011 => (pure WVX_VSUB)
  | 0b110000 => (pure WVX_VADDU)
  | 0b110010 => (pure WVX_VSUBU)
  | 0b111011 => (pure WVX_VWMUL)
  | 0b111000 => (pure WVX_VWMULU)
  | 0b111010 => (pure WVX_VWMULSU)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_wvxfunct6_forwards_matches (arg_ : wvxfunct6) : Bool :=
  match arg_ with
  | .WVX_VADD => true
  | .WVX_VSUB => true
  | .WVX_VADDU => true
  | .WVX_VSUBU => true
  | .WVX_VWMUL => true
  | .WVX_VWMULU => true
  | .WVX_VWMULSU => true

def encdec_wvxfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b110001 => true
  | 0b110011 => true
  | 0b110000 => true
  | 0b110010 => true
  | 0b111011 => true
  | 0b111000 => true
  | 0b111010 => true
  | _ => false

def wvxtype_mnemonic_backwards (arg_ : String) : SailM wvxfunct6 := do
  match arg_ with
  | "vwadd.vx" => (pure WVX_VADD)
  | "vwsub.vx" => (pure WVX_VSUB)
  | "vwaddu.vx" => (pure WVX_VADDU)
  | "vwsubu.vx" => (pure WVX_VSUBU)
  | "vwmul.vx" => (pure WVX_VWMUL)
  | "vwmulu.vx" => (pure WVX_VWMULU)
  | "vwmulsu.vx" => (pure WVX_VWMULSU)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def wvxtype_mnemonic_forwards_matches (arg_ : wvxfunct6) : Bool :=
  match arg_ with
  | .WVX_VADD => true
  | .WVX_VSUB => true
  | .WVX_VADDU => true
  | .WVX_VSUBU => true
  | .WVX_VWMUL => true
  | .WVX_VWMULU => true
  | .WVX_VWMULSU => true

def wvxtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vwadd.vx" => true
  | "vwsub.vx" => true
  | "vwaddu.vx" => true
  | "vwsubu.vx" => true
  | "vwmul.vx" => true
  | "vwmulu.vx" => true
  | "vwmulsu.vx" => true
  | _ => false

def encdec_wxfunct6_backwards (arg_ : (BitVec 6)) : SailM wxfunct6 := do
  match arg_ with
  | 0b110101 => (pure WX_VADD)
  | 0b110111 => (pure WX_VSUB)
  | 0b110100 => (pure WX_VADDU)
  | 0b110110 => (pure WX_VSUBU)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_wxfunct6_forwards_matches (arg_ : wxfunct6) : Bool :=
  match arg_ with
  | .WX_VADD => true
  | .WX_VSUB => true
  | .WX_VADDU => true
  | .WX_VSUBU => true

def encdec_wxfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b110101 => true
  | 0b110111 => true
  | 0b110100 => true
  | 0b110110 => true
  | _ => false

def wxtype_mnemonic_backwards (arg_ : String) : SailM wxfunct6 := do
  match arg_ with
  | "vwadd.wx" => (pure WX_VADD)
  | "vwsub.wx" => (pure WX_VSUB)
  | "vwaddu.wx" => (pure WX_VADDU)
  | "vwsubu.wx" => (pure WX_VSUBU)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def wxtype_mnemonic_forwards_matches (arg_ : wxfunct6) : Bool :=
  match arg_ with
  | .WX_VADD => true
  | .WX_VSUB => true
  | .WX_VADDU => true
  | .WX_VSUBU => true

def wxtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vwadd.wx" => true
  | "vwsub.wx" => true
  | "vwaddu.wx" => true
  | "vwsubu.wx" => true
  | _ => false

def encdec_wmvxfunct6_backwards (arg_ : (BitVec 6)) : SailM wmvxfunct6 := do
  match arg_ with
  | 0b111100 => (pure WMVX_VWMACCU)
  | 0b111101 => (pure WMVX_VWMACC)
  | 0b111110 => (pure WMVX_VWMACCUS)
  | 0b111111 => (pure WMVX_VWMACCSU)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_wmvxfunct6_forwards_matches (arg_ : wmvxfunct6) : Bool :=
  match arg_ with
  | .WMVX_VWMACCU => true
  | .WMVX_VWMACC => true
  | .WMVX_VWMACCUS => true
  | .WMVX_VWMACCSU => true

def encdec_wmvxfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b111100 => true
  | 0b111101 => true
  | 0b111110 => true
  | 0b111111 => true
  | _ => false

def wmvxtype_mnemonic_backwards (arg_ : String) : SailM wmvxfunct6 := do
  match arg_ with
  | "vwmaccu.vx" => (pure WMVX_VWMACCU)
  | "vwmacc.vx" => (pure WMVX_VWMACC)
  | "vwmaccus.vx" => (pure WMVX_VWMACCUS)
  | "vwmaccsu.vx" => (pure WMVX_VWMACCSU)
  | _ =>
    (do
      «assert» false "Pattern match failure at unknown location"
      throw Error.Exit)

def wmvxtype_mnemonic_forwards_matches (arg_ : wmvxfunct6) : Bool :=
  match arg_ with
  | .WMVX_VWMACCU => true
  | .WMVX_VWMACC => true
  | .WMVX_VWMACCUS => true
  | .WMVX_VWMACCSU => true

def wmvxtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vwmaccu.vx" => true
  | "vwmacc.vx" => true
  | "vwmaccus.vx" => true
  | "vwmaccsu.vx" => true
  | _ => false

