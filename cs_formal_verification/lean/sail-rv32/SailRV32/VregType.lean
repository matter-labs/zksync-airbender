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

def undefined_vvfunct6 (_ : Unit) : SailM vvfunct6 := do
  (internal_pick
    [VV_VADD, VV_VSUB, VV_VMINU, VV_VMIN, VV_VMAXU, VV_VMAX, VV_VAND, VV_VOR, VV_VXOR, VV_VRGATHER, VV_VRGATHEREI16, VV_VSADDU, VV_VSADD, VV_VSSUBU, VV_VSSUB, VV_VSLL, VV_VSMUL, VV_VSRL, VV_VSRA, VV_VSSRL, VV_VSSRA])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 20 -/
def vvfunct6_of_num (arg_ : Nat) : vvfunct6 :=
  match arg_ with
  | 0 => VV_VADD
  | 1 => VV_VSUB
  | 2 => VV_VMINU
  | 3 => VV_VMIN
  | 4 => VV_VMAXU
  | 5 => VV_VMAX
  | 6 => VV_VAND
  | 7 => VV_VOR
  | 8 => VV_VXOR
  | 9 => VV_VRGATHER
  | 10 => VV_VRGATHEREI16
  | 11 => VV_VSADDU
  | 12 => VV_VSADD
  | 13 => VV_VSSUBU
  | 14 => VV_VSSUB
  | 15 => VV_VSLL
  | 16 => VV_VSMUL
  | 17 => VV_VSRL
  | 18 => VV_VSRA
  | 19 => VV_VSSRL
  | _ => VV_VSSRA

def num_of_vvfunct6 (arg_ : vvfunct6) : Int :=
  match arg_ with
  | .VV_VADD => 0
  | .VV_VSUB => 1
  | .VV_VMINU => 2
  | .VV_VMIN => 3
  | .VV_VMAXU => 4
  | .VV_VMAX => 5
  | .VV_VAND => 6
  | .VV_VOR => 7
  | .VV_VXOR => 8
  | .VV_VRGATHER => 9
  | .VV_VRGATHEREI16 => 10
  | .VV_VSADDU => 11
  | .VV_VSADD => 12
  | .VV_VSSUBU => 13
  | .VV_VSSUB => 14
  | .VV_VSLL => 15
  | .VV_VSMUL => 16
  | .VV_VSRL => 17
  | .VV_VSRA => 18
  | .VV_VSSRL => 19
  | .VV_VSSRA => 20

def undefined_vvcmpfunct6 (_ : Unit) : SailM vvcmpfunct6 := do
  (internal_pick [VVCMP_VMSEQ, VVCMP_VMSNE, VVCMP_VMSLTU, VVCMP_VMSLT, VVCMP_VMSLEU, VVCMP_VMSLE])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def vvcmpfunct6_of_num (arg_ : Nat) : vvcmpfunct6 :=
  match arg_ with
  | 0 => VVCMP_VMSEQ
  | 1 => VVCMP_VMSNE
  | 2 => VVCMP_VMSLTU
  | 3 => VVCMP_VMSLT
  | 4 => VVCMP_VMSLEU
  | _ => VVCMP_VMSLE

def num_of_vvcmpfunct6 (arg_ : vvcmpfunct6) : Int :=
  match arg_ with
  | .VVCMP_VMSEQ => 0
  | .VVCMP_VMSNE => 1
  | .VVCMP_VMSLTU => 2
  | .VVCMP_VMSLT => 3
  | .VVCMP_VMSLEU => 4
  | .VVCMP_VMSLE => 5

def undefined_vvmfunct6 (_ : Unit) : SailM vvmfunct6 := do
  (internal_pick [VVM_VMADC, VVM_VMSBC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def vvmfunct6_of_num (arg_ : Nat) : vvmfunct6 :=
  match arg_ with
  | 0 => VVM_VMADC
  | _ => VVM_VMSBC

def num_of_vvmfunct6 (arg_ : vvmfunct6) : Int :=
  match arg_ with
  | .VVM_VMADC => 0
  | .VVM_VMSBC => 1

def undefined_vvmcfunct6 (_ : Unit) : SailM vvmcfunct6 := do
  (internal_pick [VVMC_VMADC, VVMC_VMSBC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def vvmcfunct6_of_num (arg_ : Nat) : vvmcfunct6 :=
  match arg_ with
  | 0 => VVMC_VMADC
  | _ => VVMC_VMSBC

def num_of_vvmcfunct6 (arg_ : vvmcfunct6) : Int :=
  match arg_ with
  | .VVMC_VMADC => 0
  | .VVMC_VMSBC => 1

def undefined_vvmsfunct6 (_ : Unit) : SailM vvmsfunct6 := do
  (internal_pick [VVMS_VADC, VVMS_VSBC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def vvmsfunct6_of_num (arg_ : Nat) : vvmsfunct6 :=
  match arg_ with
  | 0 => VVMS_VADC
  | _ => VVMS_VSBC

def num_of_vvmsfunct6 (arg_ : vvmsfunct6) : Int :=
  match arg_ with
  | .VVMS_VADC => 0
  | .VVMS_VSBC => 1

def undefined_vxmfunct6 (_ : Unit) : SailM vxmfunct6 := do
  (internal_pick [VXM_VMADC, VXM_VMSBC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def vxmfunct6_of_num (arg_ : Nat) : vxmfunct6 :=
  match arg_ with
  | 0 => VXM_VMADC
  | _ => VXM_VMSBC

def num_of_vxmfunct6 (arg_ : vxmfunct6) : Int :=
  match arg_ with
  | .VXM_VMADC => 0
  | .VXM_VMSBC => 1

def undefined_vxmcfunct6 (_ : Unit) : SailM vxmcfunct6 := do
  (internal_pick [VXMC_VMADC, VXMC_VMSBC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def vxmcfunct6_of_num (arg_ : Nat) : vxmcfunct6 :=
  match arg_ with
  | 0 => VXMC_VMADC
  | _ => VXMC_VMSBC

def num_of_vxmcfunct6 (arg_ : vxmcfunct6) : Int :=
  match arg_ with
  | .VXMC_VMADC => 0
  | .VXMC_VMSBC => 1

def undefined_vxmsfunct6 (_ : Unit) : SailM vxmsfunct6 := do
  (internal_pick [VXMS_VADC, VXMS_VSBC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def vxmsfunct6_of_num (arg_ : Nat) : vxmsfunct6 :=
  match arg_ with
  | 0 => VXMS_VADC
  | _ => VXMS_VSBC

def num_of_vxmsfunct6 (arg_ : vxmsfunct6) : Int :=
  match arg_ with
  | .VXMS_VADC => 0
  | .VXMS_VSBC => 1

def undefined_vimfunct6 (_ : Unit) : SailM vimfunct6 := do
  (internal_pick [VIM_VMADC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 0 -/
def vimfunct6_of_num (arg_ : Nat) : vimfunct6 :=
  match arg_ with
  | _ => VIM_VMADC

def num_of_vimfunct6 (arg_ : vimfunct6) : Int :=
  match arg_ with
  | .VIM_VMADC => 0

def undefined_vimcfunct6 (_ : Unit) : SailM vimcfunct6 := do
  (internal_pick [VIMC_VMADC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 0 -/
def vimcfunct6_of_num (arg_ : Nat) : vimcfunct6 :=
  match arg_ with
  | _ => VIMC_VMADC

def num_of_vimcfunct6 (arg_ : vimcfunct6) : Int :=
  match arg_ with
  | .VIMC_VMADC => 0

def undefined_vimsfunct6 (_ : Unit) : SailM vimsfunct6 := do
  (internal_pick [VIMS_VADC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 0 -/
def vimsfunct6_of_num (arg_ : Nat) : vimsfunct6 :=
  match arg_ with
  | _ => VIMS_VADC

def num_of_vimsfunct6 (arg_ : vimsfunct6) : Int :=
  match arg_ with
  | .VIMS_VADC => 0

def undefined_vxcmpfunct6 (_ : Unit) : SailM vxcmpfunct6 := do
  (internal_pick
    [VXCMP_VMSEQ, VXCMP_VMSNE, VXCMP_VMSLTU, VXCMP_VMSLT, VXCMP_VMSLEU, VXCMP_VMSLE, VXCMP_VMSGTU, VXCMP_VMSGT])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def vxcmpfunct6_of_num (arg_ : Nat) : vxcmpfunct6 :=
  match arg_ with
  | 0 => VXCMP_VMSEQ
  | 1 => VXCMP_VMSNE
  | 2 => VXCMP_VMSLTU
  | 3 => VXCMP_VMSLT
  | 4 => VXCMP_VMSLEU
  | 5 => VXCMP_VMSLE
  | 6 => VXCMP_VMSGTU
  | _ => VXCMP_VMSGT

def num_of_vxcmpfunct6 (arg_ : vxcmpfunct6) : Int :=
  match arg_ with
  | .VXCMP_VMSEQ => 0
  | .VXCMP_VMSNE => 1
  | .VXCMP_VMSLTU => 2
  | .VXCMP_VMSLT => 3
  | .VXCMP_VMSLEU => 4
  | .VXCMP_VMSLE => 5
  | .VXCMP_VMSGTU => 6
  | .VXCMP_VMSGT => 7

def undefined_vicmpfunct6 (_ : Unit) : SailM vicmpfunct6 := do
  (internal_pick [VICMP_VMSEQ, VICMP_VMSNE, VICMP_VMSLEU, VICMP_VMSLE, VICMP_VMSGTU, VICMP_VMSGT])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def vicmpfunct6_of_num (arg_ : Nat) : vicmpfunct6 :=
  match arg_ with
  | 0 => VICMP_VMSEQ
  | 1 => VICMP_VMSNE
  | 2 => VICMP_VMSLEU
  | 3 => VICMP_VMSLE
  | 4 => VICMP_VMSGTU
  | _ => VICMP_VMSGT

def num_of_vicmpfunct6 (arg_ : vicmpfunct6) : Int :=
  match arg_ with
  | .VICMP_VMSEQ => 0
  | .VICMP_VMSNE => 1
  | .VICMP_VMSLEU => 2
  | .VICMP_VMSLE => 3
  | .VICMP_VMSGTU => 4
  | .VICMP_VMSGT => 5

def undefined_nvfunct6 (_ : Unit) : SailM nvfunct6 := do
  (internal_pick [NV_VNCLIPU, NV_VNCLIP])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def nvfunct6_of_num (arg_ : Nat) : nvfunct6 :=
  match arg_ with
  | 0 => NV_VNCLIPU
  | _ => NV_VNCLIP

def num_of_nvfunct6 (arg_ : nvfunct6) : Int :=
  match arg_ with
  | .NV_VNCLIPU => 0
  | .NV_VNCLIP => 1

def undefined_nvsfunct6 (_ : Unit) : SailM nvsfunct6 := do
  (internal_pick [NVS_VNSRL, NVS_VNSRA])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def nvsfunct6_of_num (arg_ : Nat) : nvsfunct6 :=
  match arg_ with
  | 0 => NVS_VNSRL
  | _ => NVS_VNSRA

def num_of_nvsfunct6 (arg_ : nvsfunct6) : Int :=
  match arg_ with
  | .NVS_VNSRL => 0
  | .NVS_VNSRA => 1

def undefined_nxfunct6 (_ : Unit) : SailM nxfunct6 := do
  (internal_pick [NX_VNCLIPU, NX_VNCLIP])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def nxfunct6_of_num (arg_ : Nat) : nxfunct6 :=
  match arg_ with
  | 0 => NX_VNCLIPU
  | _ => NX_VNCLIP

def num_of_nxfunct6 (arg_ : nxfunct6) : Int :=
  match arg_ with
  | .NX_VNCLIPU => 0
  | .NX_VNCLIP => 1

def undefined_nxsfunct6 (_ : Unit) : SailM nxsfunct6 := do
  (internal_pick [NXS_VNSRL, NXS_VNSRA])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def nxsfunct6_of_num (arg_ : Nat) : nxsfunct6 :=
  match arg_ with
  | 0 => NXS_VNSRL
  | _ => NXS_VNSRA

def num_of_nxsfunct6 (arg_ : nxsfunct6) : Int :=
  match arg_ with
  | .NXS_VNSRL => 0
  | .NXS_VNSRA => 1

def undefined_mmfunct6 (_ : Unit) : SailM mmfunct6 := do
  (internal_pick [MM_VMAND, MM_VMNAND, MM_VMANDN, MM_VMXOR, MM_VMOR, MM_VMNOR, MM_VMORN, MM_VMXNOR])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def mmfunct6_of_num (arg_ : Nat) : mmfunct6 :=
  match arg_ with
  | 0 => MM_VMAND
  | 1 => MM_VMNAND
  | 2 => MM_VMANDN
  | 3 => MM_VMXOR
  | 4 => MM_VMOR
  | 5 => MM_VMNOR
  | 6 => MM_VMORN
  | _ => MM_VMXNOR

def num_of_mmfunct6 (arg_ : mmfunct6) : Int :=
  match arg_ with
  | .MM_VMAND => 0
  | .MM_VMNAND => 1
  | .MM_VMANDN => 2
  | .MM_VMXOR => 3
  | .MM_VMOR => 4
  | .MM_VMNOR => 5
  | .MM_VMORN => 6
  | .MM_VMXNOR => 7

def undefined_nifunct6 (_ : Unit) : SailM nifunct6 := do
  (internal_pick [NI_VNCLIPU, NI_VNCLIP])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def nifunct6_of_num (arg_ : Nat) : nifunct6 :=
  match arg_ with
  | 0 => NI_VNCLIPU
  | _ => NI_VNCLIP

def num_of_nifunct6 (arg_ : nifunct6) : Int :=
  match arg_ with
  | .NI_VNCLIPU => 0
  | .NI_VNCLIP => 1

def undefined_nisfunct6 (_ : Unit) : SailM nisfunct6 := do
  (internal_pick [NIS_VNSRL, NIS_VNSRA])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def nisfunct6_of_num (arg_ : Nat) : nisfunct6 :=
  match arg_ with
  | 0 => NIS_VNSRL
  | _ => NIS_VNSRA

def num_of_nisfunct6 (arg_ : nisfunct6) : Int :=
  match arg_ with
  | .NIS_VNSRL => 0
  | .NIS_VNSRA => 1

def undefined_wvvfunct6 (_ : Unit) : SailM wvvfunct6 := do
  (internal_pick [WVV_VADD, WVV_VSUB, WVV_VADDU, WVV_VSUBU, WVV_VWMUL, WVV_VWMULU, WVV_VWMULSU])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def wvvfunct6_of_num (arg_ : Nat) : wvvfunct6 :=
  match arg_ with
  | 0 => WVV_VADD
  | 1 => WVV_VSUB
  | 2 => WVV_VADDU
  | 3 => WVV_VSUBU
  | 4 => WVV_VWMUL
  | 5 => WVV_VWMULU
  | _ => WVV_VWMULSU

def num_of_wvvfunct6 (arg_ : wvvfunct6) : Int :=
  match arg_ with
  | .WVV_VADD => 0
  | .WVV_VSUB => 1
  | .WVV_VADDU => 2
  | .WVV_VSUBU => 3
  | .WVV_VWMUL => 4
  | .WVV_VWMULU => 5
  | .WVV_VWMULSU => 6

def undefined_wvfunct6 (_ : Unit) : SailM wvfunct6 := do
  (internal_pick [WV_VADD, WV_VSUB, WV_VADDU, WV_VSUBU])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def wvfunct6_of_num (arg_ : Nat) : wvfunct6 :=
  match arg_ with
  | 0 => WV_VADD
  | 1 => WV_VSUB
  | 2 => WV_VADDU
  | _ => WV_VSUBU

def num_of_wvfunct6 (arg_ : wvfunct6) : Int :=
  match arg_ with
  | .WV_VADD => 0
  | .WV_VSUB => 1
  | .WV_VADDU => 2
  | .WV_VSUBU => 3

def undefined_wvxfunct6 (_ : Unit) : SailM wvxfunct6 := do
  (internal_pick [WVX_VADD, WVX_VSUB, WVX_VADDU, WVX_VSUBU, WVX_VWMUL, WVX_VWMULU, WVX_VWMULSU])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def wvxfunct6_of_num (arg_ : Nat) : wvxfunct6 :=
  match arg_ with
  | 0 => WVX_VADD
  | 1 => WVX_VSUB
  | 2 => WVX_VADDU
  | 3 => WVX_VSUBU
  | 4 => WVX_VWMUL
  | 5 => WVX_VWMULU
  | _ => WVX_VWMULSU

def num_of_wvxfunct6 (arg_ : wvxfunct6) : Int :=
  match arg_ with
  | .WVX_VADD => 0
  | .WVX_VSUB => 1
  | .WVX_VADDU => 2
  | .WVX_VSUBU => 3
  | .WVX_VWMUL => 4
  | .WVX_VWMULU => 5
  | .WVX_VWMULSU => 6

def undefined_wxfunct6 (_ : Unit) : SailM wxfunct6 := do
  (internal_pick [WX_VADD, WX_VSUB, WX_VADDU, WX_VSUBU])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def wxfunct6_of_num (arg_ : Nat) : wxfunct6 :=
  match arg_ with
  | 0 => WX_VADD
  | 1 => WX_VSUB
  | 2 => WX_VADDU
  | _ => WX_VSUBU

def num_of_wxfunct6 (arg_ : wxfunct6) : Int :=
  match arg_ with
  | .WX_VADD => 0
  | .WX_VSUB => 1
  | .WX_VADDU => 2
  | .WX_VSUBU => 3

def undefined_vextfunct6 (_ : Unit) : SailM vextfunct6 := do
  (internal_pick [VEXT2_ZVF2, VEXT2_SVF2, VEXT4_ZVF4, VEXT4_SVF4, VEXT8_ZVF8, VEXT8_SVF8])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def vextfunct6_of_num (arg_ : Nat) : vextfunct6 :=
  match arg_ with
  | 0 => VEXT2_ZVF2
  | 1 => VEXT2_SVF2
  | 2 => VEXT4_ZVF4
  | 3 => VEXT4_SVF4
  | 4 => VEXT8_ZVF8
  | _ => VEXT8_SVF8

def num_of_vextfunct6 (arg_ : vextfunct6) : Int :=
  match arg_ with
  | .VEXT2_ZVF2 => 0
  | .VEXT2_SVF2 => 1
  | .VEXT4_ZVF4 => 2
  | .VEXT4_SVF4 => 3
  | .VEXT8_ZVF8 => 4
  | .VEXT8_SVF8 => 5

def undefined_vxfunct6 (_ : Unit) : SailM vxfunct6 := do
  (internal_pick
    [VX_VADD, VX_VSUB, VX_VRSUB, VX_VMINU, VX_VMIN, VX_VMAXU, VX_VMAX, VX_VAND, VX_VOR, VX_VXOR, VX_VSADDU, VX_VSADD, VX_VSSUBU, VX_VSSUB, VX_VSLL, VX_VSMUL, VX_VSRL, VX_VSRA, VX_VSSRL, VX_VSSRA])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 19 -/
def vxfunct6_of_num (arg_ : Nat) : vxfunct6 :=
  match arg_ with
  | 0 => VX_VADD
  | 1 => VX_VSUB
  | 2 => VX_VRSUB
  | 3 => VX_VMINU
  | 4 => VX_VMIN
  | 5 => VX_VMAXU
  | 6 => VX_VMAX
  | 7 => VX_VAND
  | 8 => VX_VOR
  | 9 => VX_VXOR
  | 10 => VX_VSADDU
  | 11 => VX_VSADD
  | 12 => VX_VSSUBU
  | 13 => VX_VSSUB
  | 14 => VX_VSLL
  | 15 => VX_VSMUL
  | 16 => VX_VSRL
  | 17 => VX_VSRA
  | 18 => VX_VSSRL
  | _ => VX_VSSRA

def num_of_vxfunct6 (arg_ : vxfunct6) : Int :=
  match arg_ with
  | .VX_VADD => 0
  | .VX_VSUB => 1
  | .VX_VRSUB => 2
  | .VX_VMINU => 3
  | .VX_VMIN => 4
  | .VX_VMAXU => 5
  | .VX_VMAX => 6
  | .VX_VAND => 7
  | .VX_VOR => 8
  | .VX_VXOR => 9
  | .VX_VSADDU => 10
  | .VX_VSADD => 11
  | .VX_VSSUBU => 12
  | .VX_VSSUB => 13
  | .VX_VSLL => 14
  | .VX_VSMUL => 15
  | .VX_VSRL => 16
  | .VX_VSRA => 17
  | .VX_VSSRL => 18
  | .VX_VSSRA => 19

def undefined_vifunct6 (_ : Unit) : SailM vifunct6 := do
  (internal_pick
    [VI_VADD, VI_VRSUB, VI_VAND, VI_VOR, VI_VXOR, VI_VSADDU, VI_VSADD, VI_VSLL, VI_VSRL, VI_VSRA, VI_VSSRL, VI_VSSRA])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 11 -/
def vifunct6_of_num (arg_ : Nat) : vifunct6 :=
  match arg_ with
  | 0 => VI_VADD
  | 1 => VI_VRSUB
  | 2 => VI_VAND
  | 3 => VI_VOR
  | 4 => VI_VXOR
  | 5 => VI_VSADDU
  | 6 => VI_VSADD
  | 7 => VI_VSLL
  | 8 => VI_VSRL
  | 9 => VI_VSRA
  | 10 => VI_VSSRL
  | _ => VI_VSSRA

def num_of_vifunct6 (arg_ : vifunct6) : Int :=
  match arg_ with
  | .VI_VADD => 0
  | .VI_VRSUB => 1
  | .VI_VAND => 2
  | .VI_VOR => 3
  | .VI_VXOR => 4
  | .VI_VSADDU => 5
  | .VI_VSADD => 6
  | .VI_VSLL => 7
  | .VI_VSRL => 8
  | .VI_VSRA => 9
  | .VI_VSSRL => 10
  | .VI_VSSRA => 11

def undefined_vxsgfunct6 (_ : Unit) : SailM vxsgfunct6 := do
  (internal_pick [VX_VSLIDEUP, VX_VSLIDEDOWN, VX_VRGATHER])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def vxsgfunct6_of_num (arg_ : Nat) : vxsgfunct6 :=
  match arg_ with
  | 0 => VX_VSLIDEUP
  | 1 => VX_VSLIDEDOWN
  | _ => VX_VRGATHER

def num_of_vxsgfunct6 (arg_ : vxsgfunct6) : Int :=
  match arg_ with
  | .VX_VSLIDEUP => 0
  | .VX_VSLIDEDOWN => 1
  | .VX_VRGATHER => 2

def undefined_visgfunct6 (_ : Unit) : SailM visgfunct6 := do
  (internal_pick [VI_VSLIDEUP, VI_VSLIDEDOWN, VI_VRGATHER])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def visgfunct6_of_num (arg_ : Nat) : visgfunct6 :=
  match arg_ with
  | 0 => VI_VSLIDEUP
  | 1 => VI_VSLIDEDOWN
  | _ => VI_VRGATHER

def num_of_visgfunct6 (arg_ : visgfunct6) : Int :=
  match arg_ with
  | .VI_VSLIDEUP => 0
  | .VI_VSLIDEDOWN => 1
  | .VI_VRGATHER => 2

def undefined_mvvfunct6 (_ : Unit) : SailM mvvfunct6 := do
  (internal_pick
    [MVV_VAADDU, MVV_VAADD, MVV_VASUBU, MVV_VASUB, MVV_VMUL, MVV_VMULH, MVV_VMULHU, MVV_VMULHSU, MVV_VDIVU, MVV_VDIV, MVV_VREMU, MVV_VREM])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 11 -/
def mvvfunct6_of_num (arg_ : Nat) : mvvfunct6 :=
  match arg_ with
  | 0 => MVV_VAADDU
  | 1 => MVV_VAADD
  | 2 => MVV_VASUBU
  | 3 => MVV_VASUB
  | 4 => MVV_VMUL
  | 5 => MVV_VMULH
  | 6 => MVV_VMULHU
  | 7 => MVV_VMULHSU
  | 8 => MVV_VDIVU
  | 9 => MVV_VDIV
  | 10 => MVV_VREMU
  | _ => MVV_VREM

def num_of_mvvfunct6 (arg_ : mvvfunct6) : Int :=
  match arg_ with
  | .MVV_VAADDU => 0
  | .MVV_VAADD => 1
  | .MVV_VASUBU => 2
  | .MVV_VASUB => 3
  | .MVV_VMUL => 4
  | .MVV_VMULH => 5
  | .MVV_VMULHU => 6
  | .MVV_VMULHSU => 7
  | .MVV_VDIVU => 8
  | .MVV_VDIV => 9
  | .MVV_VREMU => 10
  | .MVV_VREM => 11

def undefined_mvvmafunct6 (_ : Unit) : SailM mvvmafunct6 := do
  (internal_pick [MVV_VMACC, MVV_VNMSAC, MVV_VMADD, MVV_VNMSUB])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def mvvmafunct6_of_num (arg_ : Nat) : mvvmafunct6 :=
  match arg_ with
  | 0 => MVV_VMACC
  | 1 => MVV_VNMSAC
  | 2 => MVV_VMADD
  | _ => MVV_VNMSUB

def num_of_mvvmafunct6 (arg_ : mvvmafunct6) : Int :=
  match arg_ with
  | .MVV_VMACC => 0
  | .MVV_VNMSAC => 1
  | .MVV_VMADD => 2
  | .MVV_VNMSUB => 3

def undefined_rmvvfunct6 (_ : Unit) : SailM rmvvfunct6 := do
  (internal_pick
    [MVV_VREDSUM, MVV_VREDAND, MVV_VREDOR, MVV_VREDXOR, MVV_VREDMINU, MVV_VREDMIN, MVV_VREDMAXU, MVV_VREDMAX])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def rmvvfunct6_of_num (arg_ : Nat) : rmvvfunct6 :=
  match arg_ with
  | 0 => MVV_VREDSUM
  | 1 => MVV_VREDAND
  | 2 => MVV_VREDOR
  | 3 => MVV_VREDXOR
  | 4 => MVV_VREDMINU
  | 5 => MVV_VREDMIN
  | 6 => MVV_VREDMAXU
  | _ => MVV_VREDMAX

def num_of_rmvvfunct6 (arg_ : rmvvfunct6) : Int :=
  match arg_ with
  | .MVV_VREDSUM => 0
  | .MVV_VREDAND => 1
  | .MVV_VREDOR => 2
  | .MVV_VREDXOR => 3
  | .MVV_VREDMINU => 4
  | .MVV_VREDMIN => 5
  | .MVV_VREDMAXU => 6
  | .MVV_VREDMAX => 7

def undefined_rivvfunct6 (_ : Unit) : SailM rivvfunct6 := do
  (internal_pick [IVV_VWREDSUMU, IVV_VWREDSUM])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def rivvfunct6_of_num (arg_ : Nat) : rivvfunct6 :=
  match arg_ with
  | 0 => IVV_VWREDSUMU
  | _ => IVV_VWREDSUM

def num_of_rivvfunct6 (arg_ : rivvfunct6) : Int :=
  match arg_ with
  | .IVV_VWREDSUMU => 0
  | .IVV_VWREDSUM => 1

def undefined_rfvvfunct6 (_ : Unit) : SailM rfvvfunct6 := do
  (internal_pick [FVV_VFREDOSUM, FVV_VFREDUSUM, FVV_VFREDMAX, FVV_VFREDMIN])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def rfvvfunct6_of_num (arg_ : Nat) : rfvvfunct6 :=
  match arg_ with
  | 0 => FVV_VFREDOSUM
  | 1 => FVV_VFREDUSUM
  | 2 => FVV_VFREDMAX
  | _ => FVV_VFREDMIN

def num_of_rfvvfunct6 (arg_ : rfvvfunct6) : Int :=
  match arg_ with
  | .FVV_VFREDOSUM => 0
  | .FVV_VFREDUSUM => 1
  | .FVV_VFREDMAX => 2
  | .FVV_VFREDMIN => 3

def undefined_rfwvvfunct6 (_ : Unit) : SailM rfwvvfunct6 := do
  (internal_pick [FVV_VFWREDOSUM, FVV_VFWREDUSUM])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def rfwvvfunct6_of_num (arg_ : Nat) : rfwvvfunct6 :=
  match arg_ with
  | 0 => FVV_VFWREDOSUM
  | _ => FVV_VFWREDUSUM

def num_of_rfwvvfunct6 (arg_ : rfwvvfunct6) : Int :=
  match arg_ with
  | .FVV_VFWREDOSUM => 0
  | .FVV_VFWREDUSUM => 1

def undefined_wmvvfunct6 (_ : Unit) : SailM wmvvfunct6 := do
  (internal_pick [WMVV_VWMACCU, WMVV_VWMACC, WMVV_VWMACCSU])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def wmvvfunct6_of_num (arg_ : Nat) : wmvvfunct6 :=
  match arg_ with
  | 0 => WMVV_VWMACCU
  | 1 => WMVV_VWMACC
  | _ => WMVV_VWMACCSU

def num_of_wmvvfunct6 (arg_ : wmvvfunct6) : Int :=
  match arg_ with
  | .WMVV_VWMACCU => 0
  | .WMVV_VWMACC => 1
  | .WMVV_VWMACCSU => 2

def undefined_mvxfunct6 (_ : Unit) : SailM mvxfunct6 := do
  (internal_pick
    [MVX_VAADDU, MVX_VAADD, MVX_VASUBU, MVX_VASUB, MVX_VSLIDE1UP, MVX_VSLIDE1DOWN, MVX_VMUL, MVX_VMULH, MVX_VMULHU, MVX_VMULHSU, MVX_VDIVU, MVX_VDIV, MVX_VREMU, MVX_VREM])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 13 -/
def mvxfunct6_of_num (arg_ : Nat) : mvxfunct6 :=
  match arg_ with
  | 0 => MVX_VAADDU
  | 1 => MVX_VAADD
  | 2 => MVX_VASUBU
  | 3 => MVX_VASUB
  | 4 => MVX_VSLIDE1UP
  | 5 => MVX_VSLIDE1DOWN
  | 6 => MVX_VMUL
  | 7 => MVX_VMULH
  | 8 => MVX_VMULHU
  | 9 => MVX_VMULHSU
  | 10 => MVX_VDIVU
  | 11 => MVX_VDIV
  | 12 => MVX_VREMU
  | _ => MVX_VREM

def num_of_mvxfunct6 (arg_ : mvxfunct6) : Int :=
  match arg_ with
  | .MVX_VAADDU => 0
  | .MVX_VAADD => 1
  | .MVX_VASUBU => 2
  | .MVX_VASUB => 3
  | .MVX_VSLIDE1UP => 4
  | .MVX_VSLIDE1DOWN => 5
  | .MVX_VMUL => 6
  | .MVX_VMULH => 7
  | .MVX_VMULHU => 8
  | .MVX_VMULHSU => 9
  | .MVX_VDIVU => 10
  | .MVX_VDIV => 11
  | .MVX_VREMU => 12
  | .MVX_VREM => 13

def undefined_mvxmafunct6 (_ : Unit) : SailM mvxmafunct6 := do
  (internal_pick [MVX_VMACC, MVX_VNMSAC, MVX_VMADD, MVX_VNMSUB])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def mvxmafunct6_of_num (arg_ : Nat) : mvxmafunct6 :=
  match arg_ with
  | 0 => MVX_VMACC
  | 1 => MVX_VNMSAC
  | 2 => MVX_VMADD
  | _ => MVX_VNMSUB

def num_of_mvxmafunct6 (arg_ : mvxmafunct6) : Int :=
  match arg_ with
  | .MVX_VMACC => 0
  | .MVX_VNMSAC => 1
  | .MVX_VMADD => 2
  | .MVX_VNMSUB => 3

def undefined_wmvxfunct6 (_ : Unit) : SailM wmvxfunct6 := do
  (internal_pick [WMVX_VWMACCU, WMVX_VWMACC, WMVX_VWMACCUS, WMVX_VWMACCSU])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def wmvxfunct6_of_num (arg_ : Nat) : wmvxfunct6 :=
  match arg_ with
  | 0 => WMVX_VWMACCU
  | 1 => WMVX_VWMACC
  | 2 => WMVX_VWMACCUS
  | _ => WMVX_VWMACCSU

def num_of_wmvxfunct6 (arg_ : wmvxfunct6) : Int :=
  match arg_ with
  | .WMVX_VWMACCU => 0
  | .WMVX_VWMACC => 1
  | .WMVX_VWMACCUS => 2
  | .WMVX_VWMACCSU => 3

def undefined_maskfunct3 (_ : Unit) : SailM maskfunct3 := do
  (internal_pick [VV_VMERGE, VI_VMERGE, VX_VMERGE])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def maskfunct3_of_num (arg_ : Nat) : maskfunct3 :=
  match arg_ with
  | 0 => VV_VMERGE
  | 1 => VI_VMERGE
  | _ => VX_VMERGE

def num_of_maskfunct3 (arg_ : maskfunct3) : Int :=
  match arg_ with
  | .VV_VMERGE => 0
  | .VI_VMERGE => 1
  | .VX_VMERGE => 2

def undefined_vlewidth (_ : Unit) : SailM vlewidth := do
  (internal_pick [VLE8, VLE16, VLE32, VLE64])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def vlewidth_of_num (arg_ : Nat) : vlewidth :=
  match arg_ with
  | 0 => VLE8
  | 1 => VLE16
  | 2 => VLE32
  | _ => VLE64

def num_of_vlewidth (arg_ : vlewidth) : Int :=
  match arg_ with
  | .VLE8 => 0
  | .VLE16 => 1
  | .VLE32 => 2
  | .VLE64 => 3

def undefined_fvvfunct6 (_ : Unit) : SailM fvvfunct6 := do
  (internal_pick
    [FVV_VADD, FVV_VSUB, FVV_VMIN, FVV_VMAX, FVV_VSGNJ, FVV_VSGNJN, FVV_VSGNJX, FVV_VDIV, FVV_VMUL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 8 -/
def fvvfunct6_of_num (arg_ : Nat) : fvvfunct6 :=
  match arg_ with
  | 0 => FVV_VADD
  | 1 => FVV_VSUB
  | 2 => FVV_VMIN
  | 3 => FVV_VMAX
  | 4 => FVV_VSGNJ
  | 5 => FVV_VSGNJN
  | 6 => FVV_VSGNJX
  | 7 => FVV_VDIV
  | _ => FVV_VMUL

def num_of_fvvfunct6 (arg_ : fvvfunct6) : Int :=
  match arg_ with
  | .FVV_VADD => 0
  | .FVV_VSUB => 1
  | .FVV_VMIN => 2
  | .FVV_VMAX => 3
  | .FVV_VSGNJ => 4
  | .FVV_VSGNJN => 5
  | .FVV_VSGNJX => 6
  | .FVV_VDIV => 7
  | .FVV_VMUL => 8

def undefined_fvvmafunct6 (_ : Unit) : SailM fvvmafunct6 := do
  (internal_pick
    [FVV_VMADD, FVV_VNMADD, FVV_VMSUB, FVV_VNMSUB, FVV_VMACC, FVV_VNMACC, FVV_VMSAC, FVV_VNMSAC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def fvvmafunct6_of_num (arg_ : Nat) : fvvmafunct6 :=
  match arg_ with
  | 0 => FVV_VMADD
  | 1 => FVV_VNMADD
  | 2 => FVV_VMSUB
  | 3 => FVV_VNMSUB
  | 4 => FVV_VMACC
  | 5 => FVV_VNMACC
  | 6 => FVV_VMSAC
  | _ => FVV_VNMSAC

def num_of_fvvmafunct6 (arg_ : fvvmafunct6) : Int :=
  match arg_ with
  | .FVV_VMADD => 0
  | .FVV_VNMADD => 1
  | .FVV_VMSUB => 2
  | .FVV_VNMSUB => 3
  | .FVV_VMACC => 4
  | .FVV_VNMACC => 5
  | .FVV_VMSAC => 6
  | .FVV_VNMSAC => 7

def undefined_fwvvfunct6 (_ : Unit) : SailM fwvvfunct6 := do
  (internal_pick [FWVV_VADD, FWVV_VSUB, FWVV_VMUL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def fwvvfunct6_of_num (arg_ : Nat) : fwvvfunct6 :=
  match arg_ with
  | 0 => FWVV_VADD
  | 1 => FWVV_VSUB
  | _ => FWVV_VMUL

def num_of_fwvvfunct6 (arg_ : fwvvfunct6) : Int :=
  match arg_ with
  | .FWVV_VADD => 0
  | .FWVV_VSUB => 1
  | .FWVV_VMUL => 2

def undefined_fwvvmafunct6 (_ : Unit) : SailM fwvvmafunct6 := do
  (internal_pick [FWVV_VMACC, FWVV_VNMACC, FWVV_VMSAC, FWVV_VNMSAC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def fwvvmafunct6_of_num (arg_ : Nat) : fwvvmafunct6 :=
  match arg_ with
  | 0 => FWVV_VMACC
  | 1 => FWVV_VNMACC
  | 2 => FWVV_VMSAC
  | _ => FWVV_VNMSAC

def num_of_fwvvmafunct6 (arg_ : fwvvmafunct6) : Int :=
  match arg_ with
  | .FWVV_VMACC => 0
  | .FWVV_VNMACC => 1
  | .FWVV_VMSAC => 2
  | .FWVV_VNMSAC => 3

def undefined_fwvfunct6 (_ : Unit) : SailM fwvfunct6 := do
  (internal_pick [FWV_VADD, FWV_VSUB])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def fwvfunct6_of_num (arg_ : Nat) : fwvfunct6 :=
  match arg_ with
  | 0 => FWV_VADD
  | _ => FWV_VSUB

def num_of_fwvfunct6 (arg_ : fwvfunct6) : Int :=
  match arg_ with
  | .FWV_VADD => 0
  | .FWV_VSUB => 1

def undefined_fvvmfunct6 (_ : Unit) : SailM fvvmfunct6 := do
  (internal_pick [FVVM_VMFEQ, FVVM_VMFLE, FVVM_VMFLT, FVVM_VMFNE])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def fvvmfunct6_of_num (arg_ : Nat) : fvvmfunct6 :=
  match arg_ with
  | 0 => FVVM_VMFEQ
  | 1 => FVVM_VMFLE
  | 2 => FVVM_VMFLT
  | _ => FVVM_VMFNE

def num_of_fvvmfunct6 (arg_ : fvvmfunct6) : Int :=
  match arg_ with
  | .FVVM_VMFEQ => 0
  | .FVVM_VMFLE => 1
  | .FVVM_VMFLT => 2
  | .FVVM_VMFNE => 3

def undefined_vfunary0 (_ : Unit) : SailM vfunary0 := do
  (internal_pick [FV_CVT_XU_F, FV_CVT_X_F, FV_CVT_F_XU, FV_CVT_F_X, FV_CVT_RTZ_XU_F, FV_CVT_RTZ_X_F])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def vfunary0_of_num (arg_ : Nat) : vfunary0 :=
  match arg_ with
  | 0 => FV_CVT_XU_F
  | 1 => FV_CVT_X_F
  | 2 => FV_CVT_F_XU
  | 3 => FV_CVT_F_X
  | 4 => FV_CVT_RTZ_XU_F
  | _ => FV_CVT_RTZ_X_F

def num_of_vfunary0 (arg_ : vfunary0) : Int :=
  match arg_ with
  | .FV_CVT_XU_F => 0
  | .FV_CVT_X_F => 1
  | .FV_CVT_F_XU => 2
  | .FV_CVT_F_X => 3
  | .FV_CVT_RTZ_XU_F => 4
  | .FV_CVT_RTZ_X_F => 5

def undefined_vfwunary0 (_ : Unit) : SailM vfwunary0 := do
  (internal_pick
    [FWV_CVT_XU_F, FWV_CVT_X_F, FWV_CVT_F_XU, FWV_CVT_F_X, FWV_CVT_F_F, FWV_CVT_RTZ_XU_F, FWV_CVT_RTZ_X_F])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def vfwunary0_of_num (arg_ : Nat) : vfwunary0 :=
  match arg_ with
  | 0 => FWV_CVT_XU_F
  | 1 => FWV_CVT_X_F
  | 2 => FWV_CVT_F_XU
  | 3 => FWV_CVT_F_X
  | 4 => FWV_CVT_F_F
  | 5 => FWV_CVT_RTZ_XU_F
  | _ => FWV_CVT_RTZ_X_F

def num_of_vfwunary0 (arg_ : vfwunary0) : Int :=
  match arg_ with
  | .FWV_CVT_XU_F => 0
  | .FWV_CVT_X_F => 1
  | .FWV_CVT_F_XU => 2
  | .FWV_CVT_F_X => 3
  | .FWV_CVT_F_F => 4
  | .FWV_CVT_RTZ_XU_F => 5
  | .FWV_CVT_RTZ_X_F => 6

def undefined_vfnunary0 (_ : Unit) : SailM vfnunary0 := do
  (internal_pick
    [FNV_CVT_XU_F, FNV_CVT_X_F, FNV_CVT_F_XU, FNV_CVT_F_X, FNV_CVT_F_F, FNV_CVT_ROD_F_F, FNV_CVT_RTZ_XU_F, FNV_CVT_RTZ_X_F])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def vfnunary0_of_num (arg_ : Nat) : vfnunary0 :=
  match arg_ with
  | 0 => FNV_CVT_XU_F
  | 1 => FNV_CVT_X_F
  | 2 => FNV_CVT_F_XU
  | 3 => FNV_CVT_F_X
  | 4 => FNV_CVT_F_F
  | 5 => FNV_CVT_ROD_F_F
  | 6 => FNV_CVT_RTZ_XU_F
  | _ => FNV_CVT_RTZ_X_F

def num_of_vfnunary0 (arg_ : vfnunary0) : Int :=
  match arg_ with
  | .FNV_CVT_XU_F => 0
  | .FNV_CVT_X_F => 1
  | .FNV_CVT_F_XU => 2
  | .FNV_CVT_F_X => 3
  | .FNV_CVT_F_F => 4
  | .FNV_CVT_ROD_F_F => 5
  | .FNV_CVT_RTZ_XU_F => 6
  | .FNV_CVT_RTZ_X_F => 7

def undefined_vfunary1 (_ : Unit) : SailM vfunary1 := do
  (internal_pick [FVV_VSQRT, FVV_VRSQRT7, FVV_VREC7, FVV_VCLASS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def vfunary1_of_num (arg_ : Nat) : vfunary1 :=
  match arg_ with
  | 0 => FVV_VSQRT
  | 1 => FVV_VRSQRT7
  | 2 => FVV_VREC7
  | _ => FVV_VCLASS

def num_of_vfunary1 (arg_ : vfunary1) : Int :=
  match arg_ with
  | .FVV_VSQRT => 0
  | .FVV_VRSQRT7 => 1
  | .FVV_VREC7 => 2
  | .FVV_VCLASS => 3

def undefined_fvffunct6 (_ : Unit) : SailM fvffunct6 := do
  (internal_pick
    [VF_VADD, VF_VSUB, VF_VMIN, VF_VMAX, VF_VSGNJ, VF_VSGNJN, VF_VSGNJX, VF_VDIV, VF_VRDIV, VF_VMUL, VF_VRSUB, VF_VSLIDE1UP, VF_VSLIDE1DOWN])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 12 -/
def fvffunct6_of_num (arg_ : Nat) : fvffunct6 :=
  match arg_ with
  | 0 => VF_VADD
  | 1 => VF_VSUB
  | 2 => VF_VMIN
  | 3 => VF_VMAX
  | 4 => VF_VSGNJ
  | 5 => VF_VSGNJN
  | 6 => VF_VSGNJX
  | 7 => VF_VDIV
  | 8 => VF_VRDIV
  | 9 => VF_VMUL
  | 10 => VF_VRSUB
  | 11 => VF_VSLIDE1UP
  | _ => VF_VSLIDE1DOWN

def num_of_fvffunct6 (arg_ : fvffunct6) : Int :=
  match arg_ with
  | .VF_VADD => 0
  | .VF_VSUB => 1
  | .VF_VMIN => 2
  | .VF_VMAX => 3
  | .VF_VSGNJ => 4
  | .VF_VSGNJN => 5
  | .VF_VSGNJX => 6
  | .VF_VDIV => 7
  | .VF_VRDIV => 8
  | .VF_VMUL => 9
  | .VF_VRSUB => 10
  | .VF_VSLIDE1UP => 11
  | .VF_VSLIDE1DOWN => 12

def undefined_fvfmafunct6 (_ : Unit) : SailM fvfmafunct6 := do
  (internal_pick
    [VF_VMADD, VF_VNMADD, VF_VMSUB, VF_VNMSUB, VF_VMACC, VF_VNMACC, VF_VMSAC, VF_VNMSAC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def fvfmafunct6_of_num (arg_ : Nat) : fvfmafunct6 :=
  match arg_ with
  | 0 => VF_VMADD
  | 1 => VF_VNMADD
  | 2 => VF_VMSUB
  | 3 => VF_VNMSUB
  | 4 => VF_VMACC
  | 5 => VF_VNMACC
  | 6 => VF_VMSAC
  | _ => VF_VNMSAC

def num_of_fvfmafunct6 (arg_ : fvfmafunct6) : Int :=
  match arg_ with
  | .VF_VMADD => 0
  | .VF_VNMADD => 1
  | .VF_VMSUB => 2
  | .VF_VNMSUB => 3
  | .VF_VMACC => 4
  | .VF_VNMACC => 5
  | .VF_VMSAC => 6
  | .VF_VNMSAC => 7

def undefined_fwvffunct6 (_ : Unit) : SailM fwvffunct6 := do
  (internal_pick [FWVF_VADD, FWVF_VSUB, FWVF_VMUL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def fwvffunct6_of_num (arg_ : Nat) : fwvffunct6 :=
  match arg_ with
  | 0 => FWVF_VADD
  | 1 => FWVF_VSUB
  | _ => FWVF_VMUL

def num_of_fwvffunct6 (arg_ : fwvffunct6) : Int :=
  match arg_ with
  | .FWVF_VADD => 0
  | .FWVF_VSUB => 1
  | .FWVF_VMUL => 2

def undefined_fwvfmafunct6 (_ : Unit) : SailM fwvfmafunct6 := do
  (internal_pick [FWVF_VMACC, FWVF_VNMACC, FWVF_VMSAC, FWVF_VNMSAC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def fwvfmafunct6_of_num (arg_ : Nat) : fwvfmafunct6 :=
  match arg_ with
  | 0 => FWVF_VMACC
  | 1 => FWVF_VNMACC
  | 2 => FWVF_VMSAC
  | _ => FWVF_VNMSAC

def num_of_fwvfmafunct6 (arg_ : fwvfmafunct6) : Int :=
  match arg_ with
  | .FWVF_VMACC => 0
  | .FWVF_VNMACC => 1
  | .FWVF_VMSAC => 2
  | .FWVF_VNMSAC => 3

def undefined_fwffunct6 (_ : Unit) : SailM fwffunct6 := do
  (internal_pick [FWF_VADD, FWF_VSUB])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def fwffunct6_of_num (arg_ : Nat) : fwffunct6 :=
  match arg_ with
  | 0 => FWF_VADD
  | _ => FWF_VSUB

def num_of_fwffunct6 (arg_ : fwffunct6) : Int :=
  match arg_ with
  | .FWF_VADD => 0
  | .FWF_VSUB => 1

def undefined_fvfmfunct6 (_ : Unit) : SailM fvfmfunct6 := do
  (internal_pick [VFM_VMFEQ, VFM_VMFLE, VFM_VMFLT, VFM_VMFNE, VFM_VMFGT, VFM_VMFGE])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def fvfmfunct6_of_num (arg_ : Nat) : fvfmfunct6 :=
  match arg_ with
  | 0 => VFM_VMFEQ
  | 1 => VFM_VMFLE
  | 2 => VFM_VMFLT
  | 3 => VFM_VMFNE
  | 4 => VFM_VMFGT
  | _ => VFM_VMFGE

def num_of_fvfmfunct6 (arg_ : fvfmfunct6) : Int :=
  match arg_ with
  | .VFM_VMFEQ => 0
  | .VFM_VMFLE => 1
  | .VFM_VMFLT => 2
  | .VFM_VMFNE => 3
  | .VFM_VMFGT => 4
  | .VFM_VMFGE => 5

def undefined_vmlsop (_ : Unit) : SailM vmlsop := do
  (internal_pick [VLM, VSM])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def vmlsop_of_num (arg_ : Nat) : vmlsop :=
  match arg_ with
  | 0 => VLM
  | _ => VSM

def num_of_vmlsop (arg_ : vmlsop) : Int :=
  match arg_ with
  | .VLM => 0
  | .VSM => 1

def undefined_indexed_mop (_ : Unit) : SailM indexed_mop := do
  (internal_pick [INDEXED_UNORDERED, INDEXED_ORDERED])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def indexed_mop_of_num (arg_ : Nat) : indexed_mop :=
  match arg_ with
  | 0 => INDEXED_UNORDERED
  | _ => INDEXED_ORDERED

def num_of_indexed_mop (arg_ : indexed_mop) : Int :=
  match arg_ with
  | .INDEXED_UNORDERED => 0
  | .INDEXED_ORDERED => 1

def undefined_vstart_class (_ : Unit) : SailM vstart_class := do
  (internal_pick [VSTART_ARITH, VSTART_LOAD_STORE, VSTART_SCALAR_MOVE, VSTART_MANDATORY])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def vstart_class_of_num (arg_ : Nat) : vstart_class :=
  match arg_ with
  | 0 => VSTART_ARITH
  | 1 => VSTART_LOAD_STORE
  | 2 => VSTART_SCALAR_MOVE
  | _ => VSTART_MANDATORY

def num_of_vstart_class (arg_ : vstart_class) : Int :=
  match arg_ with
  | .VSTART_ARITH => 0
  | .VSTART_LOAD_STORE => 1
  | .VSTART_SCALAR_MOVE => 2
  | .VSTART_MANDATORY => 3

