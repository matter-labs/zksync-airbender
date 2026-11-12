import SailRV32.SailRV32
import SailRV32.Prelude
import SailRV32.Errors
import SailRV32.PlatformConfig
import SailRV32.MemTypeUtils
import SailRV32.SysRegs
import SailRV32.Smcntrpmf
import SailRV32.SimpleInterruptGenerator

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

def htif_tohost_size := 8

def enable_htif (tohost_addr : (BitVec 64)) : SailM Unit := do
  writeReg htif_tohost_base (some (trunc (m := 34) tohost_addr))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_clint (typ_0 : physaddr) (width : Nat) : SailM Bool := do
  let .Physaddr addr : physaddr := typ_0
  if ((not plat_have_clint) : Bool)
  then (pure false)
  else
    (do
      if (((BitVec.toNatInt (← readReg mhartid)) ≥b 4095) : Bool)
      then (pure false)
      else
        (let addr_int := (BitVec.toNatInt addr)
        let clint_base_int := (BitVec.toNatInt plat_clint_base)
        let clint_size_int := (BitVec.toNatInt plat_clint_size)
        (pure ((clint_base_int ≤b addr_int) && ((addr_int +i width) ≤b (clint_base_int +i clint_size_int))))))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_sig (typ_0 : physaddr) (width : Nat) : SailM Bool := do
  let .Physaddr addr : physaddr := typ_0
  if ((not plat_have_sig) : Bool)
  then (pure false)
  else
    (let addr_int := (BitVec.toNatInt addr)
    let sig_base_int := (BitVec.toNatInt plat_sig_base)
    let sig_size_int := (BitVec.toNatInt plat_sig_size)
    (pure ((sig_base_int ≤b addr_int) && ((addr_int +i width) ≤b (sig_base_int +i sig_size_int)))))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_htif_writable (typ_0 : physaddr) (width : Nat) : SailM Bool := do
  let .Physaddr addr : physaddr := typ_0
  match (← readReg htif_tohost_base) with
  | none => (pure false)
  | .some base =>
    (pure ((zopz0zI_u addr (BitVec.addInt base htif_tohost_size)) && (zopz0zK_u
          (BitVec.addInt addr width) base)))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_htif_readable (addr : physaddr) (width : Nat) : SailM Bool := do
  (within_htif_writable addr width)

def MSIP_BASE : physaddrbits := (zero_extend (m := 34) 0x00000#20)

def MTIMECMP_BASE : physaddrbits := (zero_extend (m := 34) 0x04000#20)

def MTIMECMP_BASE_HI : physaddrbits := (zero_extend (m := 34) 0x04004#20)

def MTIME_BASE : physaddrbits := (zero_extend (m := 34) 0x0BFF8#20)

def MTIME_BASE_HI : physaddrbits := (zero_extend (m := 34) 0x0BFFC#20)

/-- Type quantifiers: width : Nat, width ≥ 0, width > 0 -/
def clint_load (access : (MemoryAccessType mem_payload)) (paddr : physaddr) (width : Nat) : SailM (Result (BitVec (8 * width)) (physaddr × ExceptionType)) := do
  let hart_msip_addr ← do
    (pure (MSIP_BASE + (zero_extend (m := 34) ((← readReg mhartid) <<< 2))))
  let hart_mtimecmp_addr ← do
    (pure (MTIMECMP_BASE + (zero_extend (m := 34) ((← readReg mhartid) <<< 3))))
  let hart_mtimecmp_hi_addr ← do
    (pure (MTIMECMP_BASE_HI + (zero_extend (m := 34) ((← readReg mhartid) <<< 3))))
  let .Physaddr addr := paddr
  let addr := (addr - plat_clint_base)
  if (((addr == hart_msip_addr) && ((width == 8) || (width == 4))) : Bool)
  then
    (do
      if ((get_config_print_clint ()) : Bool)
      then
        (pure (print_endline
            (HAppend.hAppend "clint["
              (HAppend.hAppend (BitVec.toFormatted addr)
                (HAppend.hAppend "] -> " (BitVec.toFormatted (← readReg msip)))))))
      else (pure ())
      (pure (Ok (zero_extend (m := (8 *i width)) (← readReg msip)))))
  else
    (do
      if (((addr == hart_mtimecmp_addr) && (width == 4)) : Bool)
      then
        (do
          if ((get_config_print_clint ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "clint<4>["
                  (HAppend.hAppend (BitVec.toFormatted addr)
                    (HAppend.hAppend "] -> "
                      (BitVec.toFormatted (Sail.BitVec.extractLsb (← readReg mtimecmp) 31 0)))))))
          else (pure ())
          (pure (Ok (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg mtimecmp) 31 0)))))
      else
        (do
          if (((addr == hart_mtimecmp_addr) && (width == 8)) : Bool)
          then
            (do
              if ((get_config_print_clint ()) : Bool)
              then
                (pure (print_endline
                    (HAppend.hAppend "clint<8>["
                      (HAppend.hAppend (BitVec.toFormatted addr)
                        (HAppend.hAppend "] -> " (BitVec.toFormatted (← readReg mtimecmp)))))))
              else (pure ())
              (pure (Ok (zero_extend (m := 64) (← readReg mtimecmp)))))
          else
            (do
              if (((addr == hart_mtimecmp_hi_addr) && (width == 4)) : Bool)
              then
                (do
                  if ((get_config_print_clint ()) : Bool)
                  then
                    (pure (print_endline
                        (HAppend.hAppend "clint-hi<4>["
                          (HAppend.hAppend (BitVec.toFormatted addr)
                            (HAppend.hAppend "] -> "
                              (BitVec.toFormatted
                                (Sail.BitVec.extractLsb (← readReg mtimecmp) 63 32)))))))
                  else (pure ())
                  (pure (Ok
                      (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg mtimecmp) 63 32)))))
              else
                (do
                  if (((addr == MTIME_BASE) && (width == 4)) : Bool)
                  then
                    (do
                      if ((get_config_print_clint ()) : Bool)
                      then
                        (pure (print_endline
                            (HAppend.hAppend "clint["
                              (HAppend.hAppend (BitVec.toFormatted addr)
                                (HAppend.hAppend "] -> " (BitVec.toFormatted (← readReg mtime)))))))
                      else (pure ())
                      (pure (Ok
                          (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg mtime) 31 0)))))
                  else
                    (do
                      if (((addr == MTIME_BASE) && (width == 8)) : Bool)
                      then
                        (do
                          if ((get_config_print_clint ()) : Bool)
                          then
                            (pure (print_endline
                                (HAppend.hAppend "clint["
                                  (HAppend.hAppend (BitVec.toFormatted addr)
                                    (HAppend.hAppend "] -> "
                                      (BitVec.toFormatted (← readReg mtime)))))))
                          else (pure ())
                          (pure (Ok (zero_extend (m := 64) (← readReg mtime)))))
                      else
                        (do
                          if (((addr == MTIME_BASE_HI) && (width == 4)) : Bool)
                          then
                            (do
                              if ((get_config_print_clint ()) : Bool)
                              then
                                (pure (print_endline
                                    (HAppend.hAppend "clint["
                                      (HAppend.hAppend (BitVec.toFormatted addr)
                                        (HAppend.hAppend "] -> "
                                          (BitVec.toFormatted (← readReg mtime)))))))
                              else (pure ())
                              (pure (Ok
                                  (zero_extend (m := 32)
                                    (Sail.BitVec.extractLsb (← readReg mtime) 63 32)))))
                          else
                            (do
                              let _ : Unit :=
                                if ((get_config_print_clint ()) : Bool)
                                then
                                  (print_endline
                                    (HAppend.hAppend "clint["
                                      (HAppend.hAppend (BitVec.toFormatted addr) "] -> <not-mapped>")))
                                else ()
                              (pure (Err (paddr, (← (accessFaultFromAccessType access))))))))))))

/-- Type quantifiers: width : Nat, width ≥ 0, width > 0 -/
def clint_store (paddr : physaddr) (width : Nat) (data : (BitVec (8 * width))) : SailM (Result Bool (physaddr × ExceptionType)) := do
  let hart_msip_addr ← do
    (pure (MSIP_BASE + (zero_extend (m := 34) ((← readReg mhartid) <<< 2))))
  let hart_mtimecmp_addr ← do
    (pure (MTIMECMP_BASE + (zero_extend (m := 34) ((← readReg mhartid) <<< 3))))
  let hart_mtimecmp_hi_addr ← do
    (pure (MTIMECMP_BASE_HI + (zero_extend (m := 34) ((← readReg mhartid) <<< 3))))
  let .Physaddr addr := paddr
  let addr := (addr - plat_clint_base)
  if (((addr == hart_msip_addr) && ((width == 8) || (width == 4))) : Bool)
  then
    (do
      let _ : Unit :=
        if ((get_config_print_clint ()) : Bool)
        then
          (print_endline
            (HAppend.hAppend "clint["
              (HAppend.hAppend (BitVec.toFormatted addr)
                (HAppend.hAppend "] <- "
                  (HAppend.hAppend (BitVec.toFormatted data)
                    (HAppend.hAppend " (msip <- " (HAppend.hAppend (BitVec.toFormatted data) ")")))))))
        else ()
      writeReg msip (BitVec.update (← readReg msip) 0 (BitVec.access data 0))
      (pure (Ok true)))
  else
    (do
      if (((addr == hart_mtimecmp_addr) && (width == 8)) : Bool)
      then
        (do
          let _ : Unit :=
            if ((get_config_print_clint ()) : Bool)
            then
              (print_endline
                (HAppend.hAppend "clint<8>["
                  (HAppend.hAppend (BitVec.toFormatted addr)
                    (HAppend.hAppend "] <- "
                      (HAppend.hAppend (BitVec.toFormatted data) " (mtimecmp)")))))
            else ()
          writeReg mtimecmp (zero_extend (m := 64) data)
          (pure (Ok true)))
      else
        (do
          if (((addr == hart_mtimecmp_addr) && (width == 4)) : Bool)
          then
            (do
              let _ : Unit :=
                if ((get_config_print_clint ()) : Bool)
                then
                  (print_endline
                    (HAppend.hAppend "clint<4>["
                      (HAppend.hAppend (BitVec.toFormatted addr)
                        (HAppend.hAppend "] <- "
                          (HAppend.hAppend (BitVec.toFormatted data) " (mtimecmp)")))))
                else ()
              writeReg mtimecmp (Sail.BitVec.updateSubrange (← readReg mtimecmp) 31 0
                (zero_extend (m := 32) data))
              (pure (Ok true)))
          else
            (do
              if (((addr == hart_mtimecmp_hi_addr) && (width == 4)) : Bool)
              then
                (do
                  let _ : Unit :=
                    if ((get_config_print_clint ()) : Bool)
                    then
                      (print_endline
                        (HAppend.hAppend "clint<4>["
                          (HAppend.hAppend (BitVec.toFormatted addr)
                            (HAppend.hAppend "] <- "
                              (HAppend.hAppend (BitVec.toFormatted data) " (mtimecmp)")))))
                    else ()
                  writeReg mtimecmp (Sail.BitVec.updateSubrange (← readReg mtimecmp) 63 32
                    (zero_extend (m := 32) data))
                  (pure (Ok true)))
              else
                (do
                  if (((addr == MTIME_BASE) && (width == 8)) : Bool)
                  then
                    (do
                      let _ : Unit :=
                        if ((get_config_print_clint ()) : Bool)
                        then
                          (print_endline
                            (HAppend.hAppend "clint<8>["
                              (HAppend.hAppend (BitVec.toFormatted addr)
                                (HAppend.hAppend "] <- "
                                  (HAppend.hAppend (BitVec.toFormatted data) " (mtime)")))))
                        else ()
                      writeReg mtime data
                      (pure (Ok true)))
                  else
                    (do
                      if (((addr == MTIME_BASE) && (width == 4)) : Bool)
                      then
                        (do
                          let _ : Unit :=
                            if ((get_config_print_clint ()) : Bool)
                            then
                              (print_endline
                                (HAppend.hAppend "clint<4>["
                                  (HAppend.hAppend (BitVec.toFormatted addr)
                                    (HAppend.hAppend "] <- "
                                      (HAppend.hAppend (BitVec.toFormatted data) " (mtime)")))))
                            else ()
                          writeReg mtime (Sail.BitVec.updateSubrange (← readReg mtime) 31 0 data)
                          (pure (Ok true)))
                      else
                        (do
                          if (((addr == MTIME_BASE_HI) && (width == 4)) : Bool)
                          then
                            (do
                              let _ : Unit :=
                                if ((get_config_print_clint ()) : Bool)
                                then
                                  (print_endline
                                    (HAppend.hAppend "clint<4>["
                                      (HAppend.hAppend (BitVec.toFormatted addr)
                                        (HAppend.hAppend "] <- "
                                          (HAppend.hAppend (BitVec.toFormatted data) " (mtime)")))))
                                else ()
                              writeReg mtime (Sail.BitVec.updateSubrange (← readReg mtime) 63 32
                                data)
                              (pure (Ok true)))
                          else
                            (let _ : Unit :=
                              if ((get_config_print_clint ()) : Bool)
                              then
                                (print_endline
                                  (HAppend.hAppend "clint["
                                    (HAppend.hAppend (BitVec.toFormatted addr)
                                      (HAppend.hAppend "] <- "
                                        (HAppend.hAppend (BitVec.toFormatted data) " (<unmapped>)")))))
                              else ()
                            (pure (Err (paddr, (E_SAMO_Access_Fault ())))))))))))

def should_inc_mcycle (priv : Privilege) : SailM Bool := do
  (pure (((_get_Counterin_CY (← readReg mcountinhibit)) == 0#1) && ((counter_priv_filter_bit
          (← readReg mcyclecfg) priv) == 0#1)))

def should_inc_minstret (priv : Privilege) : SailM Bool := do
  (pure (((_get_Counterin_IR (← readReg mcountinhibit)) == 0#1) && ((counter_priv_filter_bit
          (← readReg minstretcfg) priv) == 0#1)))

def clint_tick_clock (_ : Unit) : SailM Unit := do
  if ((← (should_inc_mcycle (← readReg cur_privilege))) : Bool)
  then writeReg mcycle (BitVec.addInt (← readReg mcycle) 1)
  else (pure ())
  writeReg mtime (BitVec.addInt (← readReg mtime) 1)

def undefined_htif_cmd (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_htif_cmd (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_htif_cmd_cmd (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _update_htif_cmd_cmd (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _set_htif_cmd_cmd (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_htif_cmd_cmd r v)

def _get_htif_cmd_device (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _update_htif_cmd_device (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def _set_htif_cmd_device (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_htif_cmd_device r v)

def _get_htif_cmd_payload (v : (BitVec 64)) : (BitVec 48) :=
  (Sail.BitVec.extractLsb v 47 0)

def _update_htif_cmd_payload (v : (BitVec 64)) (x : (BitVec 48)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 0 x)

def _set_htif_cmd_payload (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 48)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_htif_cmd_payload r v)

def reset_htif (_ : Unit) : SailM Unit := do
  writeReg htif_cmd_write 0#1
  writeReg htif_payload_writes 0x0#4
  writeReg htif_tohost (zeros (n := 64))

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def htif_load (access : (MemoryAccessType mem_payload)) (addr : physaddr) (width : Nat) : SailM (Result (BitVec (8 * width)) (physaddr × ExceptionType)) := do
  let .Physaddr paddr := addr
  if ((get_config_print_htif ()) : Bool)
  then
    (pure (print_endline
        (HAppend.hAppend "htif["
          (HAppend.hAppend (hex_bits_str paddr)
            (HAppend.hAppend "] -> " (BitVec.toFormatted (← readReg htif_tohost)))))))
  else (pure ())
  let base ← (( do
    match (← readReg htif_tohost_base) with
    | .some base => (pure base)
    | none => (internal_error "sys/platform.sail" 286 "HTIF load while HTIF isn't enabled") ) :
    SailM physaddrbits )
  if (((width == 8) && (paddr == base)) : Bool)
  then (pure (Ok (zero_extend (m := 64) (← readReg htif_tohost))))
  else
    (do
      if (((width == 4) && (paddr == base)) : Bool)
      then
        (pure (Ok (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg htif_tohost) 31 0))))
      else
        (do
          if (((width == 4) && (paddr == (BitVec.addInt base 4))) : Bool)
          then
            (pure (Ok
                (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg htif_tohost) 63 32))))
          else (pure (Err (addr, (← (accessFaultFromAccessType access)))))))

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def htif_store (addr : physaddr) (width : Nat) (data : (BitVec (8 * width))) : SailM (Result Bool (physaddr × ExceptionType)) := SailME.run do
  let .Physaddr paddr := addr
  let _ : Unit :=
    if ((get_config_print_htif ()) : Bool)
    then
      (print_endline
        (HAppend.hAppend "htif["
          (HAppend.hAppend (hex_bits_str paddr) (HAppend.hAppend "] <- " (BitVec.toFormatted data)))))
    else ()
  let base ← (( do
    match (← readReg htif_tohost_base) with
    | .some base => (pure base)
    | none => (internal_error "sys/platform.sail" 307 "HTIF store while HTIF isn't enabled") ) :
    SailME (Result Bool (physaddr × ExceptionType)) physaddrbits )
  if (((width == 8) && (paddr == base)) : Bool)
  then
    (do
      writeReg htif_cmd_write 1#1
      writeReg htif_payload_writes (BitVec.addInt (← readReg htif_payload_writes) 1)
      writeReg htif_tohost (zero_extend (m := 64) data))
  else
    (do
      if (((width == 4) && (paddr == base)) : Bool)
      then
        (do
          if ((data == (Sail.BitVec.extractLsb (← readReg htif_tohost) 31 0)) : Bool)
          then writeReg htif_payload_writes (BitVec.addInt (← readReg htif_payload_writes) 1)
          else writeReg htif_payload_writes 0x1#4
          writeReg htif_tohost (Sail.BitVec.updateSubrange (← readReg htif_tohost) 31 0 data))
      else
        (do
          if (((width == 4) && (paddr == (BitVec.addInt base 4))) : Bool)
          then
            (do
              if (((Sail.BitVec.extractLsb data 15 0) == (Sail.BitVec.extractLsb
                     (← readReg htif_tohost) 47 32)) : Bool)
              then writeReg htif_payload_writes (BitVec.addInt (← readReg htif_payload_writes) 1)
              else writeReg htif_payload_writes 0x1#4
              writeReg htif_cmd_write 1#1
              writeReg htif_tohost (Sail.BitVec.updateSubrange (← readReg htif_tohost) 63 32 data))
          else
            SailME.throw ((Err (addr, (E_SAMO_Access_Fault ()))) : (Result Bool (physaddr × ExceptionType)))))
  if (((((← readReg htif_cmd_write) == 1#1) && (← do
           (pure ((BitVec.toNatInt (← readReg htif_payload_writes)) >b 0)))) || (← do
         (pure ((BitVec.toNatInt (← readReg htif_payload_writes)) >b 2)))) : Bool)
  then
    (do
      let cmd ← do (pure (Mk_htif_cmd (← readReg htif_tohost)))
      match (_get_htif_cmd_device cmd) with
      | 0x00 =>
        (do
          let _ : Unit :=
            if ((get_config_print_htif ()) : Bool)
            then
              (print_endline
                (HAppend.hAppend "htif-syscall-proxy cmd: "
                  (BitVec.toFormatted (_get_htif_cmd_payload cmd))))
            else ()
          if (((BitVec.access (_get_htif_cmd_payload cmd) 0) == 1#1) : Bool)
          then
            (do
              writeReg htif_done true
              writeReg htif_exit_code ((zero_extend (m := 64) (_get_htif_cmd_payload cmd)) >>> 1))
          else (pure ()))
      | 0x01 =>
        (do
          let _ : Unit :=
            if ((get_config_print_htif ()) : Bool)
            then
              (print_endline
                (HAppend.hAppend "htif-term cmd: " (BitVec.toFormatted (_get_htif_cmd_payload cmd))))
            else ()
          match (_get_htif_cmd_cmd cmd) with
          | 0x00 => (pure ())
          | 0x01 => (plat_term_write (Sail.BitVec.extractLsb (_get_htif_cmd_payload cmd) 7 0))
          | c => (pure (print (HAppend.hAppend "Unknown term cmd: " (BitVec.toFormatted c))))
          (reset_htif ()))
      | _ => (pure (print (HAppend.hAppend "htif-???? cmd: " (BitVec.toFormatted data)))))
  else (pure ())
  (pure (Ok true))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_mmio_readable (addr : physaddr) (width : Nat) : SailM Bool := do
  if ((get_config_rvfi ()) : Bool)
  then (pure false)
  else
    (pure ((← (within_clint addr width)) || ((← (within_sig addr width)) || ((← (within_htif_readable
                addr width)) && (1 ≤b width)))))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def within_mmio_writable (addr : physaddr) (width : Nat) : SailM Bool := do
  if ((get_config_rvfi ()) : Bool)
  then (pure false)
  else
    (pure ((← (within_clint addr width)) || ((← (within_sig addr width)) || ((← (within_htif_writable
                addr width)) && (width ≤b 8)))))

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mmio_read (access : (MemoryAccessType mem_payload)) (paddr : physaddr) (width : Nat) : SailM (Result (BitVec (8 * width)) (physaddr × ExceptionType)) := do
  if ((← (within_clint paddr width)) : Bool)
  then (clint_load access paddr width)
  else
    (do
      if ((← (within_sig paddr width)) : Bool)
      then (sig_load access paddr width)
      else
        (do
          if ((← (within_htif_readable paddr width)) : Bool)
          then (htif_load access paddr width)
          else (pure (Err (paddr, (← (accessFaultFromAccessType access)))))))

/-- Type quantifiers: width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mmio_write (paddr : physaddr) (width : Nat) (data : (BitVec (8 * width))) : SailM (Result Bool (physaddr × ExceptionType)) := do
  if ((← (within_clint paddr width)) : Bool)
  then (clint_store paddr width data)
  else
    (do
      if ((← (within_sig paddr width)) : Bool)
      then (sig_store paddr width data)
      else
        (do
          if ((← (within_htif_writable paddr width)) : Bool)
          then (htif_store paddr width data)
          else (pure (Err (paddr, (E_SAMO_Access_Fault ()))))))

