import SailRV32.Flow
import SailRV32.Prelude
import SailRV32.Errors
import SailRV32.AextTypes
import SailRV32.MemAddrtype
import SailRV32.MemMetadata
import SailRV32.PlatformConfig
import SailRV32.Types
import SailRV32.VmemTypes
import SailRV32.PhysMemInterface
import SailRV32.MemTypeUtils
import SailRV32.Callbacks
import SailRV32.PmpControl
import SailRV32.SysControl
import SailRV32.Platform
import SailRV32.SplitAccessUtils
import SailRV32.Pma

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

/-- Type quantifiers: k_ex1822051_ : Bool, k_ex1822050_ : Bool, k_ex1822049_ : Bool -/
def read_kind_of_flags (aq : Bool) (rl : Bool) (res : Bool) : SailM read_kind := do
  match (aq, rl, res) with
  | (false, false, false) => (pure Read_plain)
  | (true, false, false) =>
    (internal_error "sys/mem.sail" 38 "Unreserved load with acquire semantics should be unreachable")
  | (true, true, false) =>
    (internal_error "sys/mem.sail" 39
      "Unreserved load with acquire-release semantics should be unreachable")
  | (false, false, true) => (pure Read_RISCV_reserved)
  | (true, false, true) => (pure Read_RISCV_reserved_acquire)
  | (true, true, true) => (pure Read_RISCV_reserved_strong_acquire)
  | (false, true, false) =>
    (internal_error "sys/mem.sail" 44 "Unreserved Load with release semantics should be unreachable")
  | (false, true, true) =>
    (internal_error "sys/mem.sail" 45 "Load-reserved with release semantics should be unreachable")

/-- Type quantifiers: k_ex1822054_ : Bool, k_ex1822053_ : Bool, k_ex1822052_ : Bool -/
def write_kind_of_flags (aq : Bool) (rl : Bool) (con : Bool) : SailM write_kind := do
  match (aq, rl, con) with
  | (false, false, false) => (pure Write_plain)
  | (false, true, false) =>
    (internal_error "sys/mem.sail" 51
      "Unconditional store with release semantics should be unreachable")
  | (false, false, true) => (pure Write_RISCV_conditional)
  | (false, true, true) => (pure Write_RISCV_conditional_release)
  | (true, true, false) =>
    (internal_error "sys/mem.sail" 54
      "Unconditional store with acquire-release semantics should be unreachable")
  | (true, true, true) => (pure Write_RISCV_conditional_strong_release)
  | (true, false, false) =>
    (internal_error "sys/mem.sail" 57
      "Unconditional store with acquire semantics should be unreachable")
  | (true, false, true) =>
    (internal_error "sys/mem.sail" 58
      "Store-conditional with acquire semantics should be unreachable")

def undefined_Phys_Mem_Access_Info (_ : Unit) : SailM Phys_Mem_Access_Info := do
  (pure { splittable := ← (undefined_Splittability ())
          granule_size_exp := ← (undefined_range 0 12) })

/-- Type quantifiers: k_ex1822055_ : Bool, width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def pmaCheck (paddr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (res_or_con : Bool) : SailM (Result Phys_Mem_Access_Info ExceptionType) := SailME.run do
  let attributes ← (( do
    match (matching_pma_region (← readReg pma_regions) paddr width) with
    | none =>
      SailME.throw (← do
          (pure (Err (← (accessFaultFromAccessType access)))))
    | .some { attributes := attributes, size := _, include_in_device_tree := _, base := _ } =>
      (pure (override_PMA attributes pbmt)) ) : SailME (Result Phys_Mem_Access_Info ExceptionType)
    PMA )
  let canAccess ← (( do
    match access with
    | .InstructionFetch () => (pure attributes.executable)
    | .Load .Data =>
      (do
        «assert» (not res_or_con) "sys/mem.sail:99.53-99.54"
        (pure attributes.readable))
    | .Load .Vector =>
      (do
        «assert» (not res_or_con) "sys/mem.sail:100.53-100.54"
        (pure attributes.readable))
    | .Load .PageTableEntry =>
      (do
        «assert» (not res_or_con) "sys/mem.sail:101.53-101.54"
        (pure attributes.supports_pte_read))
    | .LoadExecute .Data =>
      (do
        «assert» (not res_or_con) "sys/mem.sail:106.53-106.54"
        (pure (attributes.executable && attributes.readable)))
    | .Store .Data =>
      (do
        «assert» (not res_or_con) "sys/mem.sail:107.53-107.54"
        (pure attributes.writable))
    | .Store .Vector =>
      (do
        «assert» (not res_or_con) "sys/mem.sail:108.53-108.54"
        (pure attributes.writable))
    | .Store .PageTableEntry =>
      (do
        «assert» (not res_or_con) "sys/mem.sail:109.53-109.54"
        (pure attributes.supports_pte_write))
    | .LoadReserved (_, _, .Data) =>
      (do
        «assert» res_or_con "sys/mem.sail:113.55-113.56"
        (pure (attributes.readable && (bne attributes.reservability RsrvNone))))
    | .StoreConditional (_, _, .Data) =>
      (do
        «assert» res_or_con "sys/mem.sail:114.55-114.56"
        (pure (attributes.writable && (bne attributes.reservability RsrvNone))))
    | .Atomic (op, _, _, .Data, .Data) =>
      (do
        «assert» res_or_con "sys/mem.sail:115.55-115.56"
        (pure (attributes.readable && (attributes.writable && (pma_allows_atomic_op
                attributes.atomic_support op width)))))
    | .Load .ShadowStack =>
      (do
        «assert» (not res_or_con) "sys/mem.sail:119.53-119.54"
        (pure (attributes.readable && attributes.read_idempotent)))
    | .Store .ShadowStack =>
      (do
        «assert» (not res_or_con) "sys/mem.sail:120.53-120.54"
        (pure (attributes.writable && attributes.write_idempotent)))
    | .Atomic (.AMOSWAP, _, _, .ShadowStack, .ShadowStack) =>
      (do
        «assert» res_or_con "sys/mem.sail:121.73-121.74"
        (pure (attributes.readable && (attributes.writable && (attributes.read_idempotent && (attributes.write_idempotent && (pma_allows_atomic_op
                    attributes.atomic_support AMOSWAP width)))))))
    | .CacheAccess (.CB_zero ()) => (pure (attributes.writable && attributes.supports_cbo_zero))
    | .CacheAccess (.CB_manage _) => (pure (attributes.readable || attributes.writable))
    | .CacheAccess (.CB_prefetch p) =>
      (match p with
      | .PREFETCH_R => (pure attributes.readable)
      | .PREFETCH_W => (pure attributes.writable)
      | .PREFETCH_I => (pure attributes.executable))
    | .LoadExecute p =>
      (internal_error "sys/mem.sail" 158
        (HAppend.hAppend "Invalid payload ("
          (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadExecute.")))
    | .LoadReserved (_, _, p) =>
      (internal_error "sys/mem.sail" 159
        (HAppend.hAppend "Invalid payload ("
          (HAppend.hAppend (mem_payload_name_forwards p) ") for LoadReserved.")))
    | .StoreConditional (_, _, p) =>
      (internal_error "sys/mem.sail" 160
        (HAppend.hAppend "Invalid payload ("
          (HAppend.hAppend (mem_payload_name_forwards p) ") for StoreConditional.")))
    | .Atomic (op, _, _, .ShadowStack, .ShadowStack) =>
      (internal_error "sys/mem.sail" 162
        (HAppend.hAppend "Invalid op ("
          (HAppend.hAppend (amo_mnemonic_forwards op) ") for ShadowStack Atomic.")))
    | .Atomic (_, _, _, rp, wp) =>
      (internal_error "sys/mem.sail" 163
        (HAppend.hAppend "Invalid payloads ("
          (HAppend.hAppend (mem_payload_name_forwards rp)
            (HAppend.hAppend ", " (HAppend.hAppend (mem_payload_name_forwards wp) ") for Atomic.")))))
    ) : SailME (Result Phys_Mem_Access_Info ExceptionType) Bool )
  if ((not canAccess) : Bool)
  then
    (do
      let _ : Unit :=
        if ((get_config_print_pma ()) : Bool)
        then
          (print_endline
            (HAppend.hAppend "PMA access check failed for a "
              (HAppend.hAppend (Int.repr width)
                (HAppend.hAppend "-byte wide "
                  (HAppend.hAppend (accessType_to_str access)
                    (HAppend.hAppend " access to address "
                      (HAppend.hAppend (hex_bits_str (bits_of_physaddr paddr))
                        (HAppend.hAppend " with PMA {"
                          (HAppend.hAppend (pma_attributes_to_str attributes) "}")))))))))
        else ()
      (pure (Err (← (accessFaultFromAccessType access)))))
  else
    (do
      match (← (mag_pma_check attributes access paddr width)) with
      | .Ok (splittable, granule_size_exp) =>
        (pure (Ok
            { splittable := splittable
              granule_size_exp := granule_size_exp }))
      | .Err e =>
        (do
          let _ : Unit :=
            if ((get_config_print_pma ()) : Bool)
            then
              (print_endline
                (HAppend.hAppend "MAG PMA check failed for a "
                  (HAppend.hAppend (Int.repr width)
                    (HAppend.hAppend "-byte wide "
                      (HAppend.hAppend (accessType_to_str access)
                        (HAppend.hAppend " access to address "
                          (HAppend.hAppend (hex_bits_str (bits_of_physaddr paddr))
                            (HAppend.hAppend " with PMA {"
                              (HAppend.hAppend (pma_attributes_to_str attributes) "}")))))))))
            else ()
          match e with
          | .AccessFault => (pure (Err (← (accessFaultFromAccessType access))))
          | .AlignmentException => (pure (Err (← (alignmentFaultFromAccessType access))))))

/-- Type quantifiers: k_ex1822056_ : Bool, width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def phys_access_check (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (paddr : physaddr) (width : Nat) (res_or_con : Bool) : SailM (Result Phys_Mem_Access_Info ExceptionType) := do
  match (← (pmpCheck paddr width access priv)) with
  | .some e => (pure (Err e))
  | none => (pmaCheck paddr width access pbmt res_or_con)

/-- Type quantifiers: k_ex1822057_ : Bool, width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def check_pma_with_pmp_priority (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (paddr : physaddr) (width : Nat) (res_or_con : Bool) : SailM (Result Phys_Mem_Access_Info ExceptionType) := do
  match (← (pmaCheck paddr width access pbmt res_or_con)) with
  | .Ok access_info => (pure (Ok access_info))
  | .Err pmaExc =>
    (do
      match (← (pmpCheck paddr width access priv)) with
      | .some pmpExc => (pure (Err pmpExc))
      | none => (pure (Err pmaExc)))

/-- Type quantifiers: k_ex1822061_ : Bool, k_ex1822060_ : Bool, k_ex1822059_ : Bool, k_ex1822058_ :
  Bool, width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def checked_mem_read (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta' : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType)) := SailME.run do
  let access_info ← (( do
    match (← (check_pma_with_pmp_priority access pbmt priv paddr width res)) with
    | .Ok access_info => (pure access_info)
    | .Err e =>
      SailME.throw ((Err (paddr, e)) : (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType)))
    ) : SailME (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType))
    Phys_Mem_Access_Info )
  let (N, split_width) ← do
    (split_misaligned paddr width access_info.granule_size_exp access_info.splittable)
  let paddr_bits := (bits_of_physaddr paddr)
  let data := (zeros (n := ((8 *i N) *i split_width)))
  let (first, last, step) := (misaligned_order N)
  let i : Nat := first
  let finished : Bool := false
  let rk ← do (read_kind_of_flags aq rl res)
  let (data, finished, i) ← (( do
    let loop_vars ← untilFuelM (fuel :=N) (fun (data, finished, i) => (pure finished)) (data, finished, i)
      fun (data, finished, i) => do
        «assert» true "loop dummy assert"
        let offset := i
        let paddr := (Physaddr (BitVec.addInt paddr_bits (offset *i split_width)))
        match (← (pmpCheck paddr split_width access priv)) with
        | .some e =>
          SailME.throw ((Err (paddr, e)) : (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType)))
        | none => (pure ())
        let split_data ← do
          if ((← (within_mmio_readable paddr split_width)) : Bool)
          then
            (do
              match (← (mmio_read access paddr split_width)) with
              | .Err e =>
                SailME.throw ((Err e) : (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType)))
              | .Ok mmio_data => (pure mmio_data))
          else
            (do
              let (ram_data, _meta) ← do (read_ram rk access paddr split_width meta')
              (pure ram_data))
        let data : (BitVec (8 * N * split_width)) :=
          (Sail.BitVec.updateSubrange data (((8 *i (offset +i 1)) *i split_width) -i 1)
            ((8 *i offset) *i split_width) split_data)
        let (finished, i) : (Bool × Nat) :=
          if ((offset == last) : Bool)
          then
            (let finished : Bool := true
            (finished, i))
          else
            (let i : Nat := (offset +i step)
            (finished, i))
        (pure (data, finished, i))
    (pure loop_vars) ) : SailME (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType))
    ((BitVec (8 * N * split_width)) × Bool × Nat) )
  (pure (Ok (data, default_meta)))

/-- Type quantifiers: k_ex1822065_ : Bool, k_ex1822064_ : Bool, k_ex1822063_ : Bool, k_ex1822062_ :
  Bool, width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_read_priv_meta (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta' : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType)) := do
  let result ← (( do
    match (aq, rl, res) with
    | (false, true, false) => sailThrow ((Error_not_implemented "load.rl"))
    | (false, true, true) => sailThrow ((Error_not_implemented "lr.rl"))
    | (_, _, _) => (checked_mem_read access pbmt priv paddr width aq rl res meta') ) : SailM
    (MemoryOpResult ((BitVec (8 * width)) × mem_meta)) )
  let _ : Unit :=
    match result with
    | .Ok (value, _) =>
      (mem_read_callback (accessType_to_str access) (bits_of_physaddr paddr) width value)
    | .Err (addr, e) =>
      (mem_exception_callback (bits_of_physaddr addr) (exceptionType_bits_forwards e))
  (pure result)

/-- Type quantifiers: k_ex1822069_ : Bool, k_ex1822068_ : Bool, k_ex1822067_ : Bool, k_ex1822066_ :
  Bool, width : Nat, width ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_read_meta (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (eff_priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta' : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) (physaddr × ExceptionType)) := do
  (mem_read_priv_meta access pbmt eff_priv paddr width aq rl res meta')

/-- Type quantifiers: k_ex1822072_ : Bool, k_ex1822071_ : Bool, k_ex1822070_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_read (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (eff_priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) (physaddr × ExceptionType)) := do
  (pure (MemoryOpResult_drop_meta
      (← (mem_read_priv_meta access pbmt eff_priv paddr width aq rl res false))))

/-- Type quantifiers: k_ex1822075_ : Bool, k_ex1822074_ : Bool, k_ex1822073_ : Bool, width : Nat, 0
  < width ∧ width ≤ max_mem_access -/
def mem_write_ea (paddr : physaddr) (width : Nat) (priv : Privilege) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Unit (physaddr × ExceptionType)) := SailME.run do
  let access_info ← (( do
    match (← (check_pma_with_pmp_priority access pbmt priv paddr width con)) with
    | .Ok access_info => (pure access_info)
    | .Err e => SailME.throw ((Err (paddr, e)) : (Result Unit (physaddr × ExceptionType))) ) :
    SailME (Result Unit (physaddr × ExceptionType)) Phys_Mem_Access_Info )
  let (N, split_width) ← do
    (split_misaligned paddr width access_info.granule_size_exp access_info.splittable)
  let paddr_bits := (bits_of_physaddr paddr)
  let (first, last, step) := (misaligned_order N)
  let i : Nat := first
  let finished : Bool := false
  let wk ← do (write_kind_of_flags aq rl con)
  let (finished, i) ← (( do
    let loop_vars ← untilFuelM (fuel :=N) (fun (finished, i) => (pure finished)) (finished, i)
      fun (finished, i) => do
        «assert» true "loop dummy assert"
        let offset := i
        let paddr := (Physaddr (BitVec.addInt paddr_bits (offset *i split_width)))
        match (← (pmpCheck paddr split_width access priv)) with
        | .some e => SailME.throw ((Err (paddr, e)) : (Result Unit (physaddr × ExceptionType)))
        | none =>
          (do
            if ((not (← (within_mmio_writable paddr split_width))) : Bool)
            then (write_ram_ea wk access paddr split_width)
            else (pure ()))
        let (finished, i) : (Bool × Nat) :=
          if ((offset == last) : Bool)
          then
            (let finished : Bool := true
            (finished, i))
          else
            (let i : Nat := (offset +i step)
            (finished, i))
        (pure (finished, i))
    (pure loop_vars) ) : SailME (Result Unit (physaddr × ExceptionType)) (Bool × Nat) )
  (pure (Ok ()))

/-- Type quantifiers: k_ex1822078_ : Bool, k_ex1822077_ : Bool, k_ex1822076_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def checked_mem_write (paddr : physaddr) (width : Nat) (data : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (meta' : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool (physaddr × ExceptionType)) := SailME.run do
  let access_info ← (( do
    match (← (check_pma_with_pmp_priority access pbmt priv paddr width con)) with
    | .Ok access_info => (pure access_info)
    | .Err e => SailME.throw ((Err (paddr, e)) : (Result Bool (physaddr × ExceptionType))) ) :
    SailME (Result Bool (physaddr × ExceptionType)) Phys_Mem_Access_Info )
  let (N, split_width) ← do
    (split_misaligned paddr width access_info.granule_size_exp access_info.splittable)
  let paddr_bits := (bits_of_physaddr paddr)
  let write_success : Bool := true
  let (first, last, step) := (misaligned_order N)
  let i : Nat := first
  let finished : Bool := false
  let wk ← do (write_kind_of_flags aq rl con)
  let (finished, i, write_success) ← (( do
    let loop_vars ← untilFuelM (fuel :=N) (fun (finished, i, write_success) => (pure finished)) (finished, i, write_success)
      fun (finished, i, write_success) => do
        «assert» true "loop dummy assert"
        let offset := i
        let paddr := (Physaddr (BitVec.addInt paddr_bits (offset *i split_width)))
        match (← (pmpCheck paddr split_width access priv)) with
        | .some e => SailME.throw ((Err (paddr, e)) : (Result Bool (physaddr × ExceptionType)))
        | none => (pure ())
        let write_value :=
          (Sail.BitVec.extractLsb data (((8 *i (offset +i 1)) *i split_width) -i 1)
            ((8 *i offset) *i split_width))
        let write_success ← (( do
          if ((← (within_mmio_writable paddr split_width)) : Bool)
          then
            (do
              match (← (mmio_write paddr split_width write_value)) with
              | .Ok v => (pure (write_success && v))
              | .Err e => SailME.throw ((Err e) : (Result Bool (physaddr × ExceptionType))))
          else
            (do
              let v ← do (write_ram wk access paddr split_width write_value meta')
              (pure (write_success && v))) ) : SailME (Result Bool (physaddr × ExceptionType)) Bool
          )
        let (finished, i) : (Bool × Nat) :=
          if ((offset == last) : Bool)
          then
            (let finished : Bool := true
            (finished, i))
          else
            (let i : Nat := (offset +i step)
            (finished, i))
        (pure (finished, i, write_success))
    (pure loop_vars) ) : SailME (Result Bool (physaddr × ExceptionType)) (Bool × Nat × Bool) )
  (pure (Ok write_success))

/-- Type quantifiers: k_ex1822081_ : Bool, k_ex1822080_ : Bool, k_ex1822079_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_write_value_priv_meta (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (priv : Privilege) (meta' : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool (physaddr × ExceptionType)) := do
  let result ← do (checked_mem_write paddr width value access pbmt priv meta' aq rl con)
  let _ : Unit :=
    match result with
    | .Ok _ => (mem_write_callback (accessType_to_str access) (bits_of_physaddr paddr) width value)
    | .Err (addr, e) =>
      (mem_exception_callback (bits_of_physaddr addr) (exceptionType_bits_forwards e))
  (pure result)

/-- Type quantifiers: k_ex1822084_ : Bool, k_ex1822083_ : Bool, k_ex1822082_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_write_value (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (priv : Privilege) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool (physaddr × ExceptionType)) := do
  (mem_write_value_priv_meta paddr width value access pbmt priv default_meta aq rl con)

/-- Type quantifiers: k_ex1822087_ : Bool, k_ex1822086_ : Bool, k_ex1822085_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def mem_write_value_meta (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (eff_priv : Privilege) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (meta' : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool (physaddr × ExceptionType)) := do
  (mem_write_value_priv_meta paddr width value access pbmt eff_priv meta' aq rl con)

