import Sail
open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ArchSem

namespace SailRV32

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr
  open option

inductive AtomicSupport where | AMONone | AMOSwap | AMOLogical | AMOArithmetic | AMOCASW | AMOCASD | AMOCASQ
  deriving BEq, Inhabited, Repr
  open AtomicSupport

inductive Privileged_ISA_Version where | Privileged_ISA_1_11 | Privileged_ISA_1_12 | Privileged_ISA_1_13
  deriving BEq, Inhabited, Repr
  open Privileged_ISA_Version

inductive vector_support where | Disabled | Integer | Float_single | Float_double | Full
  deriving BEq, Inhabited, Repr
  open vector_support

abbrev bits k_n := (BitVec k_n)

inductive regidx where
  | Regidx (_ : (BitVec (if ( false  : Bool) then 4 else 5)))
  deriving Inhabited, BEq, Repr
  open regidx

abbrev xlenbits := (BitVec 32)

inductive virtaddr where
  | Virtaddr (_ : xlenbits)
  deriving Inhabited, BEq, Repr
  open virtaddr

abbrev nat1 := Int

inductive Signedness where | Signed | Unsigned
  deriving BEq, Inhabited, Repr
  open Signedness

inductive VectorHalf where | High | Low
  deriving BEq, Inhabited, Repr
  open VectorHalf

abbrev max_mem_access  : Int := 4096

abbrev mem_access_width := Nat

inductive exception where
  | Error_not_implemented (_ : String)
  | Error_internal_error (_ : String)
  | Error_reserved_behavior (_ : String)
  deriving Inhabited, BEq, Repr
  open exception

inductive amoop where | AMOSWAP | AMOAND | AMOOR | AMOXOR | AMOADD | AMOMIN | AMOMAX | AMOMINU | AMOMAXU | AMOCAS
  deriving BEq, Inhabited, Repr
  open amoop

inductive cbop_zicbom where | CBO_CLEAN | CBO_FLUSH | CBO_INVAL
  deriving BEq, Inhabited, Repr
  open cbop_zicbom

inductive cbop_zicbop where | PREFETCH_I | PREFETCH_R | PREFETCH_W
  deriving BEq, Inhabited, Repr
  open cbop_zicbop

abbrev pm_len := Int

inductive PointerMaskingMode where | PMM_Disabled | PMM_Reserved | PMM_PMLEN_7 | PMM_PMLEN_16
  deriving BEq, Inhabited, Repr
  open PointerMaskingMode

abbrev xlen  : Int := 32

abbrev physaddr_bits  : Int := 34

abbrev geilen  : Int := 31

abbrev physaddrbits_len  : Int := (if ( xlen = 32  : Bool) then 34 else 64)

abbrev gpabits := (BitVec (if ( 32 = 32  : Bool) then 34 else 64))

abbrev asidbits := (BitVec (if ( 32 = 32  : Bool) then 9 else 16))

abbrev vmidbits := (BitVec (if ( 32 = 32  : Bool) then 7 else 14))

abbrev physaddrbits := (BitVec (if ( 32 = 32  : Bool) then 34 else 64))

inductive physaddr where
  | Physaddr (_ : physaddrbits)
  deriving Inhabited, BEq, Repr
  open physaddr

abbrev mem_meta := Unit

inductive misaligned_exception where | AccessFault | AlignmentException
  deriving BEq, Inhabited, Repr
  open misaligned_exception

inductive mem_payload where | Data | Vector | PageTableEntry | ShadowStack
  deriving BEq, Inhabited, Repr
  open mem_payload

inductive cacheop where
  | CB_manage (_ : cbop_zicbom)
  | CB_zero (_ : Unit)
  | CB_prefetch (_ : cbop_zicbop)
  deriving Inhabited, BEq, Repr
  open cacheop

/-- Type quantifiers: k_a : Type -/
inductive MemoryAccessType (k_a : Type) where
  | Load (_ : k_a)
  | Store (_ : k_a)
  | LoadReserved (_ : (Bool × Bool × k_a))
  | LoadExecute (_ : k_a)
  | StoreConditional (_ : (Bool × Bool × k_a))
  | Atomic (_ : (amoop × Bool × Bool × k_a × k_a))
  | InstructionFetch (_ : Unit)
  | CacheAccess (_ : cacheop)
  deriving Inhabited, BEq, Repr
  open MemoryAccessType

abbrev csreg := (BitVec 12)

abbrev ext_exc_type := Unit

inductive breakpoint_cause where | Brk_Software | Brk_Hardware
  deriving BEq, Inhabited, Repr
  open breakpoint_cause

inductive ExceptionType where
  | E_Fetch_Addr_Align (_ : Unit)
  | E_Fetch_Access_Fault (_ : Unit)
  | E_Illegal_Instr (_ : Unit)
  | E_Breakpoint (_ : breakpoint_cause)
  | E_Load_Addr_Align (_ : Unit)
  | E_Load_Access_Fault (_ : Unit)
  | E_SAMO_Addr_Align (_ : Unit)
  | E_SAMO_Access_Fault (_ : Unit)
  | E_U_EnvCall (_ : Unit)
  | E_S_EnvCall (_ : Unit)
  | E_VS_EnvCall (_ : Unit)
  | E_M_EnvCall (_ : Unit)
  | E_Fetch_Page_Fault (_ : Unit)
  | E_Load_Page_Fault (_ : Unit)
  | E_Reserved_14 (_ : Unit)
  | E_SAMO_Page_Fault (_ : Unit)
  | E_Double_Trap (_ : Unit)
  | E_Reserved_17 (_ : Unit)
  | E_Software_Check (_ : Unit)
  | E_Hardware_Error (_ : Unit)
  | E_Fetch_GPage_Fault (_ : Unit)
  | E_Load_GPage_Fault (_ : Unit)
  | E_Virtual_Instr (_ : Unit)
  | E_SAMO_GPage_Fault (_ : Unit)
  | E_Extension (_ : ext_exc_type)
  deriving Inhabited, BEq, Repr
  open ExceptionType

inductive MemoryRegionType where | MainMemory | IOMemory
  deriving BEq, Inhabited, Repr
  open MemoryRegionType

structure PMAMisalignedExceptions where
  load_store : (Option misaligned_exception)
  vector : (Option misaligned_exception)
  amo : misaligned_exception
  lrsc : misaligned_exception
  deriving BEq, Inhabited, Repr

inductive Reservability where | RsrvNone | RsrvNonEventual | RsrvEventual
  deriving BEq, Inhabited, Repr
  open Reservability

abbrev mag_size_exp := Nat

structure PMA where
  mem_type : MemoryRegionType
  cacheable : Bool
  coherent : Bool
  executable : Bool
  readable : Bool
  writable : Bool
  read_idempotent : Bool
  write_idempotent : Bool
  misaligned_exceptions : PMAMisalignedExceptions
  atomic_support : AtomicSupport
  reservability : Reservability
  supports_cbo_zero : Bool
  supports_pte_read : Bool
  supports_pte_write : Bool
  misaligned_atomicity_granule_size_exp : mag_size_exp
  vector_misaligned_atomicity_granule_size_exp : mag_size_exp
  deriving BEq, Inhabited, Repr

structure PMA_Region where
  base : (BitVec 64)
  size : (BitVec 64)
  attributes : PMA
  include_in_device_tree : Bool
  deriving BEq, Inhabited, Repr

inductive Privilege where | User | VirtualUser | Supervisor | VirtualSupervisor | Machine
  deriving BEq, Inhabited, Repr
  open Privilege

inductive extension where | Ext_M | Ext_A | Ext_F | Ext_D | Ext_B | Ext_V | Ext_S | Ext_U | Ext_H | Ext_Sha | Ext_Shcounterenw | Ext_Shgatpa | Ext_Shtvala | Ext_Shvsatpa | Ext_Shvstvala | Ext_Shvstvecd | Ext_Zibi | Ext_Zic64b | Ext_Zicbom | Ext_Zicbop | Ext_Zicboz | Ext_Zicfilp | Ext_Zicfiss | Ext_Zicntr | Ext_Zicond | Ext_Zicsr | Ext_Zifencei | Ext_Zihintntl | Ext_Zihintpause | Ext_Zihpm | Ext_Zilx | Ext_Zimop | Ext_Zmmul | Ext_Zaamo | Ext_Zabha | Ext_Zacas | Ext_Zalrsc | Ext_Zama16b | Ext_Zawrs | Ext_Za64rs | Ext_Za128rs | Ext_Zfa | Ext_Zfbfmin | Ext_Zfh | Ext_Zfhmin | Ext_Zfinx | Ext_Zdinx | Ext_Zca | Ext_Zcb | Ext_Zcd | Ext_Zcf | Ext_Zcmop | Ext_C | Ext_Zba | Ext_Zbb | Ext_Zbc | Ext_Zbkb | Ext_Zbkc | Ext_Zbkx | Ext_Zbs | Ext_Ziccamoa | Ext_Ziccamoc | Ext_Ziccif | Ext_Zicclsm | Ext_Ziccrse | Ext_Zknd | Ext_Zkne | Ext_Zknh | Ext_Zkr | Ext_Zksed | Ext_Zksh | Ext_Zkt | Ext_Zhinx | Ext_Zhinxmin | Ext_Zvl32b | Ext_Zvl64b | Ext_Zvl128b | Ext_Zvl256b | Ext_Zvl512b | Ext_Zvl1024b | Ext_Zve32f | Ext_Zve32x | Ext_Zve64d | Ext_Zve64f | Ext_Zve64x | Ext_Zvabd | Ext_Zvfbfmin | Ext_Zvfbfwma | Ext_Zvfh | Ext_Zvfhmin | Ext_Zvbb | Ext_Zvbc | Ext_Zvkb | Ext_Zvkg | Ext_Zvkned | Ext_Zvknha | Ext_Zvknhb | Ext_Zvksed | Ext_Zvksh | Ext_Zvkt | Ext_Zvkn | Ext_Zvknc | Ext_Zvkng | Ext_Zvks | Ext_Zvksc | Ext_Zvksg | Ext_Ssccptr | Ext_Sscofpmf | Ext_Sscounterenw | Ext_Ssdbltrp | Ext_Ssnpm | Ext_Ssstateen | Ext_Ssstrict | Ext_Sstc | Ext_Sstvala | Ext_Sstvecd | Ext_Ssu64xl | Ext_Svbare | Ext_Sv32 | Ext_Sv39 | Ext_Sv48 | Ext_Sv57 | Ext_Svade | Ext_Svadu | Ext_Svinval | Ext_Svnapot | Ext_Svpbmt | Ext_Svrsw60t59b | Ext_Svukte | Ext_Svvptc | Ext_Smcntrpmf | Ext_Smdbltrp | Ext_Smmpm | Ext_Smnpm | Ext_Smstateen | Ext_Ssqosid | Ext_Sspm | Ext_Supm
  deriving BEq, Inhabited, Repr
  open extension

abbrev MEnvcfg := (BitVec 64)

inductive Architecture where | RV32 | RV64 | RV128
  deriving BEq, Inhabited, Repr
  open Architecture

abbrev Misa := (BitVec 32)

abbrev Mstatus := (BitVec 64)

abbrev Seccfg := (BitVec 64)

abbrev HEnvcfg := (BitVec 64)

abbrev SEnvcfg := (BitVec 64)

abbrev Hstateen0 := (BitVec 64)

abbrev Hstateen1 := (BitVec 64)

abbrev Hstateen2 := (BitVec 64)

abbrev Hstateen3 := (BitVec 64)

abbrev Mstateen0 := (BitVec 64)

abbrev Mstateen1 := (BitVec 64)

abbrev Mstateen2 := (BitVec 64)

abbrev Mstateen3 := (BitVec 64)

abbrev Sstateen0 := (BitVec 32)

abbrev Sstateen1 := (BitVec 32)

abbrev Sstateen2 := (BitVec 32)

abbrev Sstateen3 := (BitVec 32)

inductive stateen_bit where | STATEEN_FCSR | STATEEN_SRMCFG | STATEEN_P1P13 | STATEEN_ENVCFG | STATEEN_SE
  deriving BEq, Inhabited, Repr
  open stateen_bit

abbrev ext_ptw_error := Unit

inductive PTW_Error where
  | PTW_Invalid_Addr (_ : Unit)
  | PTW_No_Access (_ : Unit)
  | PTW_Invalid_PTE (_ : Unit)
  | PTW_No_Permission (_ : Unit)
  | PTW_Misaligned (_ : Unit)
  | PTW_PTE_Needs_Update (_ : Unit)
  | PTW_Implicit_Error (_ : (ExceptionType × gpabits × (MemoryAccessType mem_payload)))
  | PTW_Ext_Error (_ : ext_ptw_error)
  deriving Inhabited, BEq, Repr
  open PTW_Error

inductive TranslationStage where | S_Stage | VS_Stage | G_Stage
  deriving BEq, Inhabited, Repr
  open TranslationStage

abbrev ext_exception := Unit

structure ExceptionContext where
  trap : ExceptionType
  excinfo_is_gva : Bool
  excinfo : xlenbits
  excinfo2 : (Option xlenbits)
  excinst : (Option xlenbits)
  excinst_offset : (BitVec 5)
  ext : (Option ext_exception)
  deriving BEq, Inhabited, Repr

inductive WaitReason where | WAIT_WFI | WAIT_WRS_STO | WAIT_WRS_NTO
  deriving BEq, Inhabited, Repr
  open WaitReason

structure GlobalMisalignedExceptions where
  load_store : (Option misaligned_exception)
  vector : (Option misaligned_exception)
  amo : (Option misaligned_exception)
  lrsc : (Option misaligned_exception)
  deriving BEq, Inhabited, Repr

abbrev ext_ptw := Unit

abbrev ext_ptw_fail := Unit

abbrev half := (BitVec 16)

abbrev word := (BitVec 32)

inductive regno where
  | Regno (_ : Nat)
  deriving Inhabited, BEq, Repr
  open regno

abbrev is_mem_width (k_w : Int) : Bool := List.elem k_w [1, 2, 4, 8]

abbrev hgatp_mode := (BitVec 4)

inductive HGATPMode where | HBare | Sv32x4 | Sv39x4 | Sv48x4 | Sv57x4
  deriving BEq, Inhabited, Repr
  open HGATPMode

abbrev satp_mode := (BitVec 4)

inductive SATPMode where | Bare | Sv32 | Sv39 | Sv48 | Sv57
  deriving BEq, Inhabited, Repr
  open SATPMode

abbrev word_width := Int

abbrev is_sv_mode (k_v : Int) : Bool := List.elem k_v [32, 39, 48, 57]

abbrev is_svx4_mode (k_v : Int) : Bool := List.elem k_v [34, 41, 50, 59]

abbrev is_sv_or_svx4_mode (k_v : Int) : Bool := (is_sv_mode k_v) ∨ (is_svx4_mode k_v)

abbrev is_sv32_mode (k_v : Int) : Bool := k_v = 32 ∨ k_v = 34

abbrev root_level (k_v : Nat) : Int :=
  (if ( k_v = 32 ∨ k_v = 34  : Bool) then 1 else (if ( k_v = 39 ∨ k_v = 41  : Bool) then 2 else (if ( k_v
  = 48 ∨ k_v = 50  : Bool) then 3 else 4)))

abbrev level_range (k_v : Nat) := Nat

abbrev pte_bits k_v := (BitVec (if ( (is_sv32_mode k_v)  : Bool) then 32 else 64))

abbrev ppn_bits k_v := (BitVec (if ( (is_sv32_mode k_v)  : Bool) then 22 else 44))

abbrev vpn_bits k_v := (BitVec (k_v - 12))

inductive page_based_mem_type where | PBMT_PMA | PBMT_NC | PBMT_IO
  deriving BEq, Inhabited, Repr
  open page_based_mem_type

inductive write_kind where | Write_plain | Write_RISCV_release | Write_RISCV_strong_release | Write_RISCV_conditional | Write_RISCV_conditional_release | Write_RISCV_conditional_strong_release
  deriving BEq, Inhabited, Repr
  open write_kind

inductive read_kind where | Read_plain | Read_ifetch | Read_RISCV_acquire | Read_RISCV_strong_acquire | Read_RISCV_reserved | Read_RISCV_reserved_acquire | Read_RISCV_reserved_strong_acquire
  deriving BEq, Inhabited, Repr
  open read_kind

inductive access_kind where
  | AK_Write (_ : (write_kind × (MemoryAccessType mem_payload)))
  | AK_Read (_ : (read_kind × (MemoryAccessType mem_payload)))
  deriving Inhabited, BEq, Repr
  open access_kind

abbrev regtype := xlenbits

abbrev Hstatus := (BitVec 64)

abbrev Minterrupts := (BitVec 32)

inductive XipReadType where | IncludePlatformInterrupts | ExcludePlatformInterrupts
  deriving BEq, Inhabited, Repr
  open XipReadType

/-- Type quantifiers: k_a : Type -/
inductive Ext_DataAddr_Check (k_a : Type) where
  | Ext_DataAddr_OK (_ : virtaddr)
  | Ext_DataAddr_Error (_ : k_a)
  deriving Inhabited, BEq, Repr
  open Ext_DataAddr_Check

abbrev ext_control_addr_error := Unit

abbrev ext_data_addr_error := Unit

inductive PmpAddrMatchType where | OFF | TOR | NA4 | NAPOT
  deriving BEq, Inhabited, Repr
  open PmpAddrMatchType

abbrev Pmpcfg_ent := (BitVec 8)

inductive pmpAddrMatch where | PMP_NoMatch | PMP_PartialMatch | PMP_Match
  deriving BEq, Inhabited, Repr
  open pmpAddrMatch

inductive uop where | LUI | AUIPC
  deriving BEq, Inhabited, Repr
  open uop

inductive bop where | BEQ | BNE | BLT | BGE | BLTU | BGEU
  deriving BEq, Inhabited, Repr
  open bop

inductive iop where | ADDI | SLTI | SLTIU | XORI | ORI | ANDI
  deriving BEq, Inhabited, Repr
  open iop

inductive sop where | SLLI | SRLI | SRAI
  deriving BEq, Inhabited, Repr
  open sop

inductive rop where | ADD | SUB | SLL | SLT | SLTU | XOR | SRL | SRA | OR | AND
  deriving BEq, Inhabited, Repr
  open rop

inductive ropw where | ADDW | SUBW | SLLW | SRLW | SRAW
  deriving BEq, Inhabited, Repr
  open ropw

inductive sopw where | SLLIW | SRLIW | SRAIW
  deriving BEq, Inhabited, Repr
  open sopw

structure mul_op where
  result_part : VectorHalf
  signed_rs1 : Signedness
  signed_rs2 : Signedness
  deriving BEq, Inhabited, Repr

inductive brop_zbb where | ANDN | ORN | XNOR | MAX | MAXU | MIN | MINU | ROL | ROR
  deriving BEq, Inhabited, Repr
  open brop_zbb

inductive bropw_zbb where | ROLW | RORW
  deriving BEq, Inhabited, Repr
  open bropw_zbb

inductive extop_zbb where | SEXTB | SEXTH | ZEXTH
  deriving BEq, Inhabited, Repr
  open extop_zbb

inductive csrop where | CSRRW | CSRRS | CSRRC
  deriving BEq, Inhabited, Repr
  open csrop

abbrev MemoryOpResult k_a := (Result k_a (physaddr × ExceptionType))

inductive Splittability where | CanSplit | CannotSplit
  deriving BEq, Inhabited, Repr
  open Splittability

structure Phys_Mem_Access_Info where
  splittable : Splittability
  granule_size_exp : mag_size_exp
  deriving BEq, Inhabited, Repr

abbrev pte_ext_bits := (BitVec 10)

abbrev PTE_Ext := (BitVec 10)

abbrev PTE_Flags := (BitVec 8)

inductive pte_check_failure where
  | PTE_No_Permission (_ : Unit)
  | PTE_No_Access (_ : Unit)
  | PTE_Ext_Failure (_ : ext_ptw_fail)
  deriving Inhabited, BEq, Repr
  open pte_check_failure

inductive PTE_Check where
  | PTE_Check_Success (_ : ext_ptw)
  | PTE_Check_Failure (_ : (ext_ptw × pte_check_failure))
  deriving Inhabited, BEq, Repr
  open PTE_Check

abbrev tlb_vpn_bits  : Int := (59 - 12)

structure TLB_Entry where
  asid : asidbits
  vmid : vmidbits
  stage : TranslationStage
  global : Bool
  vpn : (BitVec (59 - 12))
  levelMask : (BitVec (59 - 12))
  ppn : (BitVec 44)
  pte : (BitVec 64)
  pteAddr : physaddr
  deriving BEq, Inhabited, Repr

abbrev num_tlb_entries_exp  : Int := 6

abbrev num_tlb_entries  : Int := (2 ^ 6)

abbrev tlb_index_range := Nat

/-- Type quantifiers: k_v : Int, (is_sv_or_svx4_mode k_v) -/
structure PTW_Output (k_v : Nat) where
  ppn : (ppn_bits k_v)
  pte : (pte_bits k_v)
  pteAddr : physaddr
  level : (level_range k_v)
  pbmt : page_based_mem_type
  global : Bool
  deriving BEq, Inhabited, Repr

inductive instruction where
  | ILLEGAL (_ : word)
  | C_ILLEGAL (_ : half)
  | UTYPE (_ : ((BitVec 20) × regidx × uop))
  | JAL (_ : ((BitVec 21) × regidx))
  | JALR (_ : ((BitVec 12) × regidx × regidx))
  | BTYPE (_ : ((BitVec 13) × regidx × regidx × bop))
  | ITYPE (_ : ((BitVec 12) × regidx × regidx × iop))
  | SHIFTIOP (_ : ((BitVec 6) × regidx × regidx × sop))
  | RTYPE (_ : (regidx × regidx × regidx × rop))
  | LOAD (_ : ((BitVec 12) × regidx × regidx × Bool × word_width))
  | STORE (_ : ((BitVec 12) × regidx × regidx × word_width))
  | ADDIW (_ : ((BitVec 12) × regidx × regidx))
  | RTYPEW (_ : (regidx × regidx × regidx × ropw))
  | SHIFTIWOP (_ : ((BitVec 5) × regidx × regidx × sopw))
  | FENCE_TSO (_ : Unit)
  | FENCE (_ : ((BitVec 4) × (BitVec 4) × (BitVec 4) × regidx × regidx))
  | ECALL (_ : Unit)
  | MRET (_ : Unit)
  | SRET (_ : Unit)
  | EBREAK (_ : Unit)
  | WFI (_ : Unit)
  | SFENCE_VMA (_ : (regidx × regidx))
  | MUL (_ : (regidx × regidx × regidx × mul_op))
  | DIV (_ : (regidx × regidx × regidx × Bool))
  | REM (_ : (regidx × regidx × regidx × Bool))
  | MULW (_ : (regidx × regidx × regidx))
  | DIVW (_ : (regidx × regidx × regidx × Bool))
  | REMW (_ : (regidx × regidx × regidx × Bool))
  | RORIW (_ : ((BitVec 5) × regidx × regidx))
  | RORI (_ : ((BitVec 6) × regidx × regidx))
  | ZBB_RTYPEW (_ : (regidx × regidx × regidx × bropw_zbb))
  | ZBB_RTYPE (_ : (regidx × regidx × regidx × brop_zbb))
  | ZBB_EXTOP (_ : (regidx × regidx × extop_zbb))
  | REV8 (_ : (regidx × regidx))
  | ORCB (_ : (regidx × regidx))
  | CPOP (_ : (regidx × regidx))
  | CPOPW (_ : (regidx × regidx))
  | CLZ (_ : (regidx × regidx))
  | CLZW (_ : (regidx × regidx))
  | CTZ (_ : (regidx × regidx))
  | CTZW (_ : (regidx × regidx))
  | CSRReg (_ : (csreg × regidx × regidx × csrop))
  | CSRImm (_ : (csreg × (BitVec 5) × regidx × csrop))
  deriving Inhabited, Repr
  open instruction

inductive ExecutionResult where
  | Retire_Success (_ : Unit)
  | ExecuteAs (_ : instruction)
  | Enter_Wait (_ : WaitReason)
  | Illegal_Instruction (_ : Unit)
  | Virtual_Instruction (_ : Unit)
  | Trap (_ : (Privilege × ExceptionContext × xlenbits))
  | Ext_CSR_Check_Failure (_ : Unit)
  | Ext_ControlAddr_Check_Failure (_ : ext_control_addr_error)
  | Ext_DataAddr_Check_Failure (_ : ext_data_addr_error)
  | Ext_XRET_Priv_Failure (_ : Unit)
  deriving Inhabited, Repr
  open ExecutionResult

structure AccessInfo where
  eff_privilege : Privilege
  pmlen : pm_len
  as_guest : Bool
  deriving BEq, Inhabited, Repr

inductive Register : Type where
  | vsatp
  | satp
  | hgatp
  | tlb
  | pma_regions
  | htif_payload_writes
  | htif_cmd_write
  | htif_exit_code
  | htif_done
  | htif_tohost
  | htif_tohost_base
  | elp
  | pmpaddr_n
  | pmpcfg_n
  | sig_msip
  | msip
  | mtime
  | mtimecmp
  | sig_ssip
  | sig_seip
  | sig_meip
  | mip
  | sig_hgeip
  | hgeie
  | mhartid
  | hstatus
  | x31
  | x30
  | x29
  | x28
  | x27
  | x26
  | x25
  | x24
  | x23
  | x22
  | x21
  | x20
  | x19
  | x18
  | x17
  | x16
  | x15
  | x14
  | x13
  | x12
  | x11
  | x10
  | x9
  | x8
  | x7
  | x6
  | x5
  | x4
  | x3
  | x2
  | x1
  | nextPC
  | PC
  | henvcfg
  | menvcfg
  | mseccfg
  | senvcfg
  | sstateen3
  | sstateen2
  | sstateen1
  | sstateen0
  | mstateen3
  | mstateen2
  | mstateen1
  | mstateen0
  | hstateen3
  | hstateen2
  | hstateen1
  | hstateen0
  | vsstatus
  | mstatus
  | misa
  | cur_privilege
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .vsatp => (BitVec 32)
  | .satp => (BitVec 32)
  | .hgatp => (BitVec 32)
  | .tlb => (Vector (Option TLB_Entry) (2 ^ 6))
  | .pma_regions => (List PMA_Region)
  | .htif_payload_writes => (BitVec 4)
  | .htif_cmd_write => (BitVec 1)
  | .htif_exit_code => (BitVec 64)
  | .htif_done => Bool
  | .htif_tohost => (BitVec 64)
  | .htif_tohost_base => (Option (BitVec (if ( 32 = 32  : Bool) then 34 else 64)))
  | .elp => (BitVec 1)
  | .pmpaddr_n => (Vector (BitVec 32) 64)
  | .pmpcfg_n => (Vector (BitVec 8) 64)
  | .sig_msip => (BitVec 1)
  | .msip => (BitVec 32)
  | .mtime => (BitVec 64)
  | .mtimecmp => (BitVec 64)
  | .sig_ssip => (BitVec 1)
  | .sig_seip => (BitVec 1)
  | .sig_meip => (BitVec 1)
  | .mip => (BitVec 32)
  | .sig_hgeip => (BitVec 32)
  | .hgeie => (BitVec 32)
  | .mhartid => (BitVec 32)
  | .hstatus => (BitVec 64)
  | .x31 => (BitVec 32)
  | .x30 => (BitVec 32)
  | .x29 => (BitVec 32)
  | .x28 => (BitVec 32)
  | .x27 => (BitVec 32)
  | .x26 => (BitVec 32)
  | .x25 => (BitVec 32)
  | .x24 => (BitVec 32)
  | .x23 => (BitVec 32)
  | .x22 => (BitVec 32)
  | .x21 => (BitVec 32)
  | .x20 => (BitVec 32)
  | .x19 => (BitVec 32)
  | .x18 => (BitVec 32)
  | .x17 => (BitVec 32)
  | .x16 => (BitVec 32)
  | .x15 => (BitVec 32)
  | .x14 => (BitVec 32)
  | .x13 => (BitVec 32)
  | .x12 => (BitVec 32)
  | .x11 => (BitVec 32)
  | .x10 => (BitVec 32)
  | .x9 => (BitVec 32)
  | .x8 => (BitVec 32)
  | .x7 => (BitVec 32)
  | .x6 => (BitVec 32)
  | .x5 => (BitVec 32)
  | .x4 => (BitVec 32)
  | .x3 => (BitVec 32)
  | .x2 => (BitVec 32)
  | .x1 => (BitVec 32)
  | .nextPC => (BitVec 32)
  | .PC => (BitVec 32)
  | .henvcfg => (BitVec 64)
  | .menvcfg => (BitVec 64)
  | .mseccfg => (BitVec 64)
  | .senvcfg => (BitVec 64)
  | .sstateen3 => (BitVec 32)
  | .sstateen2 => (BitVec 32)
  | .sstateen1 => (BitVec 32)
  | .sstateen0 => (BitVec 32)
  | .mstateen3 => (BitVec 64)
  | .mstateen2 => (BitVec 64)
  | .mstateen1 => (BitVec 64)
  | .mstateen0 => (BitVec 64)
  | .hstateen3 => (BitVec 64)
  | .hstateen2 => (BitVec 64)
  | .hstateen1 => (BitVec 64)
  | .hstateen0 => (BitVec 64)
  | .vsstatus => (BitVec 64)
  | .mstatus => (BitVec 64)
  | .misa => (BitVec 32)
  | .cur_privilege => Privilege

/-- Type quantifiers: k_p : Bool -/
def not (b : Bool) : Bool :=
  (! b)

def is_implicit_access (access : (MemoryAccessType mem_payload)) : Bool :=
  match access with
  | .InstructionFetch () => true
  | .Load .PageTableEntry => true
  | .Store .PageTableEntry => true
  | _ => false

def ak_memory_access (acc : access_kind) : (MemoryAccessType mem_payload) :=
  match acc with
  | .AK_Write (_, access) => access
  | .AK_Read (_, access) => access

def ak_is_explicit (acc : access_kind) : Bool :=
  (not (is_implicit_access (ak_memory_access acc)))

def ak_is_ifetch (acc : access_kind) : Bool :=
  ((ak_memory_access acc) == (InstructionFetch ()))

def ak_is_ttw (acc : access_kind) : Bool :=
  match (ak_memory_access acc) with
  | .Load .PageTableEntry => true
  | .Store .PageTableEntry => true
  | _ => false

def ak_is_relaxed (acc : access_kind) : Bool :=
  ((ak_is_explicit acc) && (match acc with
    | .AK_Write (.Write_plain, _) => true
    | .AK_Write (.Write_RISCV_conditional, _) => true
    | .AK_Read (.Read_plain, _) => true
    | .AK_Read (.Read_RISCV_reserved, _) => true
    | _ => false : Bool))

def ak_is_rel_acq_rcsc (acc : access_kind) : Bool :=
  ((ak_is_explicit acc) && (match acc with
    | .AK_Write (.Write_RISCV_strong_release, _) => true
    | .AK_Write (.Write_RISCV_conditional_strong_release, _) => true
    | .AK_Read (.Read_RISCV_strong_acquire, _) => true
    | .AK_Read (.Read_RISCV_reserved_strong_acquire, _) => true
    | _ => false : Bool))

def ak_is_rel_acq_rcpc (acc : access_kind) : Bool :=
  ((ak_is_explicit acc) && (match acc with
    | .AK_Write (.Write_RISCV_release, _) => true
    | .AK_Write (.Write_RISCV_conditional_release, _) => true
    | .AK_Read (.Read_RISCV_acquire, _) => true
    | .AK_Read (.Read_RISCV_reserved_acquire, _) => true
    | _ => false : Bool))

def ak_is_standalone (acc : access_kind) : Bool :=
  ((ak_is_explicit acc) && (match (ak_memory_access acc) with
    | .LoadReserved _ => false
    | .StoreConditional _ => false
    | .Atomic _ => false
    | _ => true : Bool))

def ak_is_exclusive (acc : access_kind) : Bool :=
  match (ak_memory_access acc) with
  | .LoadReserved _ => true
  | .StoreConditional _ => true
  | _ => false

def ak_is_atomic_rmw (acc : access_kind) : Bool :=
  match (ak_memory_access acc) with
  | .Atomic _ => true
  | _ => false

@[reducible]
instance : Arch where
  addr_size := physaddrbits_len
  addr_space := Unit
  CHERI := false
  cap_size_log := 0
  register := Register
  register_type := RegisterType
  mem_acc := access_kind
  mem_acc_is_explicit := ak_is_explicit
  mem_acc_is_ifetch := ak_is_ifetch
  mem_acc_is_ttw := ak_is_ttw
  mem_acc_is_relaxed := ak_is_relaxed
  mem_acc_is_rel_acq_rcpc := ak_is_rel_acq_rcpc
  mem_acc_is_rel_acq_rcsc := ak_is_rel_acq_rcsc
  mem_acc_is_standalone := ak_is_standalone
  mem_acc_is_exclusive := ak_is_exclusive
  mem_acc_is_atomic_rmw := ak_is_atomic_rmw
  trans_start := Unit
  trans_end := Unit
  abort := Unit
  barrier := Unit
  cache_op := Unit
  tlbi := Unit
  exn := Unit
  sys_reg_id := Unit

abbrev SailM := PreSailM exception
abbrev SailME := PreSailME exception



instance : Inhabited (RegisterRef Privilege) where
  default := .Reg cur_privilege
instance : Inhabited (RegisterRef (BitVec 1)) where
  default := .Reg sig_meip
instance : Inhabited (RegisterRef (BitVec 32)) where
  default := .Reg misa
instance : Inhabited (RegisterRef (BitVec 4)) where
  default := .Reg htif_payload_writes
instance : Inhabited (RegisterRef (BitVec 64)) where
  default := .Reg mstatus
instance : Inhabited (RegisterRef Bool) where
  default := .Reg htif_done
instance : Inhabited (RegisterRef (List PMA_Region)) where
  default := .Reg pma_regions
instance : Inhabited (RegisterRef (Option (BitVec (if ( 32 = 32  : Bool) then 34 else 64)))) where
  default := .Reg htif_tohost_base
instance : Inhabited (RegisterRef (Vector (BitVec 32) 64)) where
  default := .Reg pmpaddr_n
instance : Inhabited (RegisterRef (Vector (BitVec 8) 64)) where
  default := .Reg pmpcfg_n
instance : Inhabited (RegisterRef (Vector (Option TLB_Entry) (2 ^ 6))) where
  default := .Reg tlb