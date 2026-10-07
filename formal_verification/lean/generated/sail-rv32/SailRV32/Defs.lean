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

abbrev bits k_n := (BitVec k_n)

inductive regidx where
  | Regidx (_ : (BitVec (if ( false  : Bool) then 4 else 5)))
  deriving Inhabited, BEq, Repr
  open regidx

abbrev xlenbits := (BitVec 32)

inductive Signedness where | Signed | Unsigned
  deriving BEq, Inhabited, Repr
  open Signedness

inductive VectorHalf where | High | Low
  deriving BEq, Inhabited, Repr
  open VectorHalf

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

inductive Privilege where | User | VirtualUser | Supervisor | VirtualSupervisor | Machine
  deriving BEq, Inhabited, Repr
  open Privilege

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

abbrev half := (BitVec 16)

abbrev word := (BitVec 32)

inductive regno where
  | Regno (_ : Nat)
  deriving Inhabited, BEq, Repr
  open regno

abbrev word_width := Int

abbrev regtype := xlenbits

abbrev ext_control_addr_error := Unit

abbrev ext_data_addr_error := Unit

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

inductive Register : Type where
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
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
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

@[reducible]
instance : Arch where
  addr_size := 64
  addr_space := Unit
  CHERI := false
  cap_size_log := 0
  register := Register
  register_type := RegisterType
  mem_acc := Unit
  mem_acc_is_explicit := fun _ => false
  mem_acc_is_ifetch := fun _ => false
  mem_acc_is_ttw := fun _ => false
  mem_acc_is_relaxed := fun _ => false
  mem_acc_is_rel_acq_rcpc := fun _ => false
  mem_acc_is_rel_acq_rcsc := fun _ => false
  mem_acc_is_standalone := fun _ => false
  mem_acc_is_exclusive := fun _ => false
  mem_acc_is_atomic_rmw := fun _ => false
  trans_start := Unit
  trans_end := Unit
  abort := Unit
  barrier := Unit
  cache_op := Unit
  tlbi := Unit
  exn := Unit
  sys_reg_id := Unit

abbrev exception := Unit

abbrev SailM := PreSailM exception
abbrev SailME := PreSailME exception



instance : Inhabited (RegisterRef (BitVec 32)) where
  default := .Reg PC