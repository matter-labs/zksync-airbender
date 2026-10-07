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

inductive vector_support where | Disabled | Integer | Float_single | Float_double | Full
  deriving BEq, Inhabited, Repr
  open vector_support

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

inductive Privilege where | User | VirtualUser | Supervisor | VirtualSupervisor | Machine
  deriving BEq, Inhabited, Repr
  open Privilege

inductive extension where | Ext_M | Ext_A | Ext_F | Ext_D | Ext_B | Ext_V | Ext_S | Ext_U | Ext_H | Ext_Sha | Ext_Shcounterenw | Ext_Shgatpa | Ext_Shtvala | Ext_Shvsatpa | Ext_Shvstvala | Ext_Shvstvecd | Ext_Zibi | Ext_Zic64b | Ext_Zicbom | Ext_Zicbop | Ext_Zicboz | Ext_Zicfilp | Ext_Zicfiss | Ext_Zicntr | Ext_Zicond | Ext_Zicsr | Ext_Zifencei | Ext_Zihintntl | Ext_Zihintpause | Ext_Zihpm | Ext_Zilx | Ext_Zimop | Ext_Zmmul | Ext_Zaamo | Ext_Zabha | Ext_Zacas | Ext_Zalrsc | Ext_Zama16b | Ext_Zawrs | Ext_Za64rs | Ext_Za128rs | Ext_Zfa | Ext_Zfbfmin | Ext_Zfh | Ext_Zfhmin | Ext_Zfinx | Ext_Zdinx | Ext_Zca | Ext_Zcb | Ext_Zcd | Ext_Zcf | Ext_Zcmop | Ext_C | Ext_Zba | Ext_Zbb | Ext_Zbc | Ext_Zbkb | Ext_Zbkc | Ext_Zbkx | Ext_Zbs | Ext_Ziccamoa | Ext_Ziccamoc | Ext_Ziccif | Ext_Zicclsm | Ext_Ziccrse | Ext_Zknd | Ext_Zkne | Ext_Zknh | Ext_Zkr | Ext_Zksed | Ext_Zksh | Ext_Zkt | Ext_Zhinx | Ext_Zhinxmin | Ext_Zvl32b | Ext_Zvl64b | Ext_Zvl128b | Ext_Zvl256b | Ext_Zvl512b | Ext_Zvl1024b | Ext_Zve32f | Ext_Zve32x | Ext_Zve64d | Ext_Zve64f | Ext_Zve64x | Ext_Zvabd | Ext_Zvfbfmin | Ext_Zvfbfwma | Ext_Zvfh | Ext_Zvfhmin | Ext_Zvbb | Ext_Zvbc | Ext_Zvkb | Ext_Zvkg | Ext_Zvkned | Ext_Zvknha | Ext_Zvknhb | Ext_Zvksed | Ext_Zvksh | Ext_Zvkt | Ext_Zvkn | Ext_Zvknc | Ext_Zvkng | Ext_Zvks | Ext_Zvksc | Ext_Zvksg | Ext_Ssccptr | Ext_Sscofpmf | Ext_Sscounterenw | Ext_Ssdbltrp | Ext_Ssnpm | Ext_Ssstateen | Ext_Ssstrict | Ext_Sstc | Ext_Sstvala | Ext_Sstvecd | Ext_Ssu64xl | Ext_Svbare | Ext_Sv32 | Ext_Sv39 | Ext_Sv48 | Ext_Sv57 | Ext_Svade | Ext_Svadu | Ext_Svinval | Ext_Svnapot | Ext_Svpbmt | Ext_Svrsw60t59b | Ext_Svukte | Ext_Svvptc | Ext_Smcntrpmf | Ext_Smdbltrp | Ext_Smmpm | Ext_Smnpm | Ext_Smstateen | Ext_Ssqosid | Ext_Sspm | Ext_Supm
  deriving BEq, Inhabited, Repr
  open extension

abbrev MEnvcfg := (BitVec 64)

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

inductive Register : Type where
  | elp
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
  | .elp => (BitVec 1)
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



instance : Inhabited (RegisterRef Privilege) where
  default := .Reg cur_privilege
instance : Inhabited (RegisterRef (BitVec 1)) where
  default := .Reg elp
instance : Inhabited (RegisterRef (BitVec 32)) where
  default := .Reg misa
instance : Inhabited (RegisterRef (BitVec 64)) where
  default := .Reg mstatus