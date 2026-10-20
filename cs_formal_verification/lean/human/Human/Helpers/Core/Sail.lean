import SailRV32
import Human.Helpers.Core.Word

deriving instance DecidableEq for SailRV32.regidx

namespace Airbender.Reference.Sail
open _root_.Sail.ArchSem

/-- Reuse Sail's sequential interpreter; no local register or effect semantics. -/
abbrev run [Arch] {ε α : Type} (program : PreSailM ε α)
    (state : SequentialState Arch.register_type) :=
  (interpretSailEffects program).run state

end Airbender.Reference.Sail

namespace Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
open Airbender.Reference.Sail
open Airbender.Arithmetic

abbrev State := SequentialState SailRV32.RegisterType
abbrev zeroRegister : SailRV32.regidx := .Regidx 0

/-- Projection of the circuit's destination word through Sail's own register-write semantics. -/
def writeResult (rd : SailRV32.regidx) (output : Word) : SailRV32.SailM SailRV32.ExecutionResult := do
  SailRV32.Functions.wX_bits rd output.toBitVec
  pure SailRV32.Functions.RETIRE_SUCCESS

/-- Observable circuit outputs; all other architectural state is checked through Sail. -/
structure Output where
  destination : Word
  pc : Word

/-- Circuit memory outputs become an untagged native Sail write. Byte order and
    state updates are supplied by the pinned sequential interpreter. -/
def writeMemory {size : Nat} (address : BitVec 32) (value : BitVec (8 * size)) :
    SailRV32.SailM Unit :=
  let request : MemRequest := {
    accessKind := .AK_Write (.Write_plain, .Store .Data)
    address := address.zeroExtend 34
    addressSpace := ()
    size := size
    numTag := 0 }
  .impure (.inl (.ok (.memWrite request value 0))) (fun _ => .pure ())

/-- Successful decoded four-byte path: upstream nextPC initialization, instruction
    execution, then upstream PC retirement. Fetch/interrupt/exception handling is excluded. -/
def normalStep (instruction : SailRV32.SailM SailRV32.ExecutionResult) : SailRV32.SailM SailRV32.ExecutionResult := do
  SailRV32.Functions.normal_base_next_pc ()
  let result ← instruction
  SailRV32.Functions.tick_pc ()
  pure result

/-- Interpret the declared outputs using native Sail effects. Stores supply a
    memory write; register-only instructions use the default empty effect. -/
def projectedStep (rd : SailRV32.regidx) (output : Output)
    (memory : SailRV32.SailM Unit := pure ()) : SailRV32.SailM SailRV32.ExecutionResult := do
  SailRV32.writeReg .nextPC output.pc.toBitVec
  memory
  let _ ← writeResult rd output.destination
  SailRV32.writeReg .PC output.pc.toBitVec
  pure SailRV32.Functions.RETIRE_SUCCESS

/-- Shared native-state claim for standard Sail clauses and reviewed custom operations. -/
def stepSpec (before : State) (instruction : SailRV32.SailM SailRV32.ExecutionResult)
    (rd : SailRV32.regidx) (output : Output) (memory : SailRV32.SailM Unit := pure ()) : Prop :=
  ∃ after,
    run (normalStep instruction) before = .ok SailRV32.Functions.RETIRE_SUCCESS after ∧
    run (projectedStep rd output memory) before = .ok SailRV32.Functions.RETIRE_SUCCESS after

/-- Dispatch to the original generated Sail clauses, without defining any
    instruction behavior. Unsupported constructors have no clause here. -/
def registerClause : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult)
  | .RTYPE (rs2, rs1, rd, opcode) => some (SailRV32.Functions.execute_RTYPE rs2 rs1 rd opcode)
  | .ITYPE (imm, rs1, rd, opcode) => some (SailRV32.Functions.execute_ITYPE imm rs1 rd opcode)
  | .SHIFTIOP (amount, rs1, rd, opcode) =>
    some (SailRV32.Functions.execute_SHIFTIOP amount rs1 rd opcode)
  | .REV8 (rs1, rd) => some (SailRV32.Functions.execute_REV8 rs1 rd)
  | .UTYPE (imm, rd, .LUI) => some (SailRV32.Functions.execute_UTYPE imm rd .LUI)
  | .UTYPE (imm, rd, .AUIPC) => some (SailRV32.Functions.execute_UTYPE imm rd .AUIPC)
  | .BTYPE (imm, rs2, rs1, opcode) => some (SailRV32.Functions.execute_BTYPE imm rs2 rs1 opcode)
  | .JAL (imm, rd) => some (SailRV32.Functions.execute_JAL imm rd)
  | .JALR (imm, rs1, rd) => some (SailRV32.Functions.execute_JALR imm rs1 rd)
  | .MUL (rs2, rs1, rd, opcode) => some (SailRV32.Functions.execute_MUL rs2 rs1 rd opcode)
  | .DIV (rs2, rs1, rd, unsigned) => some (SailRV32.Functions.execute_DIV rs2 rs1 rd unsigned)
  | .REM (rs2, rs1, rd, unsigned) => some (SailRV32.Functions.execute_REM rs2 rs1 rd unsigned)
  | _ => none

end Airbender.Reference.RiscV.Sail
