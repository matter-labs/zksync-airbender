import Airbender.Review.Helpers.Decoder.Program
import Airbender.Review.Helpers.Memory.ROM
import Airbender.Review.Helpers.Memory.Platform
import Airbender.Review.Helpers.Memory.Values

namespace Airbender.Trace
open Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- Dispatch original Sail memory clauses or the shared register/control dispatcher.
    Unsupported instruction constructors have no execution clause. -/
def instructionClause : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult)
  | .LOAD (imm, rs1, rd, unsigned, size) =>
    some (SailRV32.Functions.execute_LOAD imm rs1 rd unsigned size)
  | .STORE (imm, rs2, rs1, size) => some (SailRV32.Functions.execute_STORE imm rs2 rs1 size)
  | instruction => registerClause instruction

/-- Select unchanged Sail semantics or the explicitly documented LW-to-x0
    Airbender deviation. The selected profile is visible in the execution claim. -/
inductive ISAProfile where
  | sail
  | airbender

/-- The pinned Airbender ISA table makes LW-to-x0 a PC-only NOP, even for
    unaligned addresses (`vendor/airbender/00-master.md`, LW row). Implement
    that one deviation with the original Sail ADDI x0,x0,0 clause. All other
    selected instructions execute their unchanged original Sail clauses. -/
def profileClause (profile : ISAProfile) (instruction : SailRV32.instruction) :
    Option (SailRV32.SailM SailRV32.ExecutionResult) :=
  match profile, instruction with
  | .airbender, .LOAD (_, _, .Regidx 0, false, 4) =>
    some (SailRV32.Functions.execute_ITYPE 0 (.Regidx 0) (.Regidx 0) .ADDI)
  | _, _ => instructionClause instruction

/-- Exclude LW-to-x0 from an unchanged-Sail claim. Airbender treats that
    instruction as a NOP, whereas original Sail can perform a failing memory
    access. The explicit Airbender profile covers this deviation separately. -/
def NoDiscardedLoads {Kind : Type} (program : List (ProgramEntry Kind)) : Prop :=
  ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
    entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)

end Airbender.Trace
