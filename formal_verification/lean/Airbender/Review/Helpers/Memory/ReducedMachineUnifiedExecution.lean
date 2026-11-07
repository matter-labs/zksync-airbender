import Airbender.Review.Helpers.Decoder.ReducedMachineUnified
import Airbender.Review.Helpers.Decoder.ReducedMachineSupported
import Airbender.Review.Helpers.Memory.ReducedMachineWordMemoryPlatform

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option autoImplicit false

/-- Original public memory constructors activate reference memory configuration;
    local row profiles and successful accesses are not inputs. -/
def InstructionUsesWordMemory : SailRV32.instruction → Prop
  | .LOAD _ | .STORE _ => True
  | _ => False

/-- Meaningful INITIAL reference configuration, conditional on original public
    constructors. Ordinary/empty programs need no CSR availability; branch/JAL
    misa remains unrestricted and only JALR activates its security configuration. -/
structure UnifiedISA (setup : SparseDecoderSetup UnifiedMode) (initial : State) : Prop where
  control : (∃ entry ∈ setup.program, InstructionUsesMisa entry.instruction) →
    ∃ value, initial.regs.get? .misa = some value
  indirect : (∃ entry ∈ setup.program, ∃ args, entry.instruction = .JALR args) →
    initial.regs.get? .cur_privilege = some .Machine ∧ ∃ security,
      initial.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0
  memory : (∃ entry ∈ setup.program, InstructionUsesWordMemory entry.instruction) →
    FlatMemoryConfiguration initial

/-- Only public memory constructors require the architectural RAM domain to
    exclude the pinned platform's special windows. -/
def UnifiedOrdinaryCells (setup : SparseDecoderSetup UnifiedMode) (cells : List Cell) : Prop :=
  (∃ entry ∈ setup.program, InstructionUsesWordMemory entry.instruction) → WordMemoryOrdinaryCells cells

/-- Reference dispatch retains original clauses and operands. The existing
    registerClause and wordMemoryClause are unchanged. -/
def unifiedClause [MemoryPlatform SailRV32.exception] (instruction : SailRV32.instruction) :
    Option (SailRV32.SailM SailRV32.ExecutionResult) :=
  match instruction with
  | .LOAD _ | .STORE _ => wordMemoryClause instruction
  | _ => registerClause instruction

end Airbender.ReducedMachine.Native
