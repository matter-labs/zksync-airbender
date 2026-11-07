import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Review.Circuits.ReducedMachine.JumpDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Complete sparse/padded public decoder membership for the selected jump profile.
    This is a separate logical decoder boundary, not native fixed ROM equivalence
    or physical preprocessing enforcement. -/
def JumpDecodedTrace {p : Nat} [Fact p.Prime] (trace : Data p NativeReducedFamily)
    (setup : SparseDecoderSetup JumpMode) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery

/-- Reference-state configuration only: nonempty jump programs need readable
    misa (value unrestricted); programs containing retained JALR additionally
    use the original Machine/MLPE-clear landing-pad path. Local reads are derived
    through actual history. Empty programs impose no CSR-read requirement. -/
def JumpISA (setup : SparseDecoderSetup JumpMode)
    (initial : Reference.RiscV.Sail.State) : Prop :=
  (setup.program ≠ [] → ∃ value, initial.regs.get? .misa = some value) ∧
  ((∃ entry ∈ setup.program, ∃ args, entry.instruction = .JALR args) →
    initial.regs.get? .cur_privilege = some .Machine ∧ ∃ security,
      initial.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0)

end Airbender.ReducedMachine.Native
