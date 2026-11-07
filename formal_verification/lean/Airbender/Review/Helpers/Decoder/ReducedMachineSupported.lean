import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Review.Circuits.ReducedMachine.SupportedDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Complete original public sparse/padded membership for mixed selected shift
    arithmetic, bitwise, comparison, branch and jump rows. Native fixed-ROM/physical setup fidelity stays separate. -/
def SupportedDecodedTrace {p : Nat} [Fact p.Prime] (trace : Data p NativeReducedFamily)
    (setup : SparseDecoderSetup SupportedMode) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery

/-- Original clauses that read misa on successful ordinary control flow. -/
def InstructionUsesMisa : SailRV32.instruction → Prop
  | .BTYPE _ | .JAL _ | .JALR _ => True
  | _ => False

/-- Initial reference configuration, conditional on original public constructors.
    Values are not local row answers; actual history derives every CSR read. -/
def SupportedISA (setup : SparseDecoderSetup SupportedMode)
    (initial : Reference.RiscV.Sail.State) : Prop :=
  ((∃ entry ∈ setup.program, InstructionUsesMisa entry.instruction) →
    ∃ value, initial.regs.get? .misa = some value) ∧
  ((∃ entry ∈ setup.program, ∃ args, entry.instruction = .JALR args) →
    initial.regs.get? .cur_privilege = some .Machine ∧ ∃ security,
      initial.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0)

end Airbender.ReducedMachine.Native
