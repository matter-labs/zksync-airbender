import Airbender.Review.Circuits.ReducedMachine.CallerDecoder
import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Review.Helpers.Memory.Values

namespace Airbender.NativeDecodedMain
open Airbender.Trace Airbender.ReducedMachine.Native

/-- The existing local preservation law, with both limbs and every earlier
    same-row source port retained. This is a derived induction rule, not an
    acceptance premise or a claim that copied/read values are already bounded. -/
def RowWriteRule (row : Row mersenne31Modulus NativeReducedFamily) : Prop :=
  ∀ port ∈ row.ports,
    (∀ source ∈ row.ports,
      (source.event row.columns row.assignment).1 ≤ (port.event row.columns row.assignment).1 →
      (readToken row.assignment source).word.Bounded) →
    (writeToken row.columns row.assignment port).word.Bounded

/-- Every actual execute1 main position in the SAME counted source. The old
    complete acceptance still retains inactive main rows and all43 worker ports.
    Scope is the original seven-profile-or-CSR public projection; MOP is absent.
    No original CSR execution, worker result or initialized mixed bound follows. -/
def Effects {R : Type} [Field R] (batch : Airbender.NativeMainDecoder.Batch R) : Prop :=
  ∀ proof ∈ batch.proofs, ∀ i < decoderAuxiliaryLayout.traceLength-1,
    proof.initialization.main.memory.rows i importedConstraintsTraceColumns.execute = 1 →
      RowWriteRule (⟨.reduced,proof.initialization.main.memory.rows i⟩ : Row mersenne31Modulus NativeReducedFamily)
end Airbender.NativeDecodedMain
