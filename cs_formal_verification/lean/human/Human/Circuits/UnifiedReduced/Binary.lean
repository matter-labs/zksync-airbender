import Human.Circuits.UnifiedReduced.Decoder
import Human.Circuits.UnifiedReduced.Tables.Setup
import Human.Helpers.Context.RowContext
import Human.Helpers.Decoder.Instruction
import Human.Helpers.Decoder.PooledProgram

namespace Airbender.UnifiedReduced.Binary
open Arithmetic Trace

/-- Canonical words observed in the imported unified register ports. All numeric
    placement IDs stay here; the model below uses named observations. -/
def leftWord {p : Nat} (w : Nat → ZMod p) : Word := ⟨(w 36).val, (w 37).val⟩
def rightWord {p : Nat} (w : Nat → ZMod p) : Word := ⟨(w 42).val, (w 43).val⟩
def initialPC {p : Nat} (w : Nat → ZMod p) : Word := ⟨(w 0).val, (w 1).val⟩
def destination {p : Nat} (w : Nat → ZMod p) : Word := ⟨(w 50).val, (w 51).val⟩
def finalPC {p : Nat} (w : Nat → ZMod p) : Word := ⟨(w 30).val, (w 31).val⟩

end Airbender.UnifiedReduced.Binary
