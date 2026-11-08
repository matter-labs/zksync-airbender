module
public import Human.Circuits.UnifiedReduced.Decoder
public import Human.Circuits.UnifiedReduced.Tables.Setup
public import Human.Helpers.Context.RowContext
public import Human.Helpers.Decoder.Instruction
public import Human.Helpers.Decoder.PooledProgram

@[expose] public section

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
