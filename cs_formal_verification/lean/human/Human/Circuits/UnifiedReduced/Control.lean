import Human.Circuits.UnifiedReduced.Decoder
import Human.Circuits.UnifiedReduced.Tables.Setup
import Human.Circuits.JumpBranchSlt.Model

namespace Airbender.UnifiedReduced.Control
open Arithmetic Trace

/-- Native register, immediate, destination and PC observations. Numeric placement
    IDs stay here; the mappings below use these names. -/
def leftWord (w : Nat → ZMod p) : Word := ⟨(w 36).val, (w 37).val⟩
def rightWord (w : Nat → ZMod p) : Word := ⟨(w 42).val, (w 43).val⟩
def comparisonRight (w : Nat → ZMod p) : Word := ⟨(w 42 + w 8).val, (w 43 + w 9).val⟩
def offsetWord (w : Nat → ZMod p) : Word := ⟨(w 8).val, (w 9).val⟩
def initialPC (w : Nat → ZMod p) : Word := ⟨(w 0).val, (w 1).val⟩
def destination (w : Nat → ZMod p) : Word := ⟨(w 50).val, (w 51).val⟩
def finalPC (w : Nat → ZMod p) : Word := ⟨(w 30).val, (w 31).val⟩

namespace Comparison

end Comparison

namespace Branch

end Branch
end Airbender.UnifiedReduced.Control
