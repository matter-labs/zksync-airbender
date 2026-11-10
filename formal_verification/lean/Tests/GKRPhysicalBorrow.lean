import Airbender.Proofs.GKRProtocol.CanonicalHelpers

namespace Tests.GKRPhysicalBorrow
open Airbender Airbender.Compiler Airbender.Compiler.Source
set_option warningAsError true

private def previous : MemoryWord := ⟨.constant (babyBearModulus - 1), .constant 0⟩
private def current : MemoryWord := .zero
private def memory : MemoryValues :=
  ⟨fun _ => 0, fun _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩
private def actual : HelperValues := ⟨memory, fun _ => 1⟩

/-- Local Boolean/range helper equations admit this noncanonical borrow.
Global timestamp bounds and exact history matching are separate obligations. -/
example : actual.borrow 0 * (actual.borrow 0 - 1) = 0 ∧
    (((comparisonFields previous current 0).1).value actual).val < 524288 ∧
    (((comparisonFields previous current 0).2).value actual).val < 524288 := by
  decide +kernel

/-- A canonical borrow is a stronger restriction than those local checks.
The physical lookup execution entrypoints therefore impose no such frame. -/
example : actual.borrow 0 ≠ (canonicalHelpers memory [(previous, current)]).borrow 0 := by
  decide +kernel

end Tests.GKRPhysicalBorrow
