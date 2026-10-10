import Airbender.Review.UnifiedReduced.Control
import Airbender.Proofs.UnifiedReduced.RegisterReads
import Airbender.Proofs.UnifiedReduced.ControlMembership

namespace Airbender.UnifiedReduced.Control.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem selectors [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} {entry : ProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (branch : Bool)
    (mask : entry.data.mask = if branch then 24576 else 4096) :
    (w 21 = 0 ∧ w 22 = 0) ∧
    (w 23 = if branch then 0 else 1) ∧ (w 24 = if branch then 1 else 0) ∧
    (w 25 = if branch then 1 else 0) ∧
    (w 26 = 0 ∧ w 27 = 0) ∧ w 28 = 0 ∧ w 29 = 0 ∧ w 87 = 0 := by
  have flags := UnifiedReduced.Proofs.decoder_selectors hp holds
    (UnifiedReduced.Proofs.decoder_field_bounds fields).2.1 query
  have a := flags 10; have b := flags 11; have c := flags 12; have d := flags 13
  have e := flags 14; have f := flags 15; have g := flags 16; have h := flags 17; have i := flags 18
  cases branch <;> simp [mask, importedConstraintsDecoderColumns, Nat.testBit,
    Nat.shiftRight_eq_div_pow] at a b c d e f g h i ⊢
  all_goals refine ⟨⟨a, b⟩, c, d, e, ⟨f, g⟩, h, i, ?_⟩
  all_goals have gate := Verification.assertion_of_holds holds ⟨42, by rw [constraint_count]; decide⟩
  all_goals simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, h] using gate

theorem right_sign_source [Fact p.Prime] {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 21 + w 22 + w 23 + w 24 = 1) : w 60 = w 43 + w 23 * w 9 := by
  have gate := Verification.assertion_of_holds holds ⟨14, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected] at gate
  linear_combination gate

end Airbender.UnifiedReduced.Control.Proofs
