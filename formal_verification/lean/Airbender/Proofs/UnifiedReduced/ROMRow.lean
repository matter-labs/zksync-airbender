import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.UnifiedReduced.ROMView
import Airbender.Proofs.UnifiedReduced
import Airbender.Review.Helpers.UnifiedReduced.Registry

namespace Airbender.UnifiedReduced.ROMView
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

@[simp] theorem row_family (before : Reference.RiscV.Sail.State) (native : Trace.Row p UnifiedFamily) :
    (row before native).family = native.family := by unfold row; split <;> rfl
@[simp] theorem row_start (before : Reference.RiscV.Sail.State) (native : Trace.Row p UnifiedFamily) :
    (row before native).start = native.start := by
  unfold row
  split <;> simp [Row.start, Row.columns, rawPair, CircuitLayout.columns,
    importedConstraintsTraceColumns, readData]
@[simp] theorem row_finish (before : Reference.RiscV.Sail.State) (native : Trace.Row p UnifiedFamily) :
    (row before native).finish = native.finish := by
  unfold row
  split <;> simp [Row.finish, Row.columns, rawPair, CircuitLayout.columns,
    importedConstraintsTraceColumns, readData]
@[simp] theorem row_query (before : Reference.RiscV.Sail.State) (native : Trace.Row p UnifiedFamily) :
    (row before native).decoderQuery = native.decoderQuery := by
  unfold row
  split <;> simp [Row.decoderQuery, nativeDecoderQuery, Row.decoderColumns, Row.columns,
    CircuitLayout.columns, CircuitLayout.decoderColumns, importedConstraintsTraceColumns,
    importedConstraintsDecoderColumns, readData]
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;> rfl

theorem row_holds [Fact p.Prime] (hp : FieldCapacity.NoWrap p 18)
    (before : Reference.RiscV.Sail.State) (native : Trace.Row p UnifiedFamily)
    (setup : Table (ZMod p) (fields 10))
    (active : native.assignment 4 = 1)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment native.assignment)
      (native.constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row before native).assignment)
      ((row before native).constraints setup) := by
  obtain ⟨family, w⟩ := native
  cases family
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup) at holds
  unfold row
  split
  · rename_i condition
    dsimp only
    have core := Verification.holds_of_sublist holds
      (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
    have excluded := Proofs.dispatch_exclusive hp core active 16 condition.1
    have arithmetic (i : Fin 10) : w (11 + i.val) = 0 := by
      have bit := excluded ⟨i.val, by have := i.isLt; omega⟩ (by
        intro equal
        have value := congrArg Fin.val equal
        change i.val = 16 at value
        have := i.isLt
        omega)
      fin_cases i <;> exact bit
    have other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0 :=
      ⟨excluded 10 (by decide), excluded 11 (by decide), excluded 12 (by decide), excluded 13 (by decide)⟩
    have binary : w 26 = 0 ∧ w 27 = 0 := ⟨excluded 14 (by decide), excluded 15 (by decide)⟩
    exact read_data_unused condition.1 (excluded 17 (by decide)) condition.2 arithmetic other binary _ _ holds
  · exact holds

end Airbender.UnifiedReduced.ROMView
