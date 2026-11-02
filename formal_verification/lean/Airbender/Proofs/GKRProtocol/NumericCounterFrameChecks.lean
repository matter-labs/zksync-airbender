import Airbender.Proofs.GKRProtocol.CounterFrame
import Airbender.Proofs.GKRProtocol.NumericQueryFrameChecks
import Mathlib.Data.List.FinRange

namespace Airbender.Compiler.NumericCounterFrameChecks
set_option warningAsError true
open NumericPolynomialChecks

structure Capture where
  columns : List Nat
  exportedColumns : List Nat
  slots : List Nat
  returns : List (Nat × Nat)
  source : List Data
  helpers : List Data

def check (sourceCount : Nat) (data : Capture) : Bool :=
  (data.columns == data.exportedColumns) && decide data.slots.Nodup &&
    data.slots.all (fun slot => decide (sourceCount ≤ slot)) &&
    data.returns.all (fun pair => pair.1 == pair.2) &&
    data.source.all (NumericQueryFrameChecks.untouched data.slots) &&
    data.helpers.all (NumericQueryFrameChecks.untouched data.slots)

def ofTyped (columns exportedColumns : List Nat) (slots : Fin columns.length → Fin n)
    (bank : WireBank n) (source helpers : List (Polynomial n (ZMod p))) : Capture where
  columns := columns
  exportedColumns := exportedColumns
  slots := (List.ofFn slots).map Fin.val
  returns := List.ofFn (fun index =>
    (AddressUniqueChecks.addressCode (bank.address (slots index)),
      AddressUniqueChecks.addressCode (.BaseLayerWitness (columns.get index))))
  source := source.map encode
  helpers := helpers.map encode

theorem untouched_all (coordinates : List (Fin n)) (polynomials : List (Polynomial n (ZMod p))) :
    (polynomials.map encode).all (NumericQueryFrameChecks.untouched (coordinates.map Fin.val)) =
      polynomials.all (erasureUntouched coordinates) := by
  simp only [List.all_map, Function.comp_def, NumericQueryFrameChecks.untouched_encode]

theorem check_sound (data : Capture) (sourceCount : Nat)
    (columns exportedColumns : List Nat) (slots : Fin columns.length → Fin n)
    (bank : WireBank n) (source helpers : List (Polynomial n (ZMod p)))
    (binding : data = ofTyped columns exportedColumns slots bank source helpers)
    (checked : check sourceCount data = true) :
    columns = exportedColumns ∧ Function.Injective slots ∧
      (∀ index, sourceCount ≤ (slots index).val) ∧
      (∀ index, bank.address (slots index) = GKRAddress.BaseLayerWitness (columns.get index)) ∧
      source.all (erasureUntouched (List.ofFn slots)) = true ∧
      helpers.all (erasureUntouched (List.ofFn slots)) = true := by
  rw [binding] at checked
  simp only [check, ofTyped, Bool.and_eq_true, beq_iff_eq] at checked
  rcases checked with ⟨⟨⟨⟨⟨columnsSame, unique⟩, fresh⟩, roundTrip⟩, sourceCheck⟩, helperCheck⟩
  refine ⟨columnsSame, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.nodup_ofFn.mp (of_decide_eq_true unique).of_map
  · intro index
    have item := List.all_eq_true.mp fresh (slots index).val
      (List.mem_map.mpr ⟨slots index, List.mem_ofFn.mpr ⟨index, rfl⟩, rfl⟩)
    exact of_decide_eq_true item
  · intro index
    apply CleanPlacementChecks.addressCode_injective
    exact beq_iff_eq.mp (List.all_eq_true.mp roundTrip _ (List.mem_ofFn.mpr ⟨index, rfl⟩))
  · simpa only [untouched_all] using sourceCheck
  · simpa only [untouched_all] using helperCheck

end Airbender.Compiler.NumericCounterFrameChecks
