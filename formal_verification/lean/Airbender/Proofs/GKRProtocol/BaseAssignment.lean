import Airbender.Proofs.GKRProtocol.BaseEncoding
import Mathlib.Data.List.Nodup

namespace Airbender.Compiler
set_option warningAsError true

/-- Build the finite address interpretation once. Its inverse law follows
generically from distinct addresses, rather than repeated finite searches. -/
def WireBank.ofList (entries : List GKRAddress) (nonempty : 0 < entries.length) : WireBank entries.length where
  address := entries.get
  placement address :=
    let index := entries.findIdx (fun candidate => addressEqual candidate address)
    if bound : index < entries.length then ⟨index, bound⟩ else ⟨0, nonempty⟩

theorem WireBank.ofList_roundTrip (entries : List GKRAddress) (nonempty : 0 < entries.length)
    (unique : entries.Nodup) (index : Fin entries.length) :
    (WireBank.ofList entries nonempty).placement ((WireBank.ofList entries nonempty).address index) = index := by
  have found : entries.findIdx (fun candidate => addressEqual candidate (entries.get index)) = index.val := by
    apply (List.findIdx_eq index.isLt).mpr
    refine ⟨(addressEqual_iff _ _).mpr rfl, ?_⟩
    intro earlier smaller
    apply Bool.eq_false_iff.mpr
    intro same
    have equalElements : entries.get ⟨earlier, Nat.lt_trans smaller index.isLt⟩ = entries.get index :=
      (addressEqual_iff _ _).mp same
    have equalIndices := unique.injective_get equalElements
    have equalValues : earlier = index.val := congrArg (fun i : Fin entries.length => i.val) equalIndices
    omega
  change (if bound : entries.findIdx (fun candidate => addressEqual candidate (entries.get index)) < entries.length then
    ⟨entries.findIdx (fun candidate => addressEqual candidate (entries.get index)), bound⟩ else ⟨0, nonempty⟩) = index
  rw [found]
  simp only [dif_pos index.isLt]

theorem WireBank.ofList_prefix (entries inputs : List GKRAddress)
    (nonempty : 0 < entries.length) (inputsNonempty : 0 < inputs.length)
    (bound : inputs.length ≤ entries.length) (initialSegment : entries.take inputs.length = inputs)
    (index : Fin inputs.length) :
    (WireBank.ofList entries nonempty).address (index.castLE bound) =
      (WireBank.ofList inputs inputsNonempty).address index := by
  have same := congrArg (fun items : List GKRAddress => items[index.val]?) initialSegment
  have nativeBound : index.val < entries.length := Nat.lt_of_lt_of_le index.isLt bound
  change entries.get (index.castLE bound) = inputs.get index
  apply Option.some.inj
  simpa only [List.getElem?_take_of_lt index.isLt, List.getElem?_eq_getElem nativeBound,
    List.getElem?_eq_getElem index.isLt, List.get_eq_getElem, Fin.val_castLE] using same


/-- Extend a finite native base assignment to the complete address space.
Unmentioned setup/input cells retain their externally supplied interpretation. -/
def WireBank.materialize (bank : WireBank n) (values : Fin n → Source.BaseField)
    (fallback : GKRAddress → Source.BaseField) (address : GKRAddress) : Source.BaseField :=
  if addressEqual (bank.address (bank.placement address)) address then values (bank.placement address)
  else fallback address

theorem WireBank.materialize_at (bank : WireBank n)
    (roundTrip : ∀ index, bank.placement (bank.address index) = index)
    (values : Fin n → Source.BaseField) (fallback : GKRAddress → Source.BaseField) (index : Fin n) :
    bank.materialize values fallback (bank.address index) = values index := by
  simp only [materialize, roundTrip, (addressEqual_iff _ _).mpr rfl, ↓reduceIte]

theorem WireBank.materialize_source_input (bank : WireBank m) (inputBank : WireBank n)
    (projection : Fin n → Fin m) (coordinates : ∀ index, bank.address (projection index) = inputBank.address index)
    (roundTrip : ∀ index, bank.placement (bank.address index) = index)
    (inputs : Fin n → Source.BaseField) (extended : Fin m → Source.BaseField)
    (preserved : ∀ index, extended (projection index) = inputs index)
    (fallback : GKRAddress → Source.BaseField) (index : Fin n) :
    bank.materialize extended fallback (inputBank.address index) = inputs index := by
  rw [← coordinates index, bank.materialize_at roundTrip, preserved]

theorem WireBank.materialize_gates (bank : WireBank n)
    (roundTrip : ∀ index, bank.placement (bank.address index) = index)
    (values : Fin n → Source.BaseField) (fallback : GKRAddress → Source.BaseField)
    (gates : List (ArithmeticGate n Source.BaseField))
    (holds : ∀ gate ∈ gates, gate.expressionResidual values = 0) :
    ∀ gate ∈ gates, gate.expressionResidual (bank.materialize values fallback ∘ bank.address) = 0 := by
  have same : bank.materialize values fallback ∘ bank.address = values :=
    funext (bank.materialize_at roundTrip values fallback)
  simpa only [same] using holds

end Airbender.Compiler
