import Airbender.Proofs.GKRProtocol.NumericMemoryFrameChecks

namespace Airbender.Compiler.NumericMemoryFrameChecks
open NumericPolynomialChecks
set_option warningAsError true

/-- Reuse the proved input prefix. Keep the complete original numeric value. -/
def ofTypedPrefix (ram initialization execution : List Source.MemoryField)
    (placement : Source.MemoryPlacement k) (nativeBank : WireBank k)
    (active allCoordinates : List (Fin n)) (inputBank : WireBank n) (fullBank : WireBank m) : Capture :=
  {ofTyped ram initialization execution placement nativeBank active allCoordinates inputBank fullBank with
    placement := LookupTable.ofList 8 (List.ofFn fun wire : Fin k =>
      if wire.val < n then wire.val else (inputBank.placement (nativeBank.address wire)).val)
    inputAddress := LookupTable.ofList 8 (List.ofFn fun wire : Fin k =>
      if wire.val < n then AddressUniqueChecks.addressCode (nativeBank.address wire)
      else AddressUniqueChecks.addressCode (inputBank.address (inputBank.placement (nativeBank.address wire))))
    fullAddress := LookupTable.ofList 8 (List.ofFn fun wire : Fin k =>
      if wire.val < n then AddressUniqueChecks.addressCode (nativeBank.address wire)
      else AddressUniqueChecks.addressCode (fullBank.address (fullBank.placement (nativeBank.address wire))))}

theorem ofTypedPrefix_eq (ram initialization execution : List Source.MemoryField)
    (placement : Source.MemoryPlacement k) (nativeBank : WireBank k)
    (active allCoordinates : List (Fin n)) (inputBank : WireBank n) (fullBank : WireBank m)
    (inputCoordinates : ∀ wire : Fin k, ∀ inside : wire.val < n,
      nativeBank.address wire = inputBank.address ⟨wire.val, inside⟩)
    (inputRoundTrip : ∀ wire, inputBank.placement (inputBank.address wire) = wire)
    (projection : Fin n → Fin m)
    (fullCoordinates : ∀ wire, fullBank.address (projection wire) = inputBank.address wire)
    (fullRoundTrip : ∀ wire, fullBank.placement (fullBank.address wire) = wire) :
    ofTypedPrefix ram initialization execution placement nativeBank active allCoordinates inputBank fullBank =
      ofTyped ram initialization execution placement nativeBank active allCoordinates inputBank fullBank := by
  have placementEqual : (List.ofFn fun wire : Fin k =>
      if wire.val < n then wire.val else (inputBank.placement (nativeBank.address wire)).val) =
      List.ofFn (fun wire : Fin k => (inputBank.placement (nativeBank.address wire)).val) := by
    congr 1
    funext wire
    by_cases inside : wire.val < n
    · simp only [if_pos inside, inputCoordinates wire inside, inputRoundTrip]
    · simp only [if_neg inside]
  have inputEqual : (List.ofFn fun wire : Fin k =>
      if wire.val < n then AddressUniqueChecks.addressCode (nativeBank.address wire)
      else AddressUniqueChecks.addressCode (inputBank.address (inputBank.placement (nativeBank.address wire)))) =
      List.ofFn (fun wire : Fin k =>
        AddressUniqueChecks.addressCode (inputBank.address (inputBank.placement (nativeBank.address wire)))) := by
    congr 1
    funext wire
    by_cases inside : wire.val < n
    · simp only [if_pos inside, inputCoordinates wire inside, inputRoundTrip]
    · simp only [if_neg inside]
  have fullEqual : (List.ofFn fun wire : Fin k =>
      if wire.val < n then AddressUniqueChecks.addressCode (nativeBank.address wire)
      else AddressUniqueChecks.addressCode (fullBank.address (fullBank.placement (nativeBank.address wire)))) =
      List.ofFn (fun wire : Fin k =>
        AddressUniqueChecks.addressCode (fullBank.address (fullBank.placement (nativeBank.address wire)))) := by
    congr 1
    funext wire
    by_cases inside : wire.val < n
    · simp only [if_pos inside]
      have seen : fullBank.address (projection ⟨wire.val, inside⟩) = nativeBank.address wire :=
        (fullCoordinates ⟨wire.val, inside⟩).trans (inputCoordinates wire inside).symm
      have returned : fullBank.address (fullBank.placement (nativeBank.address wire)) = nativeBank.address wire := by
        calc
          _ = fullBank.address (fullBank.placement (fullBank.address (projection ⟨wire.val, inside⟩))) :=
            congrArg (fun address => fullBank.address (fullBank.placement address)) seen.symm
          _ = fullBank.address (projection ⟨wire.val, inside⟩) := congrArg fullBank.address (fullRoundTrip _)
          _ = nativeBank.address wire := seen
      exact congrArg AddressUniqueChecks.addressCode returned.symm
    · simp only [if_neg inside]
  unfold ofTypedPrefix
  rw [placementEqual, inputEqual, fullEqual]
  rfl

theorem address_getter_prefix (entries inputs : List GKRAddress) (nonempty : 0 < inputs.length)
    (initialSegment : entries.take inputs.length = inputs) (wire : Fin inputs.length) :
    (entries[wire.val]?).getD (.BaseLayerWitness 0) = (WireBank.ofList inputs nonempty).address wire := by
  have same := congrArg (fun items : List GKRAddress => items[wire.val]?) initialSegment
  simp only [List.getElem?_take_of_lt wire.isLt] at same
  change (entries[wire.val]?).getD (.BaseLayerWitness 0) = inputs.get wire
  rw [same]
  simp only [List.getElem?_eq_getElem wire.isLt, Option.getD_some, List.get_eq_getElem]

end Airbender.Compiler.NumericMemoryFrameChecks
