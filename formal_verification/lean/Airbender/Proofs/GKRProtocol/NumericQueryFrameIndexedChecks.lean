import Airbender.Proofs.GKRProtocol.NumericQueryFrameChecks
import Airbender.Proofs.GKRProtocol.NumericLookupTable

namespace Airbender.Compiler.NumericQueryFrameChecks
open NumericPolynomialChecks
set_option warningAsError true

/-- Encode membership without repeated scans of the erased coordinates. -/
def coordinateMask : List Nat → Nat
  | [] => 0
  | wire :: rest => 2 ^ wire ||| coordinateMask rest

theorem coordinateMask_contains (coordinates : List Nat) (wire : Nat) :
    (coordinateMask coordinates).testBit wire = coordinates.contains wire := by
  induction coordinates with
  | nil => simp [coordinateMask]
  | cons first rest ih =>
      simp only [coordinateMask, Nat.testBit_or, Nat.testBit_two_pow, ih, List.contains_cons]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq]
      exact eq_comm

structure Index where
  coordinates : Nat
  placement : LookupTable Nat
  nativeAddress : LookupTable Nat
  returnedAddress : LookupTable Nat

def index (data : Capture) : Index where
  coordinates := coordinateMask data.coordinates
  placement := LookupTable.ofList 8 data.placement
  nativeAddress := LookupTable.ofList 8 data.nativeAddress
  returnedAddress := LookupTable.ofList 8 data.returnedAddress

def indexedFieldCheck (views : Index) (field : Data × Data) : Bool :=
  field.1.all (fun term => term.2.all fun wire => !views.coordinates.testBit wire) &&
    field.2.all (fun term => term.2.all fun wire =>
      views.returnedAddress.getD wire 0 == views.nativeAddress.getD wire 0) &&
    NumericPolynomialChecks.rename (fun wire => views.placement.getD wire 0) field.2 == field.1

def indexedCheck (views : Index) (fields : List (Data × Data)) : Bool :=
  views.placement.valid && views.nativeAddress.valid && views.returnedAddress.valid &&
    fields.all (indexedFieldCheck views)

theorem indexedCheck_sound (views : Index) (data : Capture)
    (coordinatesBinding : views.coordinates = coordinateMask data.coordinates)
    (placementBinding : views.placement.toList = data.placement)
    (nativeBinding : views.nativeAddress.toList = data.nativeAddress)
    (returnedBinding : views.returnedAddress.toList = data.returnedAddress)
    (checked : indexedCheck views data.fields = true) : check data = true := by
  simp only [indexedCheck, Bool.and_eq_true] at checked
  have placementLookup : (fun wire => views.placement.getD wire 0) = lookup data.placement := by
    funext wire
    rw [LookupTable.getD_eq _ checked.1.1.1, placementBinding]
    rfl
  have nativeLookup : (fun wire => views.nativeAddress.getD wire 0) = lookup data.nativeAddress := by
    funext wire
    rw [LookupTable.getD_eq _ checked.1.1.2, nativeBinding]
    rfl
  have returnedLookup : (fun wire => views.returnedAddress.getD wire 0) = lookup data.returnedAddress := by
    funext wire
    rw [LookupTable.getD_eq _ checked.1.2, returnedBinding]
    rfl
  have fieldEqual : indexedFieldCheck views = fieldCheck data := by
    funext field
    simp only [indexedFieldCheck, fieldCheck, untouched, coordinatesBinding,
      coordinateMask_contains]
    rw [← placementLookup]
    simp only [← nativeLookup, ← returnedLookup]
  simpa only [check, ← fieldEqual] using checked.2

end Airbender.Compiler.NumericQueryFrameChecks
