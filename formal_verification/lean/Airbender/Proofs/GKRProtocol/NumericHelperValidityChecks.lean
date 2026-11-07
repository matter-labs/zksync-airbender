import Airbender.Proofs.GKRProtocol.CanonicalSource
import Airbender.Proofs.GKRProtocol.NumericHistoryErasureChecks
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.NumericHelperValidityChecks
set_option warningAsError true
open NumericPolynomialChecks

structure Borrow where
  memory : List NumericPolynomialChecks.Data
  indices : List Nat

structure Transport where
  columns : List (Nat × Nat)
  left : NumericPolynomialChecks.Data
  right : NumericPolynomialChecks.Data

structure Capture where
  coordinates : List Nat
  borrowBound : Nat
  protectedFields : List (NumericPolynomialChecks.Data × NumericPolynomialChecks.Data)
  borrows : List Borrow
  transports : List Transport


theorem capture_eq (left right : Capture)
    (coordinatesBinding : left.coordinates = right.coordinates)
    (boundBinding : left.borrowBound = right.borrowBound)
    (protectedBinding : left.protectedFields = right.protectedFields)
    (borrowBinding : left.borrows = right.borrows)
    (transportBinding : left.transports = right.transports) : left = right := by
  cases left; cases right
  cases coordinatesBinding; cases boundBinding; cases protectedBinding
  cases borrowBinding; cases transportBinding
  rfl

def borrowCheck (coordinates : List Nat) (bound : Nat) (data : Borrow) : Bool :=
  data.memory.all (NumericQueryFrameChecks.untouched coordinates) &&
    data.indices.all (fun index => decide (index < bound))

def transportCheck (data : Transport) : Bool :=
  data.columns.all (fun pair => pair.1 == pair.2) && data.left == data.right

def check (p : Nat) (data : Capture) : Bool :=
  data.protectedFields.all (NumericHistoryErasureChecks.fieldsCheck p) &&
    data.borrows.all (borrowCheck data.coordinates data.borrowBound) &&
    data.transports.all transportCheck

def ofBorrow (placement : Source.HelperPlacement n) : Source.HelperField → Borrow
  | .memory field => ⟨[encode (field.polynomial placement.memory)], []⟩
  | .borrow index => ⟨[], [index]⟩
  | .add left right =>
      let a := ofBorrow placement left
      let b := ofBorrow placement right
      ⟨a.memory ++ b.memory, a.indices ++ b.indices⟩
  | .scale _ inner | .neg inner => ofBorrow placement inner

theorem ofBorrow_check (placement : Source.HelperPlacement n) (slots : Fin k → Fin n)
    (field : Source.HelperField) :
    borrowCheck ((List.ofFn slots).map Fin.val) k (ofBorrow placement field) =
      field.borrowCheck placement slots := by
  induction field with
  | memory field => simp only [ofBorrow, borrowCheck, List.all_cons, List.all_nil,
      Bool.and_true, NumericQueryFrameChecks.untouched_encode, Source.HelperField.borrowCheck]
  | borrow index => simp only [ofBorrow, borrowCheck, List.all_cons, List.all_nil,
      Bool.and_true, Bool.true_and, Source.HelperField.borrowCheck]
  | add left right ihLeft ihRight =>
      simp only [ofBorrow, borrowCheck, List.all_append, Source.HelperField.borrowCheck] at *
      rw [← ihLeft, ← ihRight]
      simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  | scale coefficient inner ih => exact ih
  | neg inner ih => exact ih

def ofTransport (field : Source.HelperField)
    (sourcePlacement : Source.HelperPlacement n) (nativePlacement : Source.HelperPlacement m)
    (inputBank : WireBank n) (nativeBank : WireBank m) : Transport where
  columns := (field.polynomial nativePlacement).flatMap fun term => term.2.map fun wire =>
    (AddressUniqueChecks.addressCode (inputBank.address (inputBank.placement (nativeBank.address wire))),
      AddressUniqueChecks.addressCode (nativeBank.address wire))
  left := encode (rename (inputBank.placement ∘ nativeBank.address) (field.polynomial nativePlacement))
  right := encode (field.polynomial sourcePlacement)

theorem exact_polynomial_eq (left right : Polynomial n Source.BaseField) :
    (encode left == encode right) = decide (left = right) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq]
  exact encode_injective.eq_iff

theorem ofTransport_check (field : Source.HelperField)
    (sourcePlacement : Source.HelperPlacement n) (nativePlacement : Source.HelperPlacement m)
    (inputBank : WireBank n) (nativeBank : WireBank m) :
    transportCheck (ofTransport field sourcePlacement nativePlacement inputBank nativeBank) =
      field.transportCheck sourcePlacement nativePlacement inputBank nativeBank := by
  simp only [transportCheck, ofTransport, Source.HelperField.transportCheck,
    List.all_flatMap, List.all_map, Function.comp_def,
    NumericWorkerPortChecks.addressCode_eq, exact_polynomial_eq]
  rfl

def ofTyped (history : List (Fin n)) (profile : Source.HelperProfile)
    (sourcePlacement : Source.HelperPlacement n) (slots : Fin k → Fin n)
    (fields : List Source.HelperField) (nativePlacement : Source.HelperPlacement m)
    (inputBank : WireBank n) (nativeBank : WireBank m) : Capture where
  coordinates := (List.ofFn slots).map Fin.val
  borrowBound := k
  protectedFields := profile.protectedFields.map fun field =>
    NumericHistoryErasureChecks.fastErasedPair history (field.polynomial sourcePlacement.memory)
  borrows := fields.map (ofBorrow sourcePlacement)
  transports := fields.map fun field => ofTransport field sourcePlacement nativePlacement inputBank nativeBank

theorem ofTyped_check (history : List (Fin n)) (profile : Source.HelperProfile)
    (sourcePlacement : Source.HelperPlacement n) (slots : Fin k → Fin n)
    (fields : List Source.HelperField) (nativePlacement : Source.HelperPlacement m)
    (inputBank : WireBank n) (nativeBank : WireBank m) :
    check babyBearModulus (ofTyped history profile sourcePlacement slots fields nativePlacement inputBank nativeBank) =
      (profile.protectedFields.all (fun field =>
        equal (substitute (erasurePolynomials history) (field.polynomial sourcePlacement.memory))
          (field.polynomial sourcePlacement.memory)) &&
      fields.all (Source.HelperField.borrowCheck sourcePlacement slots) &&
      fields.all (fun field => field.transportCheck sourcePlacement nativePlacement inputBank nativeBank)) := by
  simp only [check, ofTyped, List.all_map, Function.comp_def,
    NumericHistoryErasureChecks.fastErasedPair_eq,
    NumericHistoryErasureChecks.fields_encode, ofBorrow_check, ofTransport_check]

theorem check_sound (data : Capture) (history : List (Fin n)) (profile : Source.HelperProfile)
    (sourcePlacement : Source.HelperPlacement n) (slots : Fin k → Fin n)
    (fields : List Source.HelperField) (nativePlacement : Source.HelperPlacement m)
    (inputBank : WireBank n) (nativeBank : WireBank m)
    (binding : data = ofTyped history profile sourcePlacement slots fields nativePlacement inputBank nativeBank)
    (checked : check babyBearModulus data = true) :
    (profile.protectedFields.all (fun field =>
        equal (substitute (erasurePolynomials history) (field.polynomial sourcePlacement.memory))
          (field.polynomial sourcePlacement.memory)) = true ∧
      fields.all (Source.HelperField.borrowCheck sourcePlacement slots) = true) ∧
      fields.all (fun field => field.transportCheck sourcePlacement nativePlacement inputBank nativeBank) = true := by
  rw [binding, ofTyped_check] at checked
  simpa only [Bool.and_eq_true] using checked

end Airbender.Compiler.NumericHelperValidityChecks
