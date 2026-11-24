module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.QueryFrame
public import Proven.GKRProtocol.NumericPolynomialChecks
public import Proven.GKRProtocol.CleanPlacementChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.NumericQueryFrameChecks
open NumericPolynomialChecks

structure Capture where
  coordinates : List Nat
  placement : List Nat
  nativeAddress : List Nat
  returnedAddress : List Nat
  fields : List (Data × Data)

def lookup (values : List Nat) (index : Nat) : Nat := values[index]?.getD 0

def untouched (coordinates : List Nat) (polynomial : Data) : Bool :=
  polynomial.all fun term => term.2.all fun wire => !coordinates.contains wire

def fieldCheck (data : Capture) (field : Data × Data) : Bool :=
  untouched data.coordinates field.1 &&
    field.2.all (fun term => term.2.all fun wire =>
      lookup data.returnedAddress wire == lookup data.nativeAddress wire) &&
    NumericPolynomialChecks.rename (lookup data.placement) field.2 == field.1

def check (data : Capture) : Bool := data.fields.all (fieldCheck data)

def ofTyped (fields : List Source.EncodedField) (coordinates : List (Fin n))
    (sourcePlacement : Nat → Fin n) (nativePlacement : Nat → Fin m)
    (inputBank : WireBank n) (nativeBank : WireBank m) : Capture where
  coordinates := coordinates.map Fin.val
  placement := List.ofFn (fun wire => (inputBank.placement (nativeBank.address wire)).val)
  nativeAddress := List.ofFn (fun wire => AddressUniqueChecks.addressCode (nativeBank.address wire))
  returnedAddress := List.ofFn (fun wire =>
    AddressUniqueChecks.addressCode (inputBank.address (inputBank.placement (nativeBank.address wire))))
  fields := fields.map (fun field =>
    (encode (field.polynomial sourcePlacement), encode (field.polynomial nativePlacement)))

theorem lookup_ofFn (values : Fin n → Nat) (index : Fin n) :
    lookup (List.ofFn values) index.val = values index := by
  simp [lookup, index.isLt]

theorem contains_val (coordinates : List (Fin n)) (wire : Fin n) :
    (coordinates.map Fin.val).contains wire.val = coordinates.contains wire := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem]
  constructor
  · intro member
    obtain ⟨original, included, same⟩ := List.mem_map.mp member
    exact Fin.val_injective same ▸ included
  · intro member
    exact List.mem_map.mpr ⟨wire, member, rfl⟩

theorem untouched_encode (coordinates : List (Fin n)) (polynomial : Polynomial n (ZMod p)) :
    untouched (coordinates.map Fin.val) (encode polynomial) = erasureUntouched coordinates polynomial := by
  simp only [untouched, encode, erasureUntouched, List.all_map, Function.comp_def, contains_val]

theorem roundTrips_sound (data : Capture) (polynomial : Polynomial m Source.BaseField)
    (inputBank : WireBank n) (nativeBank : WireBank m)
    (nativeBinding : data.nativeAddress = List.ofFn (fun wire =>
      AddressUniqueChecks.addressCode (nativeBank.address wire)))
    (returnedBinding : data.returnedAddress = List.ofFn (fun wire =>
      AddressUniqueChecks.addressCode (inputBank.address (inputBank.placement (nativeBank.address wire)))))
    (checked : (encode polynomial).all (fun term => term.2.all fun wire =>
      lookup data.returnedAddress wire == lookup data.nativeAddress wire) = true) :
    polynomial.all (fun term => term.2.all fun wire =>
      decide (inputBank.address (inputBank.placement (nativeBank.address wire)) = nativeBank.address wire)) = true := by
  apply List.all_eq_true.mpr
  intro term member
  have row := List.all_eq_true.mp checked (term.1.val, term.2.map Fin.val)
    (List.mem_map.mpr ⟨term, member, rfl⟩)
  apply List.all_eq_true.mpr
  intro wire included
  have numeric := beq_iff_eq.mp (List.all_eq_true.mp row wire.val
    (List.mem_map.mpr ⟨wire, included, rfl⟩))
  rw [nativeBinding, returnedBinding, lookup_ofFn, lookup_ofFn] at numeric
  simp only [decide_eq_true_eq]
  exact CleanPlacementChecks.addressCode_injective numeric

theorem field_sound (data : Capture) (field : Source.EncodedField)
    (coordinates : List (Fin n)) (sourcePlacement : Nat → Fin n) (nativePlacement : Nat → Fin m)
    (inputBank : WireBank n) (nativeBank : WireBank m)
    (coordinatesBinding : data.coordinates = coordinates.map Fin.val)
    (placementBinding : data.placement = List.ofFn (fun wire =>
      (inputBank.placement (nativeBank.address wire)).val))
    (nativeBinding : data.nativeAddress = List.ofFn (fun wire =>
      AddressUniqueChecks.addressCode (nativeBank.address wire)))
    (returnedBinding : data.returnedAddress = List.ofFn (fun wire =>
      AddressUniqueChecks.addressCode (inputBank.address (inputBank.placement (nativeBank.address wire)))))
    (checked : fieldCheck data
      (encode (field.polynomial sourcePlacement), encode (field.polynomial nativePlacement)) = true) :
    (erasureUntouched coordinates (field.polynomial sourcePlacement) &&
      field.transportCheck sourcePlacement nativePlacement inputBank nativeBank) = true := by
  simp only [fieldCheck, Bool.and_eq_true, beq_iff_eq] at checked
  apply Bool.and_eq_true_iff.mpr
  constructor
  · rw [coordinatesBinding, untouched_encode] at checked
    exact checked.1.1
  · apply Bool.and_eq_true_iff.mpr
    constructor
    · exact roundTrips_sound data _ inputBank nativeBank nativeBinding returnedBinding checked.1.2
    · simp only [decide_eq_true_eq]
      apply NumericPolynomialChecks.encode_injective
      rw [NumericPolynomialChecks.encode_rename
        (inputBank.placement ∘ nativeBank.address) (lookup data.placement)
        (fun wire => by rw [placementBinding, lookup_ofFn]; rfl)]
      exact checked.2

theorem check_sound (data : Capture) (fields : List Source.EncodedField)
    (coordinates : List (Fin n)) (sourcePlacement : Nat → Fin n) (nativePlacement : Nat → Fin m)
    (inputBank : WireBank n) (nativeBank : WireBank m)
    (coordinatesBinding : data.coordinates = coordinates.map Fin.val)
    (placementBinding : data.placement = List.ofFn (fun wire =>
      (inputBank.placement (nativeBank.address wire)).val))
    (nativeBinding : data.nativeAddress = List.ofFn (fun wire =>
      AddressUniqueChecks.addressCode (nativeBank.address wire)))
    (returnedBinding : data.returnedAddress = List.ofFn (fun wire =>
      AddressUniqueChecks.addressCode (inputBank.address (inputBank.placement (nativeBank.address wire)))))
    (fieldsBinding : data.fields = fields.map (fun field =>
      (encode (field.polynomial sourcePlacement), encode (field.polynomial nativePlacement))))
    (checked : check data = true) :
    fields.all (fun field => erasureUntouched coordinates (field.polynomial sourcePlacement) &&
      field.transportCheck sourcePlacement nativePlacement inputBank nativeBank) = true := by
  apply List.all_eq_true.mpr
  intro field member
  apply field_sound data field coordinates sourcePlacement nativePlacement inputBank nativeBank
    coordinatesBinding placementBinding nativeBinding returnedBinding
  exact List.all_eq_true.mp checked _ (fieldsBinding.symm ▸ List.mem_map.mpr ⟨field, member, rfl⟩)

theorem check_sound_of_binding (data : Capture) (fields : List Source.EncodedField)
    (coordinates : List (Fin n)) (sourcePlacement : Nat → Fin n) (nativePlacement : Nat → Fin m)
    (inputBank : WireBank n) (nativeBank : WireBank m)
    (binding : data = ofTyped fields coordinates sourcePlacement nativePlacement inputBank nativeBank)
    (checked : check data = true) :
    fields.all (fun field => erasureUntouched coordinates (field.polynomial sourcePlacement) &&
      field.transportCheck sourcePlacement nativePlacement inputBank nativeBank) = true :=
  check_sound data fields coordinates sourcePlacement nativePlacement inputBank nativeBank
    (congrArg Capture.coordinates binding) (congrArg Capture.placement binding)
    (congrArg Capture.nativeAddress binding) (congrArg Capture.returnedAddress binding)
    (congrArg Capture.fields binding) checked

end Airbender.Compiler.NumericQueryFrameChecks
