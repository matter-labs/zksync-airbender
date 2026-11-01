import Airbender.Proofs.GKRProtocol.MemoryFrame
import Airbender.Proofs.GKRProtocol.NumericQueryFrameIndexedChecks

namespace Airbender.Compiler.NumericMemoryFrameChecks
open NumericPolynomialChecks
set_option warningAsError true

/-- Decode only the address class needed by the original oracle frame predicate. -/
def independent (code : Nat) : Bool :=
  let parts := Nat.unpair code
  !(parts.1 == 3) && !(parts.1 == 4 && (parts.2 == 0 || parts.2 == 1))

theorem independent_addressCode (address : GKRAddress) :
    independent (AddressUniqueChecks.addressCode address) = lookupOracleIndependent address := by
  cases address with
  | VirtualSetup kind => cases kind <;> simp [independent, AddressUniqueChecks.addressCode, lookupOracleIndependent]
  | _ => simp [independent, AddressUniqueChecks.addressCode, lookupOracleIndependent]

theorem addressCode_beq (left right : GKRAddress) :
    (AddressUniqueChecks.addressCode left == AddressUniqueChecks.addressCode right) = addressEqual left right := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, addressEqual_iff]
  exact CleanPlacementChecks.addressCode_injective.eq_iff

structure Capture where
  activeMask : Nat
  allMask : Nat
  placement : LookupTable Nat
  nativeAddress : LookupTable Nat
  inputAddress : LookupTable Nat
  fullAddress : LookupTable Nat
  ram : List Data
  initialization : List Data
  execution : List Data

def ofTyped (ram initialization execution : List Source.MemoryField)
    (placement : Source.MemoryPlacement k) (nativeBank : WireBank k)
    (active allCoordinates : List (Fin n)) (inputBank : WireBank n) (fullBank : WireBank m) : Capture where
  activeMask := NumericQueryFrameChecks.coordinateMask (active.map Fin.val)
  allMask := NumericQueryFrameChecks.coordinateMask (allCoordinates.map Fin.val)
  placement := LookupTable.ofList 8 (List.ofFn fun wire => (inputBank.placement (nativeBank.address wire)).val)
  nativeAddress := LookupTable.ofList 8 (List.ofFn fun wire => AddressUniqueChecks.addressCode (nativeBank.address wire))
  inputAddress := LookupTable.ofList 8 (List.ofFn fun wire =>
    AddressUniqueChecks.addressCode (inputBank.address (inputBank.placement (nativeBank.address wire))))
  fullAddress := LookupTable.ofList 8 (List.ofFn fun wire =>
    AddressUniqueChecks.addressCode (fullBank.address (fullBank.placement (nativeBank.address wire))))
  ram := ram.map fun field => encode (field.polynomial placement)
  initialization := initialization.map fun field => encode (field.polynomial placement)
  execution := execution.map fun field => encode (field.polynomial placement)

def valid (data : Capture) : Bool :=
  data.placement.valid && data.nativeAddress.valid && data.inputAddress.valid && data.fullAddress.valid

def portCheck (data : Capture) (mask wire : Nat) : Bool :=
  let address := data.nativeAddress.getD wire 0
  if data.inputAddress.getD wire 0 == address then
    !mask.testBit (data.placement.getD wire 0)
  else !(data.fullAddress.getD wire 0 == address) && independent address

def polynomialCheck (data : Capture) (mask : Nat) (polynomial : Data) : Bool :=
  polynomial.all fun term => term.2.all (portCheck data mask)

def check (data : Capture) : Bool :=
  valid data && data.ram.all (polynomialCheck data data.activeMask) &&
    data.initialization.all (polynomialCheck data data.allMask) &&
    data.execution.all (polynomialCheck data data.allMask)

theorem valid_sound (data : Capture) (checked : valid data = true) :
    data.placement.valid = true ∧ data.nativeAddress.valid = true ∧
      data.inputAddress.valid = true ∧ data.fullAddress.valid = true := by
  simpa only [valid, Bool.and_eq_true, and_assoc] using checked

theorem bound_lookup (table : LookupTable Nat) (values : Fin k → Nat)
    (valid : table.valid = true) (binding : table.toList = List.ofFn values) (wire : Fin k) :
    table.getD wire.val 0 = values wire := by
  rw [LookupTable.getD_eq _ valid, binding]
  exact NumericQueryFrameChecks.lookup_ofFn values wire

theorem portCheck_eq (data : Capture) (mask : Nat) (coordinates : List (Fin n))
    (inputBank : WireBank n) (fullBank : WireBank m) (nativeBank : WireBank k)
    (maskBinding : mask = NumericQueryFrameChecks.coordinateMask (coordinates.map Fin.val))
    (placementBinding : data.placement.toList = List.ofFn fun wire =>
      (inputBank.placement (nativeBank.address wire)).val)
    (nativeBinding : data.nativeAddress.toList = List.ofFn fun wire =>
      AddressUniqueChecks.addressCode (nativeBank.address wire))
    (inputBinding : data.inputAddress.toList = List.ofFn fun wire =>
      AddressUniqueChecks.addressCode (inputBank.address (inputBank.placement (nativeBank.address wire))))
    (fullBinding : data.fullAddress.toList = List.ofFn fun wire =>
      AddressUniqueChecks.addressCode (fullBank.address (fullBank.placement (nativeBank.address wire))))
    (valid : valid data = true) (wire : Fin k) :
    portCheck data mask wire.val = sourcePortFrameCheck coordinates inputBank fullBank (nativeBank.address wire) := by
  have flags := valid_sound data valid
  have actualPlacement := bound_lookup _ _ flags.1 placementBinding wire
  have actualNative := bound_lookup _ _ flags.2.1 nativeBinding wire
  have actualInput := bound_lookup _ _ flags.2.2.1 inputBinding wire
  have actualFull := bound_lookup _ _ flags.2.2.2 fullBinding wire
  simp only [portCheck, sourcePortFrameCheck, actualPlacement, actualNative, actualInput, actualFull,
    addressCode_beq, maskBinding, NumericQueryFrameChecks.coordinateMask_contains,
    NumericQueryFrameChecks.contains_val, independent_addressCode]

theorem fields_sound (data : Capture) (mask : Nat) (fields : List Source.MemoryField)
    (placement : Source.MemoryPlacement k) (nativeBank : WireBank k)
    (coordinates : List (Fin n)) (inputBank : WireBank n) (fullBank : WireBank m)
    (maskBinding : mask = NumericQueryFrameChecks.coordinateMask (coordinates.map Fin.val))
    (placementBinding : data.placement.toList = List.ofFn fun wire =>
      (inputBank.placement (nativeBank.address wire)).val)
    (nativeBinding : data.nativeAddress.toList = List.ofFn fun wire =>
      AddressUniqueChecks.addressCode (nativeBank.address wire))
    (inputBinding : data.inputAddress.toList = List.ofFn fun wire =>
      AddressUniqueChecks.addressCode (inputBank.address (inputBank.placement (nativeBank.address wire))))
    (fullBinding : data.fullAddress.toList = List.ofFn fun wire =>
      AddressUniqueChecks.addressCode (fullBank.address (fullBank.placement (nativeBank.address wire))))
    (valid : valid data = true)
    (checked : (fields.map fun field => encode (field.polynomial placement)).all (polynomialCheck data mask) = true) :
    fields.all (fun field => field.baseFrameCheck placement nativeBank coordinates inputBank fullBank) = true := by
  simpa only [List.all_map, Function.comp_def, polynomialCheck, encode,
    portCheck_eq data mask coordinates inputBank fullBank nativeBank maskBinding placementBinding nativeBinding
      inputBinding fullBinding valid, Source.MemoryField.baseFrameCheck] using checked

theorem check_sound (data : Capture) (ram initialization execution : List Source.MemoryField)
    (placement : Source.MemoryPlacement k) (nativeBank : WireBank k)
    (active allCoordinates : List (Fin n)) (inputBank : WireBank n) (fullBank : WireBank m)
    (activeBinding : data.activeMask = NumericQueryFrameChecks.coordinateMask (active.map Fin.val))
    (allBinding : data.allMask = NumericQueryFrameChecks.coordinateMask (allCoordinates.map Fin.val))
    (placementBinding : data.placement.toList = List.ofFn fun wire =>
      (inputBank.placement (nativeBank.address wire)).val)
    (nativeBinding : data.nativeAddress.toList = List.ofFn fun wire =>
      AddressUniqueChecks.addressCode (nativeBank.address wire))
    (inputBinding : data.inputAddress.toList = List.ofFn fun wire =>
      AddressUniqueChecks.addressCode (inputBank.address (inputBank.placement (nativeBank.address wire))))
    (fullBinding : data.fullAddress.toList = List.ofFn fun wire =>
      AddressUniqueChecks.addressCode (fullBank.address (fullBank.placement (nativeBank.address wire))))
    (ramBinding : data.ram = ram.map fun field => encode (field.polynomial placement))
    (initializationBinding : data.initialization = initialization.map fun field => encode (field.polynomial placement))
    (executionBinding : data.execution = execution.map fun field => encode (field.polynomial placement))
    (checked : check data = true) :
    ram.all (fun field => field.baseFrameCheck placement nativeBank active inputBank fullBank) = true ∧
      initialization.all (fun field => field.baseFrameCheck placement nativeBank allCoordinates inputBank fullBank) = true ∧
      execution.all (fun field => field.baseFrameCheck placement nativeBank allCoordinates inputBank fullBank) = true := by
  simp only [check, Bool.and_eq_true] at checked
  have ramChecked := checked.1.1.2
  have initializationChecked := checked.1.2
  have executionChecked := checked.2
  rw [ramBinding] at ramChecked
  rw [initializationBinding] at initializationChecked
  rw [executionBinding] at executionChecked
  exact ⟨fields_sound data data.activeMask ram placement nativeBank active inputBank fullBank activeBinding
      placementBinding nativeBinding inputBinding fullBinding checked.1.1.1 ramChecked,
    fields_sound data data.allMask initialization placement nativeBank allCoordinates inputBank fullBank allBinding
      placementBinding nativeBinding inputBinding fullBinding checked.1.1.1 initializationChecked,
    fields_sound data data.allMask execution placement nativeBank allCoordinates inputBank fullBank allBinding
      placementBinding nativeBinding inputBinding fullBinding checked.1.1.1 executionChecked⟩

theorem check_sound_of_binding (data : Capture) (ram initialization execution : List Source.MemoryField)
    (placement : Source.MemoryPlacement k) (nativeBank : WireBank k)
    (active allCoordinates : List (Fin n)) (inputBank : WireBank n) (fullBank : WireBank m)
    (binding : data = ofTyped ram initialization execution placement nativeBank active allCoordinates inputBank fullBank)
    (checked : check data = true) :
    ram.all (fun field => field.baseFrameCheck placement nativeBank active inputBank fullBank) = true ∧
      initialization.all (fun field => field.baseFrameCheck placement nativeBank allCoordinates inputBank fullBank) = true ∧
      execution.all (fun field => field.baseFrameCheck placement nativeBank allCoordinates inputBank fullBank) = true := by
  apply check_sound data ram initialization execution placement nativeBank active allCoordinates inputBank fullBank
  · simpa only [ofTyped] using congrArg Capture.activeMask binding
  · simpa only [ofTyped] using congrArg Capture.allMask binding
  · simpa only [ofTyped, LookupTable.toList_ofList] using congrArg (fun value => value.placement.toList) binding
  · simpa only [ofTyped, LookupTable.toList_ofList] using congrArg (fun value => value.nativeAddress.toList) binding
  · simpa only [ofTyped, LookupTable.toList_ofList] using congrArg (fun value => value.inputAddress.toList) binding
  · simpa only [ofTyped, LookupTable.toList_ofList] using congrArg (fun value => value.fullAddress.toList) binding
  · simpa only [ofTyped] using congrArg Capture.ram binding
  · simpa only [ofTyped] using congrArg Capture.initialization binding
  · simpa only [ofTyped] using congrArg Capture.execution binding
  · exact checked

end Airbender.Compiler.NumericMemoryFrameChecks
