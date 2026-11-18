module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.NumericArithmeticOperations
public import Proven.GKRProtocol.NumericLookupTable
public import Proven.GKRProtocol.FullArithmeticChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.NumericArithmeticChecks
open NumericPolynomialChecks

structure Capture (inputs : Nat) where
  sourceRows : LookupTable Data
  normalizedSourceRows : LookupTable Data
  lowerRows : LookupTable Data
  computedRows : LookupTable Data
  backwardRows : LookupTable (List (Data × Nat))
  forwardRows : LookupTable (List (Data × Nat))
  gateInputs : LookupTable Data
  gateOutputs : LookupTable Data
  sortedAddressKeys : List Nat

def Capture.extension (p : Nat) (data : Capture inputs) : Nat → Data :=
  initial p inputs (fun index => data.computedRows.getD index [])

def combine (p : Nat) (relations : LookupTable Data) (terms : List (Data × Nat)) : Data :=
  terms.foldr (fun term result => fastMultiply p term.1 (relations.getD term.2 []) ++ result) []

theorem combine_eq (p : Nat) (relations : LookupTable Data) (checked : relations.valid = true)
    (terms : List (Data × Nat)) :
    combine p relations terms = NumericPolynomialChecks.combination p relations.toList terms := by
  simp only [combine, NumericPolynomialChecks.combination, fastMultiply_eq, LookupTable.getD_eq _ checked]

/-- Reuse a bound normal form for a unit certificate row. -/
def forwardEqual (p : Nat) (data : Capture inputs) (polynomial : Data) (terms : List (Data × Nat)) : Bool :=
  match terms with
  | [(factor, index)] =>
      if isUnit factor && canonical p (data.sourceRows.getD index []) then
        NumericPolynomialChecks.normalize p polynomial == data.normalizedSourceRows.getD index []
      else fastEqual p polynomial (combine p data.sourceRows terms)
  | _ => fastEqual p polynomial (combine p data.sourceRows terms)

theorem forwardEqual_eq (p : Nat) (data : Capture inputs)
    (normalized : ∀ index, data.normalizedSourceRows.getD index [] =
      NumericPolynomialChecks.normalize p (data.sourceRows.getD index []))
    (polynomial : Data) (terms : List (Data × Nat)) :
    forwardEqual p data polynomial terms = NumericPolynomialChecks.equal p polynomial (combine p data.sourceRows terms) := by
  cases terms with
  | nil => exact fastEqual_eq ..
  | cons term rest =>
      cases rest with
      | cons next tail => exact fastEqual_eq ..
      | nil =>
          rcases term with ⟨factor, index⟩
          simp only [forwardEqual]
          split_ifs with checked
          · have product : fastMultiply p factor (data.sourceRows.getD index []) = data.sourceRows.getD index [] := by
              unfold fastMultiply
              rw [ite_eq_left checked]
            simp only [combine, List.foldr_cons, List.foldr_nil, product, List.append_nil]
            rw [normalized]
            rfl
          · exact fastEqual_eq ..

def translationCheck (p : Nat) (data : Capture inputs) : Bool :=
  (List.range data.sourceRows.size).all (fun index => data.normalizedSourceRows.getD index [] ==
    NumericPolynomialChecks.normalize p (combine p data.lowerRows (data.backwardRows.getD index []))) &&
  (List.range data.lowerRows.size).all (fun index => forwardEqual p data
    (fastSubstitute p inputs (fun index => data.computedRows.getD index []) (data.lowerRows.getD index []))
    (data.forwardRows.getD index []))

def gateCheck (data : Capture inputs) : Bool :=
  (List.range data.gateInputs.size).all fun index =>
    data.gateInputs.getD index [] == data.gateOutputs.getD index []

def layoutCheck (data : Capture inputs) : Bool :=
  data.sourceRows.valid && data.normalizedSourceRows.valid && data.lowerRows.valid && data.computedRows.valid &&
    data.backwardRows.valid && data.forwardRows.valid && data.gateInputs.valid && data.gateOutputs.valid

structure Layout (data : Capture inputs) : Prop where
  sourceRows : data.sourceRows.valid = true
  normalizedSourceRows : data.normalizedSourceRows.valid = true
  lowerRows : data.lowerRows.valid = true
  computedRows : data.computedRows.valid = true
  backwardRows : data.backwardRows.valid = true
  forwardRows : data.forwardRows.valid = true
  gateInputs : data.gateInputs.valid = true
  gateOutputs : data.gateOutputs.valid = true

theorem layout_sound (data : Capture inputs) (checked : layoutCheck data = true) : Layout data := by
  simp only [layoutCheck, Bool.and_eq_true] at checked
  rcases checked with ⟨⟨⟨⟨⟨⟨⟨first, second⟩, third⟩, fourth⟩, fifth⟩, sixth⟩, seventh⟩, eighth⟩
  exact ⟨first, second, third, fourth, fifth, sixth, seventh, eighth⟩

/-- One result checks the complete layout, address keys and arithmetic capture. -/
def check (p : Nat) (data : Capture inputs) : Bool :=
  layoutCheck data && AddressUniqueChecks.ascending data.sortedAddressKeys &&
    translationCheck p data && gateCheck data

def gateInput (gate : ArithmeticGate m (ZMod p)) : Polynomial m (ZMod p) :=
  match gate with
  | .assertZero input _ | .define _ input _ => input.polynomial
  | .copy _ _ => []

def gateOutput (gate : ArithmeticGate m (ZMod p)) : Polynomial m (ZMod p) :=
  match gate with
  | .assertZero _ output | .define _ _ output => output.polynomial
  | .copy _ _ => []

theorem gate_check_eq [NeZero p] (gate : ArithmeticGate m (ZMod p)) :
    (encode (Airbender.Compiler.normalize (gateInput gate)) ==
      encode (Airbender.Compiler.normalize (gateOutput gate))) = gate.check := by
  cases gate with
  | assertZero input output =>
      apply Bool.eq_iff_iff.mpr
      simp only [gateInput, gateOutput, ArithmeticGate.check, Airbender.Compiler.equal,
        beq_iff_eq, decide_eq_true_eq, encode_injective.eq_iff]
  | define output input expression =>
      apply Bool.eq_iff_iff.mpr
      simp only [gateInput, gateOutput, ArithmeticGate.check, Airbender.Compiler.equal,
        beq_iff_eq, decide_eq_true_eq, encode_injective.eq_iff]
  | copy _ _ => rfl

structure Bindings (addresses : List GKRAddress) (artifact : ArithmeticExtension n m (ZMod p))
    (certificate : Certificate artifact.translation) (data : Capture n) : Prop where
  sourceRows : artifact.translation.source.map encode = data.sourceRows.toList
  normalizedSourceRows : artifact.translation.source.map (fun polynomial =>
    NumericPolynomialChecks.normalize p (encode polynomial)) = data.normalizedSourceRows.toList
  lowerRows : artifact.translation.lowered.map encode = data.lowerRows.toList
  projection : ∀ wire, (artifact.projection wire).val = wire.val
  extension : ∀ wire, encode (artifact.extension wire) = data.extension p wire.val
  backward : ∀ index, encodeCombination (certificate.backward index) = data.backwardRows.getD index.val []
  forward : ∀ index, encodeCombination (certificate.forward index) = data.forwardRows.getD index.val []
  gateInputs : artifact.gates.map (fun gate => encode (Airbender.Compiler.normalize (gateInput gate))) = data.gateInputs.toList
  gateOutputs : artifact.gates.map (fun gate => encode (Airbender.Compiler.normalize (gateOutput gate))) = data.gateOutputs.toList
  addressKeys : (addresses.map AddressUniqueChecks.addressCode).insertionSort (fun a b => a ≤ b) =
    data.sortedAddressKeys

theorem mapped_size (original : List α) (f : α → β) (table : LookupTable β)
    (checked : table.valid = true) (binding : original.map f = table.toList) :
    table.size = original.length := by
  rw [LookupTable.size_eq_length table checked, ← binding, List.length_map]

theorem mapped_getD (original : List α) (f : α → β) (table : LookupTable β)
    (checked : table.valid = true) (binding : original.map f = table.toList)
    (index : Fin original.length) (fallback : β) :
    table.getD index.val fallback = f (original.get index) := by
  rw [LookupTable.getD_eq table checked, ← binding]
  simp only [List.getElem?_map, List.getElem?_eq_getElem index.isLt, Option.map_some,
    Option.getD_some, List.get_eq_getElem]

theorem vector_getD (original : Vector α count) (f : α → β) (table : LookupTable β)
    (checked : table.valid = true) (binding : original.toList.map f = table.toList)
    (index : Fin count) (fallback : β) :
    table.getD index.val fallback = f original[index] := by
  rw [LookupTable.getD_eq table checked, ← binding]
  simp only [List.getElem?_map, Vector.getElem?_toList,
    Vector.getElem?_eq_getElem index.isLt, Option.map_some, Option.getD_some]
  rfl

theorem initial_extension (bound : n ≤ m) (original : Vector (Polynomial n (ZMod p)) (m - n))
    (table : LookupTable Data) (checked : table.valid = true)
    (binding : original.toList.map encode = table.toList) (wire : Fin m) :
    encode (initialExtension bound (fun index => original[index]) wire) =
      initial p n (fun index => table.getD index []) wire.val := by
  unfold initialExtension initial
  split_ifs with inside
  · exact encode_atom _
  · exact (vector_getD original encode table checked binding ⟨wire.val - n, by omega⟩ []).symm
theorem map_encode_normalize [NeZero p] (items : List α) (f : α → Polynomial m (ZMod p)) :
    items.map (fun item => encode (Airbender.Compiler.normalize (f item))) =
      items.map (fun item => NumericPolynomialChecks.normalize p (encode (f item))) := by
  apply List.map_congr_left
  intro item _
  exact encode_normalize _

theorem encode_rename_prefix (placement : Fin n → Fin m)
    (placementPrefix : ∀ wire, (placement wire).val = wire.val) (polynomial : Polynomial n (ZMod p)) :
    encode (Airbender.Compiler.rename placement polynomial) = encode polynomial := by
  rw [encode_rename placement id (fun wire => (placementPrefix wire).symm)]
  simp [NumericPolynomialChecks.rename]

theorem normalized_getD (addresses : List GKRAddress) (artifact : ArithmeticExtension n m (ZMod p))
    (certificate : Certificate artifact.translation) (data : Capture n)
    (binding : Bindings addresses artifact certificate data) (layout : Layout data) (index : Nat) :
    data.normalizedSourceRows.getD index [] = NumericPolynomialChecks.normalize p (data.sourceRows.getD index []) := by
  have mapped : data.sourceRows.toList.map (NumericPolynomialChecks.normalize p) = data.normalizedSourceRows.toList := by
    rw [← binding.sourceRows, List.map_map]
    exact binding.normalizedSourceRows
  rw [LookupTable.getD_eq _ layout.normalizedSourceRows, ← mapped, List.getElem?_map,
    LookupTable.getD_eq _ layout.sourceRows]
  cases data.sourceRows.toList[index]? <;> rfl

theorem translation_valid [NeZero p] (addresses : List GKRAddress)
    (artifact : ArithmeticExtension n m (ZMod p)) (certificate : Certificate artifact.translation)
    (data : Capture n) (binding : Bindings addresses artifact certificate data)
    (layout : Layout data) (checked : translationCheck p data = true) : certificate.Valid := by
  simp only [translationCheck, Bool.and_eq_true] at checked
  have sourceSize := mapped_size _ encode _ layout.sourceRows binding.sourceRows
  have lowerSize := mapped_size _ encode _ layout.lowerRows binding.lowerRows
  refine ⟨?_, ?_, ?_⟩
  · intro wire
    have same : encode (artifact.extension (artifact.projection wire)) = encode (atom (F := ZMod p) wire) := by
      rw [binding.extension, binding.projection, Capture.extension, initial, ite_eq_left wire.isLt, encode_atom]
    rw [← equal_encode]
    change NumericPolynomialChecks.equal p (encode (artifact.extension (artifact.projection wire)))
      (encode (atom (F := ZMod p) wire)) = true
    rw [same]
    simp only [NumericPolynomialChecks.equal, beq_self_eq_true]
  · intro index
    have inside : index.val < data.sourceRows.size := by rw [sourceSize]; exact index.isLt
    have row := List.all_eq_true.mp checked.1 index.val (List.mem_range.mpr inside)
    have left : data.normalizedSourceRows.getD index.val [] =
        NumericPolynomialChecks.normalize p (encode (Airbender.Compiler.rename artifact.translation.projection
          (artifact.translation.source.get index))) := by
      rw [mapped_getD _ _ _ layout.normalizedSourceRows binding.normalizedSourceRows index []]
      exact congrArg (NumericPolynomialChecks.normalize p)
        (encode_rename_prefix artifact.translation.projection (fun wire => binding.projection wire) _).symm
    have right : combine p data.lowerRows (data.backwardRows.getD index.val []) =
        encode (Airbender.Compiler.combination artifact.translation.lowered (certificate.backward index)) := by
      rw [combine_eq _ _ layout.lowerRows, ← binding.backward, ← binding.lowerRows, ← encode_combination]
    rw [left, right] at row
    change NumericPolynomialChecks.equal p _ _ = true at row
    rw [equal_encode] at row
    exact row
  · intro index
    have inside : index.val < data.lowerRows.size := by rw [lowerSize]; exact index.isLt
    have row := List.all_eq_true.mp checked.2 index.val (List.mem_range.mpr inside)
    rw [forwardEqual_eq _ _ (normalized_getD addresses artifact certificate data binding layout)] at row
    have left : fastSubstitute p n (fun coordinate => data.computedRows.getD coordinate [])
        (data.lowerRows.getD index.val []) =
        encode (Airbender.Compiler.substitute artifact.translation.extension (artifact.translation.lowered.get index)) := by
      rw [fastSubstitute_eq, mapped_getD _ encode _ layout.lowerRows binding.lowerRows index []]
      exact (encode_substitute _ (data.extension p) (fun wire => (binding.extension wire).symm) _).symm
    have right : combine p data.sourceRows (data.forwardRows.getD index.val []) =
        encode (Airbender.Compiler.combination artifact.translation.source (certificate.forward index)) := by
      rw [combine_eq _ _ layout.sourceRows, ← binding.forward, ← binding.sourceRows, ← encode_combination]
    rw [left, right, equal_encode] at row
    exact row

theorem gates_checked [NeZero p] (addresses : List GKRAddress)
    (artifact : ArithmeticExtension n m (ZMod p)) (certificate : Certificate artifact.translation)
    (data : Capture n) (binding : Bindings addresses artifact certificate data)
    (layout : Layout data) (checked : gateCheck data = true) :
    artifact.gates.all ArithmeticGate.check = true := by
  have size := mapped_size _ (fun gate => encode (Airbender.Compiler.normalize (gateInput gate))) _ layout.gateInputs binding.gateInputs
  apply List.all_eq_true.mpr
  intro gate member
  obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
  have inside : index.val < data.gateInputs.size := by rw [size]; exact index.isLt
  have row := List.all_eq_true.mp checked index.val (List.mem_range.mpr inside)
  change (data.gateInputs.getD index.val [] == data.gateOutputs.getD index.val []) = true at row
  rw [mapped_getD _ _ _ layout.gateInputs binding.gateInputs index [],
    mapped_getD _ _ _ layout.gateOutputs binding.gateOutputs index [], gate_check_eq] at row
  exact row

theorem check_sound [NeZero p] (addresses : List GKRAddress)
    (artifact : ArithmeticExtension n m (ZMod p)) (certificate : Certificate artifact.translation)
    (data : Capture n) (binding : Bindings addresses artifact certificate data)
    (checked : check p data = true) :
    addresses.Nodup ∧ certificate.Valid ∧ artifact.gates.all ArithmeticGate.check = true := by
  simp only [check, Bool.and_eq_true] at checked
  have layout := layout_sound data checked.1.1.1
  refine ⟨?_, translation_valid addresses artifact certificate data binding layout checked.1.2,
    gates_checked addresses artifact certificate data binding layout checked.2⟩
  apply AddressUniqueChecks.check_sound
  simpa only [AddressUniqueChecks.check, binding.addressKeys] using checked.1.1.2

/-- Preserve the original complete Boolean statement without repeating its reductions. -/
theorem full_check [NeZero p] (addresses : List GKRAddress)
    (artifact : ArithmeticExtension n m (ZMod p)) (certificate : Certificate artifact.translation)
    (data : Capture n) (binding : Bindings addresses artifact certificate data)
    (checked : check p data = true) : FullArithmeticChecks.check addresses artifact certificate = true := by
  have facts := check_sound addresses artifact certificate data binding checked
  have original : Airbender.Compiler.check artifact.translation certificate = true := by
    simp only [Airbender.Compiler.check, Bool.and_eq_true]
    exact ⟨⟨List.all_eq_true.mpr (fun index _ => facts.2.1.1 index),
      List.all_eq_true.mpr (fun index _ => facts.2.1.2.1 index)⟩,
      List.all_eq_true.mpr (fun index _ => facts.2.1.2.2 index)⟩
  have keys : AddressUniqueChecks.check addresses = true := by
    simp only [check, Bool.and_eq_true] at checked
    simpa only [AddressUniqueChecks.check, binding.addressKeys] using checked.1.1.2
  simp only [FullArithmeticChecks.check, FullArithmeticChecks.translationCheck_eq, keys, original,
    facts.2.2, Bool.and_self]

end Airbender.Compiler.NumericArithmeticChecks
