import GKRProtocol.Source

namespace Airbender.Compiler.Source
set_option warningAsError true

def LookupInput.polynomial (placement : Nat → Fin n) : LookupInput → Compiler.Polynomial n BaseField
  | .Variable index => Compiler.atom (placement index)
  | .Expression terms constant => (coefficientValue constant, []) ::
      terms.toList.map (fun (coefficient, index) => (coefficientValue coefficient, [placement index]))

theorem LookupInput.polynomial_value (placement : Nat → Fin n) (values : Fin n → BaseField)
    (input : LookupInput) :
    Compiler.evaluate values (input.polynomial placement) = input.value (values ∘ placement) := by
  cases input with
  | Variable index => simp [polynomial, value]
  | Expression terms constant =>
    simp [polynomial, value, Compiler.evaluate, Compiler.monomialValue, List.map_map, Function.comp_def]

def LookupTable.polynomial (placement : Nat → Fin n) : LookupTable → Compiler.Polynomial n BaseField
  | .Variable index => Compiler.atom (placement index)
  | .Constant table => Compiler.constant table.id
  | .Expression expression => expression.polynomial placement

theorem LookupTable.polynomial_value (placement : Nat → Fin n) (values : Fin n → BaseField)
    (table : LookupTable) :
    Compiler.evaluate values (table.polynomial placement) = table.value (values ∘ placement) := by
  cases table with
  | Variable index => simp [polynomial, value]
  | Constant table => simp [polynomial, value]
  | Expression expression => exact expression.polynomial_value placement values

/-- Authored source fields, with explicit table selectors, decoder-mask packing
and zero padding. None of these fields are obtained from lowered equations. -/
inductive EncodedField where
  | input : LookupInput → EncodedField
  | table : LookupTable → EncodedField
  | familyMask : List Nat → EncodedField
  | zero

def EncodedField.value (values : Nat → BaseField) : EncodedField → BaseField
  | .input expression => expression.value values
  | .table selection => selection.value values
  | .familyMask bits => (bits.zipIdx.map (fun (wire, index) => (2 ^ index : BaseField) * values wire)).sum
  | .zero => 0

def EncodedField.polynomial (placement : Nat → Fin n) : EncodedField → Compiler.Polynomial n BaseField
  | .input expression => expression.polynomial placement
  | .table selection => selection.polynomial placement
  | .familyMask bits => bits.zipIdx.map (fun (wire, index) => ((2 ^ index : BaseField), [placement wire]))
  | .zero => []

theorem EncodedField.polynomial_value (placement : Nat → Fin n) (values : Fin n → BaseField)
    (field : EncodedField) :
    Compiler.evaluate values (field.polynomial placement) = field.value (values ∘ placement) := by
  cases field with
  | input expression => exact expression.polynomial_value placement values
  | table selection => exact selection.polynomial_value placement values
  | familyMask bits =>
    simp [polynomial, value, Compiler.evaluate, Compiler.monomialValue, List.map_map, Function.comp_def]
  | zero => rfl

def encodeFields (width : Nat) (includeTable : Bool) (row : List EncodedField)
    (table : LookupTable) : List EncodedField :=
  row ++ List.replicate (width - (if includeTable then 1 else 0) - row.length) .zero ++
    (if includeTable then [.table table] else [])

def queryFields (width : Nat) (includeTable : Bool) (query : Lookup) : List EncodedField :=
  encodeFields width includeTable (query.row.toList.map .input) query.table

def decoderFields (executor : Executor) (bits : List Nat) : List EncodedField :=
  ((executor.cycle_start_state.pc.values.toList ++
    [executor.decoder_data.rs1_index, executor.decoder_data.rs2_index, executor.decoder_data.rd_index] ++
    executor.decoder_data.imm.values.toList ++ executor.decoder_data.funct3.toList).map
      (fun index => .input (.Variable index))) ++
    (if bits.isEmpty then [] else [.familyMask bits])

def decoderEncodedFields (width : Nat) (includeTable : Bool)
    (executor : Executor) (bits : List Nat) : List EncodedField :=
  .input (.Variable executor.execute) ::
    encodeFields width includeTable (decoderFields executor bits) (.Constant .Decoder)

private def zeroInput : LookupInput := .Expression #[] ⟨⟨0, by decide⟩⟩

/-- Pair byte checks without losing a final odd request; its partner is the
explicit zero byte. Native column padding must agree with this value. -/
def pairByteChecks : List LookupInput → List Lookup
  | [] => []
  | [last] => [⟨#[last, zeroInput], .Constant .RangeCheck8x8⟩]
  | first :: second :: rest => ⟨#[first, second], .Constant .RangeCheck8x8⟩ :: pairByteChecks rest

def genericRequests (source : SemanticInputs) : List Lookup :=
  pairByteChecks ((source.range_checks.toList.filter (fun query => query.width == 8)).map (·.input)) ++
    source.lookups.toList

def range16Requests (source : SemanticInputs) : List LookupInput :=
  (source.range_checks.toList.filter (fun query => query.width == 16)).map (·.input)

end Airbender.Compiler.Source
