module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.NumericNativePayloadChecks
public import Proven.GKRProtocol.NumericLookupSourceChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.NumericMemoryPayloadChecks
open NumericFunctionalBaseChecks

def ofInputs (bank : WireBank n) (typing : ConsumerTyping) (inputs : List GKRAddress) :
    Typed 0 babyBearModulus :=
  ⟨inputs.map (fun address =>
      ⟨address, bank.address (bank.placement address), typing.compatible (address, .base)⟩), [], []⟩

def inputPortCode (bank : WireBank n) (typing : ConsumerTyping) (address : GKRAddress) : Nat × Nat × Nat :=
  encodePort ⟨address, bank.address (bank.placement address), typing.compatible (address, .base)⟩

theorem encode_inputs (bank : WireBank n) (typing : ConsumerTyping) (inputs : List GKRAddress) :
    encode (ofInputs bank typing inputs) = ⟨inputs.map (inputPortCode bank typing), [], []⟩ := by
  simp only [encode, ofInputs, List.map_map, Function.comp_def]
  rfl

theorem ofInputs_check (bank : WireBank n) (typing : ConsumerTyping) (inputs : List GKRAddress) :
    (ofInputs bank typing inputs).check =
      (bank.inputCheck inputs && inputs.all (fun address => typing.compatible (address, .base))) := by
  simp only [ofInputs, Typed.check, List.all_map, Function.comp_def, TypedPort.check,
    NumericNativePayloadChecks.all_and, WireBank.inputCheck]
  have empty : equal ([] : Polynomial 0 Source.BaseField) [] = true := by rfl
  simp only [empty, Bool.and_true]

def ofField {relations : List (Polynomial n Source.BaseField)}
    (field : MemoryFieldAgreement relations) (placement : Source.MemoryPlacement n)
    (bank : WireBank n) (typing : ConsumerTyping) (inputs : List GKRAddress) :
    Typed n babyBearModulus :=
  let original := field.agreement placement
  ⟨inputs.map (fun address =>
      ⟨address, bank.address (bank.placement address), typing.compatible (address, .base)⟩),
    original.source, add original.lowered (combination relations original.witness)⟩

theorem ofField_check {relations : List (Polynomial n Source.BaseField)}
    (field : MemoryFieldAgreement relations) (placement : Source.MemoryPlacement n)
    (bank : WireBank n) (typing : ConsumerTyping) (inputs : List GKRAddress) :
    (ofField field placement bank typing inputs).check =
      (bank.inputCheck inputs && inputs.all (fun address => typing.compatible (address, .base)) &&
        field.check placement) := by
  simp only [ofField, Typed.check, List.all_map, Function.comp_def, TypedPort.check,
    NumericNativePayloadChecks.all_and, WireBank.inputCheck, MemoryFieldAgreement.check,
    Agreement.check, Bool.and_assoc]

end Airbender.Compiler.NumericMemoryPayloadChecks
