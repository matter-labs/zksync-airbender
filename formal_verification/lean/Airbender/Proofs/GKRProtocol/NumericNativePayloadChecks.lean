import Airbender.Proofs.GKRProtocol.HelperCertificate
import Airbender.Proofs.GKRProtocol.MemoryCertificate
import Airbender.Proofs.GKRProtocol.NumericFunctionalBaseChecks

namespace Airbender.Compiler.NumericNativePayloadChecks
set_option warningAsError true
open NumericFunctionalBaseChecks

theorem all_and (items : List α) (left right : α → Bool) :
    items.all (fun item => left item && right item) = (items.all left && items.all right) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.all_cons, ih, Bool.and_assoc, Bool.and_left_comm]


theorem checked_at [NeZero p] (source : Typed n p) (data : List Data) (index : Nat)
    (binding : (data.drop index).take 1 = [encode source])
    (checked : NumericFunctionalBaseChecks.check p data = true) : source.check = true := by
  have windowMember : encode source ∈ (data.drop index).take 1 := by
    rw [binding]
    exact List.mem_singleton_self _
  have member := List.mem_of_mem_drop (List.mem_of_mem_take windowMember)
  have valid := List.all_eq_true.mp checked (encode source) member
  exact (entry_encode source).symm.trans valid

def ofHelper {relations : List (Polynomial n Source.BaseField)} {recipe : NativeBaseRecipe}
    (candidate : HelperAgreement relations recipe) (placement : Source.HelperPlacement n)
    (bank : WireBank n) (typing : ConsumerTyping) : Typed n babyBearModulus :=
  let original := candidate.agreement placement bank
  ⟨recipe.inputs.map (fun address =>
      ⟨address, bank.address (bank.placement address), typing.compatible (address, .base)⟩),
    original.source, add original.lowered (combination relations original.witness)⟩

theorem ofHelper_check {relations : List (Polynomial n Source.BaseField)} {recipe : NativeBaseRecipe}
    (candidate : HelperAgreement relations recipe) (placement : Source.HelperPlacement n)
    (bank : WireBank n) (typing : ConsumerTyping) :
    (ofHelper candidate placement bank typing).check =
      (bank.check recipe && (NativeLookupEncoding.scalar recipe).baseCheck typing &&
        candidate.check placement bank) := by
  simp only [ofHelper, Typed.check, List.all_map, Function.comp_def, TypedPort.check,
    all_and, WireBank.check, NativeLookupEncoding.baseCheck, NativeLookupEncoding.columns,
    List.all_cons, List.all_nil, Bool.and_true, HelperAgreement.check,
    Agreement.check, Bool.and_assoc]

def ofMemory {relations : List (Polynomial n Source.BaseField)}
    (candidate : MemoryFingerprintCertificate relations) (row : Source.MemoryRow)
    (placement : Source.MemoryPlacement n) (bank : WireBank n) (payload : LookupPayload)
    (typing : ConsumerTyping) : Typed (n + 7) babyBearModulus :=
  match payload.memoryExpression (MemorySymbolPlacement.forBank bank) with
  | none => ⟨[⟨.BaseLayerWitness 0, .BaseLayerWitness 0, false⟩], [], []⟩
  | some expression =>
      let original := candidate.agreement row placement bank expression
      ⟨payload.inputs.map (fun address =>
          ⟨address, bank.address (bank.placement address), typing.compatible (address, .base)⟩),
        original.source, add original.lowered (combination (memoryLiftedRelations relations) original.witness)⟩

theorem ofMemory_check {relations : List (Polynomial n Source.BaseField)}
    (candidate : MemoryFingerprintCertificate relations) (row : Source.MemoryRow)
    (placement : Source.MemoryPlacement n) (bank : WireBank n) (payload : LookupPayload)
    (typing : ConsumerTyping) :
    (ofMemory candidate row placement bank payload typing).check =
      (bank.inputCheck payload.inputs &&
        payload.inputs.all (fun address => typing.compatible (address, .base)) &&
        candidate.check row placement bank payload) := by
  cases reflected : payload.memoryExpression (MemorySymbolPlacement.forBank bank) with
  | none => simp only [ofMemory, MemoryFingerprintCertificate.check, reflected,
      Typed.check, List.all_cons, List.all_nil, TypedPort.check, Bool.and_false,
      Bool.false_and, Bool.and_true]
  | some expression =>
      simp only [ofMemory, MemoryFingerprintCertificate.check, reflected, Typed.check,
        List.all_map, Function.comp_def, TypedPort.check, all_and, WireBank.inputCheck,
        Agreement.check, Bool.and_assoc]

end Airbender.Compiler.NumericNativePayloadChecks
