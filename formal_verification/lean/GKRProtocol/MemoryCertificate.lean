import GKRProtocol.MemoryFingerprint
import GKRProtocol.NativeProduct
import GKRProtocol.LookupSourceSemantics

namespace Airbender.Compiler
set_option warningAsError true

def memoryLiftedRelations (relations : List (Polynomial n Source.BaseField)) :
    List (Polynomial (n + 7) Source.BaseField) :=
  relations.map (rename (fun index => index.castAdd 7))

/-- Only a copy-ideal witness is supplied by the synthesizer. The source row,
actual expanded native payload and both placements are separate inputs. -/
structure MemoryFingerprintCertificate (relations : List (Polynomial n Source.BaseField)) where
  witness : Combination (memoryLiftedRelations relations)

def MemoryFingerprintCertificate.agreement {relations : List (Polynomial n Source.BaseField)}
    (candidate : MemoryFingerprintCertificate relations) (row : Source.MemoryRow)
    (placement : Source.MemoryPlacement n) (bank : WireBank n)
    (expression : Expression (n + 7) Source.BaseField) : Agreement (memoryLiftedRelations relations) :=
  ⟨row.symbolicPolynomial placement (fun index => index.castAdd 7) (MemorySymbolPlacement.forBank bank),
    expression.polynomial, candidate.witness⟩

def MemoryFingerprintCertificate.check {relations : List (Polynomial n Source.BaseField)}
    (candidate : MemoryFingerprintCertificate relations) (row : Source.MemoryRow)
    (placement : Source.MemoryPlacement n) (bank : WireBank n) (payload : LookupPayload) : Bool :=
  match payload.memoryExpression (MemorySymbolPlacement.forBank bank) with
  | none => false
  | some expression => (candidate.agreement row placement bank expression).check

theorem MemoryFingerprintCertificate.sound [CommRing R]
    {relations : List (Polynomial n Source.BaseField)} (candidate : MemoryFingerprintCertificate relations)
    (row : Source.MemoryRow) (placement : Source.MemoryPlacement n) (bank : WireBank n)
    (payload : LookupPayload) (checked : candidate.check row placement bank payload = true)
    (inBank : bank.inputCheck payload.inputs = true) (typing : ConsumerTyping)
    (roles : payload.inputs.all (fun address => typing.compatible (address, .base)) = true)
    (assignment : TypedAssignment R) (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (copies : Satisfies relations (assignment.base ∘ bank.address)) :
    payload.interpret hom challenges (assignment.value typing hom) =
      row.fingerprint (placement.project (assignment.base ∘ bank.address)) hom challenges := by
  let symbols := memorySymbolValues bank assignment.base hom challenges
  have baseSymbols (index : Fin n) : symbols (index.castAdd 7) = hom ((assignment.base ∘ bank.address) index) :=
    memorySymbolValues_base bank assignment.base hom challenges index
  have powers := memorySymbolValues_power bank assignment.base hom challenges
  have gamma := memorySymbolValues_gamma bank assignment.base hom challenges
  cases reflected : payload.memoryExpression (MemorySymbolPlacement.forBank bank) with
  | none => simp [check, reflected] at checked
  | some expression =>
      have identity : (candidate.agreement row placement bank expression).check = true := by
        simpa only [check, reflected] using checked
      have holds : ∀ relation ∈ memoryLiftedRelations relations, evaluateHom hom symbols relation = 0 := by
        intro relation member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        rw [evaluateHom_rename]
        have same : symbols ∘ (fun index : Fin n => index.castAdd 7) =
            hom ∘ (assignment.base ∘ bank.address) := funext baseSymbols
        rw [same, evaluateHom_at_hom, copies original originalMember, map_zero]
      have equal := Agreement.sound_hom identity hom symbols holds
      change evaluateHom hom symbols (row.symbolicPolynomial placement (fun index => index.castAdd 7)
        (MemorySymbolPlacement.forBank bank)) = evaluateHom hom symbols expression.polynomial at equal
      rw [row.symbolicPolynomial_sound placement (fun index => index.castAdd 7)
        (MemorySymbolPlacement.forBank bank) hom challenges symbols (assignment.base ∘ bank.address)
        baseSymbols powers gamma, Expression.polynomial_valueHom] at equal
      exact (payload.memoryExpression_sound (MemorySymbolPlacement.forBank bank) reflected hom challenges
        symbols (assignment.value typing hom) powers gamma
        (memorySymbolValues_inputs bank typing assignment hom challenges payload.inputs inBank roles)).symm.trans equal.symm

theorem productRegistry_source_memory [CommRing R]
    {registry : List LookupPayload} {index : Nat} {leaf : LookupPayload}
    (found : registry[index]? = some leaf) (definitions : List AffineDefinition) (indices : List Nat)
    {payload : LookupPayload} (expanded : LookupPayload.expand definitions indices leaf = some payload)
    {relations : List (Polynomial n Source.BaseField)} (candidate : MemoryFingerprintCertificate relations)
    (row : Source.MemoryRow) (placement : Source.MemoryPlacement n) (bank : WireBank n)
    (checked : candidate.check row placement bank payload = true)
    (inBank : bank.inputCheck payload.inputs = true) (typing : ConsumerTyping)
    (roles : payload.inputs.all (fun address => typing.compatible (address, .base)) = true)
    (assignment : TypedAssignment R) (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (defined : ∀ definition ∈ definitions, definition.Holds hom challenges (assignment.value typing hom))
    (copies : Satisfies relations (assignment.base ∘ bank.address)) :
    productRegistryValue registry hom challenges (assignment.value typing hom) index =
      row.fingerprint (placement.project (assignment.base ∘ bank.address)) hom challenges :=
  (productRegistryValue_at found hom challenges (assignment.value typing hom)).trans
    ((LookupPayload.expand_sound hom challenges (assignment.value typing hom) defined expanded).symm.trans
      (candidate.sound row placement bank payload checked inBank typing roles assignment hom challenges copies))

/-- Occurrence correspondence permits a shared native primitive to account for
two equal source requests. The source label multiset must still be exact. -/
theorem memory_product_translation [CommMonoid R] (primitive : Nat → R)
    (source : List R) {native labels : List Nat}
    (fields : List.Forall₂ (fun index label => primitive index = (source[label]?).getD 1) native labels)
    (coverage : labels.Perm (List.range source.length)) :
    (native.map primitive).prod = source.prod := by
  have same : native.map primitive = labels.map (fun index => (source[index]?).getD 1) := by
    clear coverage
    induction fields with
    | nil => rfl
    | cons head tail proof => exact congrArg₂ List.cons head proof
  rw [same, (coverage.map (fun index => (source[index]?).getD 1)).prod_eq, List.map_range_getD]

theorem MemoryFieldAgreement.mask_value [CommRing R]
    {relations : List (Polynomial n Source.BaseField)} {field : MemoryFieldAgreement relations}
    (placement : Source.MemoryPlacement n) (bank : WireBank n) (address : GKRAddress)
    (target : field.lowered = Expression.atom (bank.placement address))
    (checked : field.check placement = true) (inBank : bank.inputCheck [address] = true)
    (typing : ConsumerTyping) (role : typing.compatible (address, .base) = true)
    (assignment : TypedAssignment R) (hom : Source.BaseField →+* R)
    (copies : Satisfies relations (assignment.base ∘ bank.address)) :
    assignment.value typing hom address = hom (field.source.value (placement.project (assignment.base ∘ bank.address))) := by
  have same := field.sound placement checked copies
  rw [target] at same
  change field.source.value (placement.project (assignment.base ∘ bank.address)) =
    assignment.base (bank.address (bank.placement address)) at same
  have roundTrip := (addressEqual_iff _ _).mp (List.all_eq_true.mp inBank address List.mem_cons_self)
  rw [roundTrip] at same
  exact (assignment.value_base typing hom role).trans (congrArg hom same.symm)

end Airbender.Compiler
