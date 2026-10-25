import GKRProtocol.CanonicalSource
import GKRProtocol.OracleFrame

namespace Airbender.Compiler
set_option warningAsError true

/-- RAM source ports do not consume generic or scalar lookup setup columns. -/
def lookupOracleIndependent : GKRAddress → Bool
  | .Setup _ | .VirtualSetup .RangeCheck16Bits | .VirtualSetup .RangeCheckTimestamp => false
  | _ => true

theorem MaterializedLookupSetup.baseOracle_frame (model : MaterializedLookupSetup width)
    (row : Fin model.imported.data.length) (fallback : GKRAddress → Source.BaseField)
    (address : GKRAddress) (independent : lookupOracleIndependent address = true) :
    model.baseOracle row fallback address = fallback address := by
  cases address with
  | Setup _ => simp [lookupOracleIndependent] at independent
  | VirtualSetup kind => cases kind <;> simp_all [lookupOracleIndependent, baseOracle]
  | _ => rfl

/-- Each source port is either a preserved finite input coordinate or an
external address outside the arithmetic bank. A placement fallback is never
accepted as evidence that an external address belongs to the finite bank. -/
def sourcePortFrameCheck (coordinates : List (Fin n)) (inputBank : WireBank n)
    (fullBank : WireBank m) (address : GKRAddress) : Bool :=
  if addressEqual (inputBank.address (inputBank.placement address)) address then
    !coordinates.contains (inputBank.placement address)
  else
    !(addressEqual (fullBank.address (fullBank.placement address)) address) &&
      lookupOracleIndependent address

theorem source_port_frame (coordinates : List (Fin n)) (inputBank : WireBank n)
    (fullBank : WireBank m) (model : MaterializedLookupSetup width)
    (row : Fin model.imported.data.length) (fallback : GKRAddress → Source.BaseField)
    (before after : Fin n → Source.BaseField) (base : GKRAddress → Source.BaseField)
    (inputAgreement : ∀ index, base (inputBank.address index) = after index)
    (externalAgreement : ∀ address,
      addressEqual (fullBank.address (fullBank.placement address)) address = false →
        base address = model.baseOracle row fallback address)
    (finiteFrame : ∀ index, index ∉ coordinates → after index = before index)
    (address : GKRAddress) (checked : sourcePortFrameCheck coordinates inputBank fullBank address = true) :
    base address = inputBank.materialize before fallback address := by
  by_cases input : addressEqual (inputBank.address (inputBank.placement address)) address = true
  · have outside : inputBank.placement address ∉ coordinates := by
      simpa [sourcePortFrameCheck, input] using checked
    have same := (addressEqual_iff _ _).mp input
    have actual := inputAgreement (inputBank.placement address)
    rw [same] at actual
    rw [actual, finiteFrame _ outside]
    simp only [WireBank.materialize, input, ↓reduceIte]
  · have clauses : addressEqual (fullBank.address (fullBank.placement address)) address = false ∧
        lookupOracleIndependent address = true := by
      simpa [sourcePortFrameCheck, input] using checked
    rw [externalAgreement address clauses.1, model.baseOracle_frame row fallback address clauses.2]
    simp only [WireBank.materialize, if_neg input]

def Source.MemoryField.baseFrameCheck (field : Source.MemoryField)
    (placement : Source.MemoryPlacement k) (nativeBank : WireBank k)
    (coordinates : List (Fin n)) (inputBank : WireBank n) (fullBank : WireBank m) : Bool :=
  (field.polynomial placement).all (fun term => term.2.all (fun wire =>
    sourcePortFrameCheck coordinates inputBank fullBank (nativeBank.address wire)))

theorem Source.MemoryField.base_frame_value (field : Source.MemoryField)
    (placement : Source.MemoryPlacement k) (nativeBank : WireBank k)
    (coordinates : List (Fin n)) (inputBank : WireBank n) (fullBank : WireBank m)
    (checked : field.baseFrameCheck placement nativeBank coordinates inputBank fullBank = true)
    (model : MaterializedLookupSetup width) (row : Fin model.imported.data.length)
    (fallback : GKRAddress → Source.BaseField) (before after : Fin n → Source.BaseField)
    (base : GKRAddress → Source.BaseField)
    (inputAgreement : ∀ index, base (inputBank.address index) = after index)
    (externalAgreement : ∀ address,
      addressEqual (fullBank.address (fullBank.placement address)) address = false →
        base address = model.baseOracle row fallback address)
    (finiteFrame : ∀ index, index ∉ coordinates → after index = before index) :
    field.value (placement.project (base ∘ nativeBank.address)) =
      field.value (placement.project ((inputBank.materialize before fallback) ∘ nativeBank.address)) := by
  rw [← field.polynomial_value, ← field.polynomial_value]
  apply evaluate_congr_on
  intro term member wire included
  exact source_port_frame coordinates inputBank fullBank model row fallback before after base
    inputAgreement externalAgreement finiteFrame (nativeBank.address wire)
    (List.all_eq_true.mp (List.all_eq_true.mp checked term member) wire included)

theorem Source.MemoryRow.fingerprint_congr {R : Type} [CommRing R]
    (row : Source.MemoryRow) (before after : Source.MemoryValues)
    (same : ∀ field ∈ row.fields, field.value before = field.value after)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) :
    row.fingerprint before hom challenges = row.fingerprint after hom challenges := by
  unfold fingerprint
  rw [same row.addressSpace (by simp [fields]), same row.address.low (by simp [fields]),
    same row.address.high (by simp [fields]), same row.timestamp.low (by simp [fields]),
    same row.timestamp.high (by simp [fields]), same row.data.low (by simp [fields]),
    same row.data.high (by simp [fields])]

end Airbender.Compiler
