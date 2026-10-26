import Airbender.Proofs.GKRProtocol.SourceFields
import Airbender.Proofs.GKRProtocol.Agreement

namespace Airbender.Compiler
set_option warningAsError true

structure LookupFieldAgreement (relations : List (Polynomial n Source.BaseField)) where
  source : Source.EncodedField
  lowered : Expression n Source.BaseField
  witness : Combination relations

def LookupFieldAgreement.agreement {relations : List (Polynomial n Source.BaseField)}
    (placement : Nat → Fin n) (field : LookupFieldAgreement relations) : Agreement relations :=
  ⟨field.source.polynomial placement, field.lowered.polynomial, field.witness⟩

def LookupFieldAgreement.check {relations : List (Polynomial n Source.BaseField)}
    (placement : Nat → Fin n) (field : LookupFieldAgreement relations) : Bool :=
  (field.agreement placement).check

theorem LookupFieldAgreement.sound {relations : List (Polynomial n Source.BaseField)}
    (placement : Nat → Fin n) {field : LookupFieldAgreement relations}
    (checked : field.check placement = true) {values : Fin n → Source.BaseField}
    (holds : Satisfies relations values) :
    field.source.value (values ∘ placement) = field.lowered.value values := by
  have same := Agreement.sound checked holds
  change evaluate values (field.source.polynomial placement) =
    evaluate values field.lowered.polynomial at same
  rw [field.source.polynomial_value, field.lowered.polynomial_value] at same
  exact same

end Airbender.Compiler
