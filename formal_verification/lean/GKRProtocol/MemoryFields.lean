import GKRProtocol.MemorySource
import GKRProtocol.BaseEncoding

namespace Airbender.Compiler
set_option warningAsError true

structure MemoryFieldAgreement (relations : List (Polynomial n Source.BaseField)) where
  source : Source.MemoryField
  lowered : Expression n Source.BaseField
  witness : Combination relations

def MemoryFieldAgreement.agreement {relations : List (Polynomial n Source.BaseField)}
    (placement : Source.MemoryPlacement n) (field : MemoryFieldAgreement relations) : Agreement relations :=
  ⟨field.source.polynomial placement, field.lowered.polynomial, field.witness⟩

def MemoryFieldAgreement.check {relations : List (Polynomial n Source.BaseField)}
    (placement : Source.MemoryPlacement n) (field : MemoryFieldAgreement relations) : Bool :=
  (field.agreement placement).check

theorem MemoryFieldAgreement.sound {relations : List (Polynomial n Source.BaseField)}
    (placement : Source.MemoryPlacement n) {field : MemoryFieldAgreement relations}
    (checked : field.check placement = true) {values : Fin n → Source.BaseField}
    (holds : Satisfies relations values) :
    field.source.value (placement.project values) = field.lowered.value values := by
  have same := Agreement.sound checked holds
  change evaluate values (field.source.polynomial placement) = evaluate values field.lowered.polynomial at same
  rw [field.source.polynomial_value, field.lowered.polynomial_value] at same
  exact same

end Airbender.Compiler
