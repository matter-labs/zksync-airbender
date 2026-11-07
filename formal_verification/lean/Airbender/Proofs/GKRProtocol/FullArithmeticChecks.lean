import Airbender.Proofs.GKRCompiler.Bidirectional
import Airbender.Proofs.GKRCompiler.Wiring
import Airbender.Proofs.GKRProtocol.AddressUniqueChecks
import Airbender.Proofs.GKRProtocol.FastPolynomialChecks

namespace Airbender.Compiler.FullArithmeticChecks
set_option warningAsError true

/-- Build natural indices and construct each bounded index at its use site. -/
def allFin (bound : Nat) (predicate : Fin bound → Bool) : Bool :=
  (List.range bound).all fun index => if inside : index < bound then predicate ⟨index, inside⟩ else false

theorem allFin_eq (bound : Nat) (predicate : Fin bound → Bool) :
    allFin bound predicate = (List.finRange bound).all predicate := by
  apply Bool.eq_iff_iff.mpr
  simp only [allFin]
  constructor
  · intro checked
    apply List.all_eq_true.mpr
    intro index _
    have item := List.all_eq_true.mp checked index.val (List.mem_range.mpr index.isLt)
    simpa only [dif_pos index.isLt] using item
  · intro checked
    apply List.all_eq_true.mpr
    intro index member
    have inside := List.mem_range.mp member
    have item := List.all_eq_true.mp checked ⟨index, inside⟩ (List.mem_finRange _)
    simpa only [dif_pos inside] using item

def translationCheck {n m : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (translation : Translation n m F) (certificate : Certificate translation) : Bool :=
  allFin n (fun wire => FastPolynomialChecks.equal (translation.extension (translation.projection wire)) (atom wire)) &&
  allFin translation.source.length (fun index =>
    FastPolynomialChecks.equal (rename translation.projection (translation.source.get index))
      (combination translation.lowered (certificate.backward index))) &&
  allFin translation.lowered.length (fun index =>
    FastPolynomialChecks.equal (substitute translation.extension (translation.lowered.get index))
      (combination translation.source (certificate.forward index)))

theorem translationCheck_eq {n m : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (translation : Translation n m F) (certificate : Certificate translation) :
    translationCheck translation certificate = Airbender.Compiler.check translation certificate := by
  simp only [translationCheck, Airbender.Compiler.check, allFin_eq, FastPolynomialChecks.equal_eq]

/-- Check the complete native arithmetic capture and its address bank. -/
def check {n m : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (addresses : List GKRAddress) (artifact : ArithmeticExtension n m F)
    (certificate : Certificate artifact.translation) : Bool :=
  AddressUniqueChecks.check addresses &&
    translationCheck artifact.translation certificate &&
    artifact.gates.all ArithmeticGate.check

theorem checked_parts {n m : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (addresses : List GKRAddress) (artifact : ArithmeticExtension n m F)
    (certificate : Certificate artifact.translation)
    (checked : check addresses artifact certificate = true) :
    (List.finRange addresses.length).all (distinctAt addresses) = true ∧
    Airbender.Compiler.check artifact.translation certificate = true ∧
    artifact.gates.all ArithmeticGate.check = true := by
  simp only [check, translationCheck_eq, Bool.and_eq_true] at checked
  have unique := AddressUniqueChecks.check_sound addresses checked.1.1
  refine ⟨?_, checked.1.2, checked.2⟩
  apply List.all_eq_true.mpr
  intro index _
  exact AddressUniqueChecks.distinctAt_complete addresses unique index

theorem check_sound {n m : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (addresses : List GKRAddress) (artifact : ArithmeticExtension n m F)
    (certificate : Certificate artifact.translation)
    (checked : check addresses artifact certificate = true) :
    addresses.Nodup ∧ certificate.Valid ∧ artifact.gates.all ArithmeticGate.check = true := by
  have facts := checked_parts addresses artifact certificate checked
  refine ⟨distinctAt_sound ?_, check_valid facts.2.1, facts.2.2⟩
  intro index
  exact List.all_eq_true.mp facts.1 index (List.mem_finRange _)

theorem unique_at {n m : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (addresses : List GKRAddress) (artifact : ArithmeticExtension n m F)
    (certificate : Certificate artifact.translation)
    (checked : check addresses artifact certificate = true) (index : Fin addresses.length) :
    distinctAt addresses index = true :=
  List.all_eq_true.mp (checked_parts addresses artifact certificate checked).1 index (List.mem_finRange _)

theorem relation_at {n m : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (addresses : List GKRAddress) (artifact : ArithmeticExtension n m F)
    (certificate : Certificate artifact.translation)
    (checked : check addresses artifact certificate = true) (index : Fin artifact.translation.lowered.length) :
    equal (substitute artifact.translation.extension (artifact.translation.lowered.get index))
      (combination artifact.translation.source (certificate.forward index)) = true :=
  (check_sound addresses artifact certificate checked).2.1.2.2 index

theorem source_at {n m : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (addresses : List GKRAddress) (artifact : ArithmeticExtension n m F)
    (certificate : Certificate artifact.translation)
    (checked : check addresses artifact certificate = true) (index : Fin artifact.translation.source.length) :
    equal (rename artifact.translation.projection (artifact.translation.source.get index))
      (combination artifact.translation.lowered (certificate.backward index)) = true :=
  (check_sound addresses artifact certificate checked).2.1.2.1 index

theorem gate_at {n m : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (addresses : List GKRAddress) (artifact : ArithmeticExtension n m F)
    (certificate : Certificate artifact.translation)
    (checked : check addresses artifact certificate = true) (index : Fin artifact.gates.length) :
    (artifact.gates.get index).check = true :=
  List.all_eq_true.mp (checked_parts addresses artifact certificate checked).2.2 _
    (List.getElem_mem index.isLt)

/-- Keep the original source shape before an imported field expression reduces. -/
theorem source_at_original {n m : Nat} {F : Type} [CommRing F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (addresses : List GKRAddress) (artifact : ArithmeticExtension n m F)
    (certificate : Certificate artifact.translation)
    (checked : check addresses artifact certificate = true) (index : Fin artifact.source.length) :
    equal (rename artifact.projection (artifact.source.get index))
      (combination artifact.translation.lowered (certificate.backward index)) = true :=
  source_at addresses artifact certificate checked index

end Airbender.Compiler.FullArithmeticChecks
