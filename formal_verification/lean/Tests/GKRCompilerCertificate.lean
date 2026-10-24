import GKRCompiler.Native.AddSubUncached

namespace Tests.GKRCompilerCertificate
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private abbrev original := Airbender.Compiler.Native.AddSubUncached.native.translation
private abbrev originalCertificate := Airbender.Compiler.Native.AddSubUncached.native.certificate

/-- All lowered equations are replaced by zero, retaining their count and
the original certificate. The checker detects the lost source obligations. -/
private def dropped : Translation 42 48 (ZMod babyBearModulus) :=
  { original with lowered := original.lowered.map (fun _ => []) }

private def droppedCertificate : Certificate dropped :=
  ⟨originalCertificate.backward, originalCertificate.forward⟩

theorem rejects_dropped_constraints : check dropped droppedCertificate = false := by
  decide +kernel

/-- A coefficient-level corruption starting from the actual ADD/SUB
source/output equations and their original identity certificate. -/
private def changed : Translation 42 48 (ZMod babyBearModulus) :=
  { original with lowered := add (constant 1) original.lowered.head! :: original.lowered.tail }

private def changedCertificate : Certificate changed :=
  ⟨originalCertificate.backward, originalCertificate.forward⟩

theorem rejects_changed_constraint : check changed changedCertificate = false := by
  decide +kernel

private def wrongExtension : Translation 42 48 (ZMod babyBearModulus) :=
  { original with extension := fun _ => [] }

private def wrongExtensionCertificate : Certificate wrongExtension :=
  ⟨originalCertificate.backward, originalCertificate.forward⟩

theorem rejects_wrong_witness_extension : check wrongExtension wrongExtensionCertificate = false := by
  decide +kernel

private def wrongPlacement : Translation 42 48 (ZMod babyBearModulus) :=
  { original with projection := fun index =>
      if index.val = 0 then original.projection 1 else original.projection index }

private def wrongPlacementCertificate : Certificate wrongPlacement :=
  ⟨originalCertificate.backward, originalCertificate.forward⟩

theorem rejects_wrong_placement : check wrongPlacement wrongPlacementCertificate = false := by
  decide +kernel

private def inconsistent : ArithmeticGate 48 (ZMod babyBearModulus) :=
  .assertZero (.constant 0) (.constant 1)

theorem rejects_inconsistent_native_fields : inconsistent.check = false := by
  decide +kernel

end Tests.GKRCompilerCertificate
