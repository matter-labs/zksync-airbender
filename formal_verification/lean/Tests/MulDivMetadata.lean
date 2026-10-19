import Tests.MulDivInitialized

namespace Tests.MulDivInitialized
open Airbender Arithmetic Trace Verification MulDiv Tests.MulDivInitializedFixture

def wrongTag (i : Nat) : ZMod mersenne31Modulus :=
  if i = 11 then 1 else assignment .mul false false i

theorem wrong_tag_native :
    FlatOperation.ConstraintsHoldFlat (environment wrongTag) MulDiv.importedConstraints := by
  simpa [MulDiv.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
    environment,wrongTag,Lookup.Contains,range16,timestamp19,fixed3,Table.toRaw,
    ProvableType.fromElements] using native_constraints .mul false false

theorem wrong_tag_rejected :
    ¬(setup .mul false).table.Contains #[] (MulDiv.decoderQuery wrongTag) := by
  intro member
  obtain ⟨actual,present,same⟩ := MulDiv.Proofs.decoder_member (by decide) wrong_tag_native member
  have single : actual = entry .mul false := by
    simpa [setup,SparseDecoderSetup.program] using present
  subst actual
  rw [entry_query] at same
  have tag := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[8]) same
  change (1 : ZMod mersenne31Modulus) = 0 at tag
  exact (by decide : (1 : ZMod mersenne31Modulus) ≠ 0) tag

/-- Malformed metadata still passes local equations after a compensating mask
    write. Public original-byte membership excludes it. This is an argument
    boundary regression, not an accepted initialized trace or a native defect. -/
def wrongFlag (i : Nat) : ZMod mersenne31Modulus :=
  if i = 8 then 2 else if i = 60 then -861 else assignment .mul false false i

theorem wrong_flag_native :
    FlatOperation.ConstraintsHoldFlat (environment wrongFlag) MulDiv.importedConstraints := by
  simp [MulDiv.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
    environment,wrongFlag,assignment,MulDivWitness.assignment,MulDivWitness.witnessValues]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | (apply MulDivWitness.byte_query_contains <;> decide) | decide

theorem wrong_flag_unbounded : ¬(writtenWord wrongFlag).Bounded := by
  intro bounded
  have low := bounded.1
  change (-861 : ZMod mersenne31Modulus).val < 65536 at low
  change 2147482786 < 65536 at low
  omega

theorem wrong_flag_rejected :
    ¬(setup .mul false).table.Contains #[] (MulDiv.decoderQuery wrongFlag) := by
  intro member
  obtain ⟨actual,present,same⟩ := MulDiv.Proofs.decoder_member (by decide) wrong_flag_native member
  have single : actual = entry .mul false := by
    simpa [setup,SparseDecoderSetup.program] using present
  subst actual
  rw [entry_query] at same
  have flag := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[5]) same
  change (2 : ZMod mersenne31Modulus) = 0 at flag
  exact (by decide : (2 : ZMod mersenne31Modulus) ≠ 0) flag

end Tests.MulDivInitialized
