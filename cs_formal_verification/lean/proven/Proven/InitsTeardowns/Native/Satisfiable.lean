module
public import Human.Compiler.NativeMemory

@[expose] public section

namespace Airbender.InitsTeardowns.Native.Proofs
open Compiler

/-- Zero challenges and zero windows. Every compiled initialization tuple is one. -/
def zeroChallenges : NativeMemory.Challenges NativeArithmetic.F :=
  ⟨⟨RingHom.id _, 0, fun _ => 0, fun _ => 0⟩, 0⟩

/-- A compiled two-element field is a two-element list. -/
theorem fixed_pair {α : Type} (pair : Fixed 2 α) : ∃ first second, pair.values.toList = [first, second] :=
  List.length_eq_two.mp (show pair.values.toList.length = 2 by simpa using pair.size_eq)

/-- Under zero challenges, unit extension values satisfy every compiled initialization pair, extension copy and
    extension product of any circuit. -/
theorem unit_holds (circuit : Circuit) (layout : InitsTeardowns.Layout) (physical : GKRAddress → NativeArithmetic.F) :
    NativeMemory.InitializationHolds circuit layout zeroChallenges physical (fun _ => 1) := by
  intro layer _ gate _
  generalize gate.enforced_relation = relation
  cases relation with
  | InitsOrTeardownsInitialPair mode setup output sets =>
    obtain ⟨left, right, setsPair⟩ := fixed_pair sets
    obtain ⟨low, high, setupPair⟩ := fixed_pair setup
    have unit : ∀ side, NativeMemory.initializationTuple zeroChallenges physical
        (InitsTeardowns.topShift layout) mode setup left side = some 1 ∧
        NativeMemory.initializationTuple zeroChallenges physical
          (InitsTeardowns.topShift layout) mode setup right side = some 1 := by
      intro side
      cases mode with
      | Init =>
        simp [NativeMemory.initializationTuple, setupPair, NativeMemory.teardownTerms, zeroChallenges,
          NativeMemory.Challenges.embed]
      | Teardown leftTime leftValue rightTime rightValue =>
        obtain ⟨a, b, leftTimePair⟩ := fixed_pair leftTime
        obtain ⟨c, d, leftValuePair⟩ := fixed_pair leftValue
        obtain ⟨e, f, rightTimePair⟩ := fixed_pair rightTime
        obtain ⟨g, h, rightValuePair⟩ := fixed_pair rightValue
        by_cases first : side == 0 <;>
          simp [NativeMemory.initializationTuple, setupPair, NativeMemory.teardownTerms, zeroChallenges,
            NativeMemory.Challenges.embed, first, leftTimePair, leftValuePair, rightTimePair, rightValuePair]
    simp only [NativeMemory.InitializationGateHolds, setsPair]
    exact ⟨1, 1, (unit 0).1, (unit 1).2, by simp⟩
  | CopyInExtensionField input output => rfl
  | TrivialProduct input output =>
    obtain ⟨left, right, inputPair⟩ := fixed_pair input
    simp [NativeMemory.InitializationGateHolds, NativeMemory.GateHolds, inputPair]
  | _ => trivial

end Airbender.InitsTeardowns.Native.Proofs
