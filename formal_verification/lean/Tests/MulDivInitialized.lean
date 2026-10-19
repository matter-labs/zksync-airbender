import Tests.MulDivInitializedFixture

namespace Tests.MulDivInitialized
open Airbender Arithmetic Trace Verification MulDiv Tests.MulDivInitializedFixture

/-- Sixteen complete initialized native traces derive actual Clean history. -/
theorem public_history (op : Operation) (discarded zeroDivisor : Bool) :
    ∃ history, MemoryHistory (trace op discarded zeroDivisor) history :=
  (MulDiv.public_memory_soundness (public_inputs op discarded zeroDivisor)
    (accepted op discarded zeroDivisor)).1

theorem first_latest (op : Operation) (discarded zeroDivisor : Bool) :
    LatestRead (trace op discarded zeroDivisor) (nativeRow op discarded zeroDivisor)
      MulDiv.importedConstraintsMemoryPorts[0] :=
  (MulDiv.public_memory_soundness (public_inputs op discarded zeroDivisor)
    (accepted op discarded zeroDivisor)).2 _ (by simp [trace]) _
      (by change _ ∈ MulDiv.importedConstraintsMemoryPorts; simp [MulDiv.importedConstraintsMemoryPorts])

theorem public_bounds (op : Operation) (discarded zeroDivisor : Bool) :
    ∀ token ∈ (trace op discarded zeroDivisor).terminalMemory, token.word.Bounded :=
  (MulDiv.public_value_bounds (program_image op discarded zeroDivisor)
    (public_inputs op discarded zeroDivisor) (accepted op discarded zeroDivisor)
    (decoded op discarded zeroDivisor)).2.2

/-- No operand bound, packed selector, zero flag, expected read or result is
    supplied to the initialized public theorem. -/
theorem public_results (op : Operation) (discarded zeroDivisor : Bool) :
    ∃ entry ∈ (setup op discarded).program,
      entry.SourceWith (before op discarded zeroDivisor) MulDiv.decoderFields ∧
      (nativeRow op discarded zeroDivisor).decoderQuery = entry.query ∧
      (selectedWord (assignment op discarded zeroDivisor)).value = entry.data.family.result
        (left (assignment op discarded zeroDivisor)) (right (assignment op discarded zeroDivisor)) ∧
      (writtenWord (assignment op discarded zeroDivisor)).value = if entry.data.rd = 0 then 0 else
        entry.data.family.result (left (assignment op discarded zeroDivisor))
          (right (assignment op discarded zeroDivisor)) :=
  MulDiv.public_native_results (program_image op discarded zeroDivisor)
    (public_inputs op discarded zeroDivisor) (accepted op discarded zeroDivisor)
    (decoded op discarded zeroDivisor) _ (by simp [trace])

theorem hole_and_tail (op : Operation) (discarded : Bool) :
    (setup op discarded).slots[1]? = some none ∧
    ∀ i : Fin ((setup op discarded).slots.length + (setup op discarded).padding),
      2 ≤ i.val → (setup op discarded).row (p := mersenne31Modulus) i =
        Vector.replicate 10 (-1) := by
  constructor
  · rfl
  · intro i outside
    apply Trace.Proofs.sparse_row_absent
    simpa only [setup,List.length_cons,List.length_nil] using outside

theorem insufficient_capacity (op : Operation) (discarded zeroDivisor : Bool) :
    MulDiv.sparseDecoderSetupImage (before op discarded zeroDivisor) 2 0 = none := rfl

theorem signed_profile_rejected :
    MulDiv.decoderFields (.MUL (.Regidx 2,.Regidx 1,.Regidx 3,⟨.High,.Signed,.Signed⟩)) = none ∧
    MulDiv.decoderFields (.MUL (.Regidx 2,.Regidx 1,.Regidx 3,⟨.High,.Signed,.Unsigned⟩)) = none ∧
    MulDiv.decoderFields (.DIV (.Regidx 2,.Regidx 1,.Regidx 3,false)) = none ∧
    MulDiv.decoderFields (.REM (.Regidx 2,.Regidx 1,.Regidx 3,false)) = none := ⟨rfl,rfl,rfl,rfl⟩

end Tests.MulDivInitialized
