import Human.Vectors

/-! `RV.StandardVectors`, each by evaluation in the kernel. Keccak-f[1600] in two halves of 12 rounds (one
evaluation of all 24 takes the kernel about 13 s), through the state after round 12 (`keccakMid`, computed once). -/

namespace RV
open Spec

theorem blake2s_test_vector : Blake2sTestVector := by unfold Blake2sTestVector; decide +kernel

/-- The all-zero state after 12 Keccak-f[1600] rounds. -/
def keccakMid : Vector Lane 25 :=
  #v[0x4089b1d2ef5d3a26, 0x8409f6c9be239ecb, 0x12657d5a4568ead5, 0x4d9f3e32387e66d3, 0x3be7f6680bb1c847,
    0x61ed7fb0ce6ca6af, 0x3671348a3fbd6487, 0x81e9f633f01dcf03, 0xab5eefa38e5546d9, 0x8298d4e430062494,
    0x3229e84a8e1704c2, 0x56f221867a1b3140, 0xdb7043cf08757bb2, 0x52de6de69935b888, 0x98a1c2d38194eda1,
    0x9af85d4549fb53c7, 0x667e09de6b59e740, 0xc08877b3d1a7a9f3, 0x5da108d19209739f, 0xe0e096ffe4ff71ea,
    0x77badafbfd43d602, 0x50a13329b93c785f, 0xf8ae145adffbe076, 0x366d5164bb8f0bb5, 0x438298aa08f16a54]

/-- Rounds `rs` of Keccak-f[1600]. -/
def keccakRounds (rs : List (Fin 24)) (A : Vector Lane 25) : Vector Lane 25 := rs.foldl (fun A r => keccakRound r A) A

theorem keccak_first_half : keccakRounds ((List.finRange 24).take 12) (Vector.replicate 25 0) = keccakMid := by
  decide +kernel

theorem keccak_second_half :
    (keccakRounds ((List.finRange 24).drop 12) keccakMid).toList.take 2 = [0xF1258F7940E1DDE7, 0x84D5CCF933C0478A] := by
  decide +kernel

theorem keccak_test_vector : KeccakTestVector := by
  rw [KeccakTestVector, keccakF, ← List.take_append_drop 12 (List.finRange 24), List.foldl_append]
  exact (congrArg (fun A => (keccakRounds _ A).toList.take 2) keccak_first_half).trans keccak_second_half

theorem keccak_slot_table : KeccakSlotTable := by unfold KeccakSlotTable; decide +kernel

theorem standard_vectors : StandardVectors := ⟨blake2s_test_vector, keccak_test_vector, keccak_slot_table⟩

end RV
