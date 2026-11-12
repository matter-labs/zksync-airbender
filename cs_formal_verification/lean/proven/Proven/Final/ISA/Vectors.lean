module
public import Proven.Deleg.Vectors

@[expose] public section

/-! The standards' test vectors (`Human/ISA/Vectors.lean`). -/

namespace RV

theorem standard_vectors : StandardVectors :=
  ⟨Deleg.blake2s_test_vector, Deleg.keccak_test_vector, Deleg.keccak_slot_table⟩

end RV
