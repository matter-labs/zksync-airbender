module
public import Human.ISA.Vectors
import all Init.Data.Array.DecidableEq -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)
import all Init.Data.Vector.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

/-! `RV.StandardVectors`, each by evaluation in the kernel. -/

namespace RV
open Spec

theorem Deleg.blake2s_test_vector : Blake2sTestVector := by unfold Blake2sTestVector; decide +kernel

theorem Deleg.keccak_test_vector : KeccakTestVector := by unfold KeccakTestVector; decide +kernel

theorem Deleg.keccak_slot_table : KeccakSlotTable := by unfold KeccakSlotTable; decide +kernel

end RV
