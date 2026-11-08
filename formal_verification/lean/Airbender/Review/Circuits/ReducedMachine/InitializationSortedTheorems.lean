import Airbender.Proofs.ReducedMachine.NativeInitializationSorted

namespace Airbender.NativeInitializationSorted
open Airbender.NativeInitializationOrdering Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native

/-- Natural sorting of EVERY ordinary initialization record, with strict growth
    from each nonpadding record. The SAME complete source and explicit full-family
    logical lookup boundary are retained; no expected order/borrow is supplied. -/
theorem native_initialization_sorted {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R}
    (accepted : Airbender.NativeScalar16Lookups.Accepted embed memory pc gamma proof) :
    (∀ i j, i ≤ j → j < scalar16Layout.traceLength-1 →
      addressValue (proof.initialization.main.rows i) ≤ addressValue (proof.initialization.main.rows j)) ∧
    (∀ i j, i < j → j < scalar16Layout.traceLength-1 → ¬ PaddingRecord (proof.initialization.main.rows i) →
      addressValue (proof.initialization.main.rows i) < addressValue (proof.initialization.main.rows j)) :=
  NativeInitializationSortedProofs.full_order embed memory pc gamma accepted

/-- Global uniqueness of actual native token addresses among nonpadding ordinary
    records, including the final ordinary row. Repeated padding remains allowed.
    Public windows/image/seeds and combined worker history are separate obligations. -/
theorem native_initialization_nonpadding_unique {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R}
    (accepted : Airbender.NativeScalar16Lookups.Accepted embed memory pc gamma proof)
    (i j : Nat) (ib : i < scalar16Layout.traceLength-1) (jb : j < scalar16Layout.traceLength-1)
    (ip : ¬ PaddingRecord (proof.initialization.main.rows i)) (jp : ¬ PaddingRecord (proof.initialization.main.rows j))
    (same : (Airbender.NativeMemoryTokens.encodeKey (initializationKey (proof.initialization.main.rows i) true)).address =
      (Airbender.NativeMemoryTokens.encodeKey (initializationKey (proof.initialization.main.rows j) true)).address) : i = j :=
  NativeInitializationSortedProofs.token_unique embed memory pc gamma accepted i j ib jb ip jp same

end Airbender.NativeInitializationSorted
