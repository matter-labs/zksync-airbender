import Airbender.Proofs.ReducedMachine.NativeInitializationWindow

namespace Airbender.NativeInitializationWindow
open Airbender.NativeInitializationBoundary Airbender.NativeInitializationOrdering Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native

/-- Actual native zero-terminal fallback forces ALL ordinary previous records to
    padding under complete source/sorting acceptance; no padded-chunk premise. -/
theorem native_initialization_window_fallback {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {previous current : Chunk R}
    (left : Airbender.NativeInitializationBoundary.Accepted embed memory pc gamma previous.proof previous.values)
    (right : Airbender.NativeInitializationBoundary.Accepted embed memory pc gamma current.proof current.values)
    (window : WindowAccepted previous.values current.values)
    (fallback : ¬ addressValue previous.values.oneBeforeLast < addressValue current.values.first) :
    ∀ i < scalar16Layout.traceLength-1, PaddingRecord (previous.proof.initialization.main.rows i) :=
  NativeInitializationWindowProofs.fallback_rows embed memory pc gamma left right window fallback

/-- EVERY ordinary row across EVERY pair of ordered supplied chunks. Padding
    remains in the actual sequence; nonpadding records grow strictly. Indexed
    normalized batch acceptance is separate from full physical protocol extraction. -/
theorem native_initialization_chunk_order {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {count : Nat} {chunks : Nat → Chunk R}
    (accepted : Airbender.NativeInitializationWindow.Accepted embed memory pc gamma count chunks) :
    ∀ c d, c < d → d < count → ∀ i < scalar16Layout.traceLength-1, ∀ j < scalar16Layout.traceLength-1,
      Airbender.NativeInitializationSorted.addressValue ((chunks c).proof.initialization.main.rows i) ≤
        Airbender.NativeInitializationSorted.addressValue ((chunks d).proof.initialization.main.rows j) ∧
      (¬ PaddingRecord ((chunks c).proof.initialization.main.rows i) →
        Airbender.NativeInitializationSorted.addressValue ((chunks c).proof.initialization.main.rows i) <
          Airbender.NativeInitializationSorted.addressValue ((chunks d).proof.initialization.main.rows j)) :=
  NativeInitializationWindowProofs.global_rows embed memory pc gamma accepted

/-- Global nonpadding native TOKEN-address uniqueness across all supplied chunks
    and all ordinary rows. This derives no public seed/image coverage or worker
    initialized memory, clocks, keys, execution or request accounting. -/
theorem native_initialization_global_token_unique {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {count : Nat} {chunks : Nat → Chunk R}
    (accepted : Airbender.NativeInitializationWindow.Accepted embed memory pc gamma count chunks)
    (c d i j : Nat) (cb : c < count) (db : d < count)
    (ib : i < scalar16Layout.traceLength-1) (jb : j < scalar16Layout.traceLength-1)
    (ip : ¬ PaddingRecord ((chunks c).proof.initialization.main.rows i))
    (jp : ¬ PaddingRecord ((chunks d).proof.initialization.main.rows j))
    (same : (Airbender.NativeMemoryTokens.encodeKey (initializationKey ((chunks c).proof.initialization.main.rows i) true)).address =
      (Airbender.NativeMemoryTokens.encodeKey (initializationKey ((chunks d).proof.initialization.main.rows j) true)).address) : c = d ∧ i = j :=
  NativeInitializationWindowProofs.global_token_unique embed memory pc gamma accepted c d i j cb db ib jb ip jp same
end Airbender.NativeInitializationWindow
