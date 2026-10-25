import GKRProtocol.InitializationTokens

namespace Airbender.Compiler
open Airbender
set_option warningAsError true

/-- Native tuple factor with Rust's supplied per-set top bits. Virtual high
setup contains only row-high bits; the public window is added per set. -/
def windowedBoundaryToken (memory : Source.MemoryValues) (publicTops : Nat → Nat)
    (stageKind : Initialization.Phase) (set stride : Nat) : Trace.MemoryToken babyBearModulus :=
  ⟨Nat.pair 1 (Nat.pair (memory.initializationAddress 0).val
      (memory.initializationAddress 1 + (publicTops set * stride : Nat)).val),
    match stageKind with
    | .initial => (0, 0)
    | .terminal => (memory.teardownTimestamp set 0, memory.teardownTimestamp set 1),
    match stageKind with
    | .initial => 0
    | .terminal => Nat.pair (memory.teardownValue set 0).val (memory.teardownValue set 1).val⟩

theorem windowed_boundary_specialization (memory : Source.MemoryValues)
    (stageKind : Initialization.Phase) (set stride : Nat) :
    windowedBoundaryToken memory id stageKind set stride = sourceBoundaryToken memory stageKind set stride := rfl

theorem windowed_boundary_leaf (layout : Initialization.Layout)
    (parameters : Initialization.Parameters babyBearModulus Source.BaseField)
    (memory : Source.MemoryValues) (publicTops : Nat → Nat) (raw : Initialization.Raw babyBearModulus)
    (stageKind : Initialization.Phase) (set : Fin layout.columns.size) (row : Fin layout.rows)
    (low : memory.initializationAddress 0 = (Initialization.addressLo row.val : Source.BaseField))
    (high : memory.initializationAddress 1 + (publicTops set.val * layout.stride : Nat) =
      (Initialization.addressHi layout parameters set.val row.val : Source.BaseField))
    (lowBound : Initialization.addressLo row.val < babyBearModulus)
    (highBound : Initialization.addressHi layout parameters set.val row.val < babyBearModulus)
    (timeLo : memory.teardownTimestamp set.val 0 = raw row.val layout.columns[set].timeLo)
    (timeHi : memory.teardownTimestamp set.val 1 = raw row.val layout.columns[set].timeHi)
    (valueLo : memory.teardownValue set.val 0 = raw row.val layout.columns[set].valueLo)
    (valueHi : memory.teardownValue set.val 1 = raw row.val layout.columns[set].valueHi) :
    windowedBoundaryToken memory publicTops stageKind set.val layout.stride =
      (Initialization.Leaf.mk stageKind set.val layout.columns[set]).token layout parameters raw row.val := by
  cases stageKind <;>
    simp only [windowedBoundaryToken, Initialization.Leaf.token, Initialization.Leaf.time,
      Initialization.Leaf.value, low, high, timeLo, timeHi, valueLo, valueHi,
      ZMod.val_natCast, Nat.mod_eq_of_lt lowBound, Nat.mod_eq_of_lt highBound]
  all_goals rfl

theorem windowed_initial_fingerprint {R : Type} [CommRing R]
    (memory : Source.MemoryValues) (publicTops : Nat → Nat) (set stride : Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) :
    memoryTokenFingerprint hom challenges (windowedBoundaryToken memory publicTops .initial set stride) =
      challenges.memoryGamma + 1 + challenges.memoryPowers 0 * hom (memory.initializationAddress 0) +
        challenges.memoryPowers 1 * (hom (memory.initializationAddress 1) + hom (publicTops set * stride : Nat)) := by
  simp [windowedBoundaryToken, memoryTokenFingerprint, map_add]

theorem windowed_terminal_fingerprint {R : Type} [CommRing R]
    (memory : Source.MemoryValues) (publicTops : Nat → Nat) (set stride : Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) :
    memoryTokenFingerprint hom challenges (windowedBoundaryToken memory publicTops .terminal set stride) =
      challenges.memoryGamma + 1 + challenges.memoryPowers 0 * hom (memory.initializationAddress 0) +
        challenges.memoryPowers 1 * (hom (memory.initializationAddress 1) + hom (publicTops set * stride : Nat)) +
        challenges.memoryPowers 2 * hom (memory.teardownTimestamp set 0) +
        challenges.memoryPowers 3 * hom (memory.teardownTimestamp set 1) +
        challenges.memoryPowers 4 * hom (memory.teardownValue set 0) +
        challenges.memoryPowers 5 * hom (memory.teardownValue set 1) := by
  simp [windowedBoundaryToken, memoryTokenFingerprint, map_add]

end Airbender.Compiler
