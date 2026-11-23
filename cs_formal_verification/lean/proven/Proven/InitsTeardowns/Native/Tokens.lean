module
public import Proven.InitsTeardowns.Native.Trees
public import Proven.InitsTeardowns.Claims

@[expose] public section

namespace Airbender.InitsTeardowns.Native.Proofs

/-- A vector lists its entries in index order. -/
theorem vector_list {α : Type} {n : Nat} (values : Vector α n) :
    values.toList = (List.finRange n).map (fun index => values[index]) := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp

/-- Public windows and logical teardown sets have the same native set order. -/
theorem vector_zip_array {α β : Type} (sets : Array β) (values : Vector α sets.size) :
    values.toList.zip sets.toList =
      (List.finRange sets.size).map (fun index => (values[index], sets[index])) := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp

/-- Native RAM addresses equal the logical window addresses under the verifier bounds. -/
theorem native_address {layout : InitsTeardowns.Layout}
    (shape : InitsTeardowns.Proofs.Shape layout) {top row : Nat}
    (topBound : top < InitsTeardowns.maxTopBit) (rowBound : row < 2 ^ layout.traceLog) :
    InitsTeardowns.addressCode (p := babyBearModulus) layout top row =
      Nat.pair 1 (Nat.pair (addressLo row) (row / 16384 + top * 2 ^ InitsTeardowns.topShift layout)) := by
  have limbFacts := InitsTeardowns.Proofs.limbs shape.traceLog topBound rowBound
  have lowBound : row * 2 ^ 2 % 2 ^ 16 < babyBearModulus := by
    norm_num only [Nat.reducePow]
    unfold babyBearModulus
    omega
  have highBound : row / 2 ^ (16 - 2) + (top <<< (layout.traceLog + 2 - 16)) % 2 ^ 32 < babyBearModulus := by
    have same := limbFacts.2.1
    have small := limbFacts.2.2
    unfold babyBearModulus
    omega
  unfold InitsTeardowns.addressCode InitsTeardowns.addressLimbs
    InitsTeardowns.setupLow InitsTeardowns.setupHigh InitsTeardowns.topShift addressLo
  rw [shape.wordBits, ← Nat.cast_add,
    InitsTeardowns.Proofs.natCast_val lowBound, InitsTeardowns.Proofs.natCast_val highBound]
  obtain ⟨_, traceLog⟩ := shape
  rcases traceLog with log | log <;> rw [log]
  all_goals
    norm_num only [Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd]
    unfold InitsTeardowns.maxTopBit at topBound
    congr 2 <;> omega

/-- The native finite row indices have the same order as logical row numbers. -/
theorem finRange_values (size : Nat) : (List.finRange size).map Fin.val = List.range size := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp

end Airbender.InitsTeardowns.Native.Proofs

namespace Airbender.InitsTeardowns.Native

/-- The memory token of one native leaf at one row, read from native addresses and raw columns.
    It is the proof form of a leaf factor. -/
def Leaf.token {p : Nat} {E : Type} [CommRing E] (layout : Layout) (parameters : Parameters p E) (raw : Raw p)
    (row : Nat) (leaf : Leaf) : Trace.MemoryToken p :=
  ⟨Nat.pair 1 (Nat.pair (addressLo row) (addressHi layout parameters leaf.set row)),
    leaf.time raw row, Nat.pair (leaf.value raw row).1.val (leaf.value raw row).2.val⟩

end Airbender.InitsTeardowns.Native

namespace Airbender.InitsTeardowns.Native.Proofs

variable {p : Nat} [Fact p.Prime] [CommRing E]

theorem factor_token (layout : Layout) (parameters : Parameters p E) (raw : Raw p)
    (row : Nat) (leaf : Leaf) :
    leaf.factor layout parameters raw row = parameters.encode (leaf.token layout parameters raw row) := by
  simp [Leaf.factor, Parameters.encode, Leaf.token]

theorem root_tokens {artifact : Artifact} {tree : Tree} {phase : Phase}
    (parameters : Parameters p E) (raw : Raw p) (wires : Wires E)
    (linked : tree.Follows artifact.gates)
    (covered : tree.leaves = artifact.layout.leaves phase)
    (accepted : Accepted artifact parameters raw wires) (row : Fin artifact.layout.rows) :
    wires tree.output row.val =
      ((artifact.layout.leaves phase).map fun leaf =>
        parameters.encode (leaf.token artifact.layout parameters raw row.val)).prod := by
  rw [follows_sound artifact.layout parameters raw wires row.val linked (accepted row),
    eval_leaves, covered]
  rw [show Leaf.factor artifact.layout parameters raw row.val =
      (fun leaf => parameters.encode (leaf.token artifact.layout parameters raw row.val)) from
    funext fun leaf => factor_token artifact.layout parameters raw row.val leaf]

end Airbender.InitsTeardowns.Native.Proofs
