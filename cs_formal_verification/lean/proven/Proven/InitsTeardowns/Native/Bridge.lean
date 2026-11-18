module
public import Proven.InitsTeardowns.Native.Semantics
public import Human.Compiler.NativeMemory
public import Human.Circuits.InitsTeardowns.Theorems

@[expose] public section

/-! The compiled acceptance `NativeMemory.InitializationHolds` of a circuit gives the tree semantics `Accepted` of the
    graph extracted from it. Each extracted gate is the decoded form of one compiled relation (`correspond`, checked
    by the kernel for each bound circuit). The compiled initialization tuple, with the setup address limbs of the
    row, is the leaf factor. -/

namespace Airbender.InitsTeardowns.Native.Proofs
open Compiler Compiler.NativeArithmetic

/-- The leaf reads the teardown columns of one side of the compiled pair; an initialization leaf reads none. -/
def leafMatches : InitsOrTeardownsTimestampAndValue → Nat → Leaf → Bool
  | .Init, _, leaf => leaf.phase == .initial
  | .Teardown leftTime leftValue rightTime rightValue, side, leaf =>
    let (time, value) := if side == 0 then (leftTime, leftValue) else (rightTime, rightValue)
    leaf.phase == .terminal && time.values.toList == [leaf.columns.timeLo, leaf.columns.timeHi] &&
      value.values.toList == [leaf.columns.valueLo, leaf.columns.valueHi]

/-- The extracted gate is the decoded form of the compiled relation. -/
def correspond : GKRRelation → Gate → Bool
  | .TrivialProduct input output, .product out left right =>
    input.values.toList == [Extract.address left, Extract.address right] && output == Extract.address out
  | .CopyInExtensionField input output, .copy out source =>
    input == Extract.address source && output == Extract.address out
  | .InitsOrTeardownsInitialPair mode setup output sets, .pair out left right =>
    setup.values.toList == [.VirtualSetup .InitsAndTeardownsLow, .VirtualSetup .InitsAndTeardownsHigh] &&
      sets.values.toList == [left.set, right.set] && output == Extract.address out &&
      leafMatches mode 0 left && leafMatches mode 1 right
  | _, _ => false

/-- The compiled relations of a circuit, in layer order. -/
def compiledRelations (circuit : Circuit) : List GKRRelation :=
  (Extract.allGates circuit).toList.map (·.enforced_relation)

/-- The set indices of an extracted initialization pair. Other gates have none. -/
def pairSets : Gate → List Nat
  | .pair _ left right => [left.set, right.set]
  | _ => []

/-- A window below the verifier ceiling, shifted by at most 26 bits, fits in a `u32`. -/
theorem window_bounded {n : Nat} (windows : Nat → Nat) (topBits : Vector Nat n) (shift : Nat)
    (small : 2 ^ shift ≤ 2 ^ 26) (equal : ∀ set : Fin n, windows set.val = topBits[set])
    (checked : ∀ top ∈ topBits.toList, top < InitsTeardowns.maxTopBit) (set : Nat) (inside : set < n) :
    windows set * 2 ^ shift < 2 ^ 32 := by
  have top := checked topBits[set] (Vector.mem_toList_iff.mpr (Vector.getElem_mem inside))
  rw [equal ⟨set, inside⟩]
  unfold InitsTeardowns.maxTopBit at top
  calc topBits[set] * 2 ^ shift < 64 * 2 ^ shift := Nat.mul_lt_mul_of_pos_right top (Nat.two_pow_pos shift)
    _ ≤ 64 * 2 ^ 26 := Nat.mul_le_mul_left 64 small
    _ = 2 ^ 32 := by norm_num

variable {E : Type} [CommRing E]

theorem holds_member {circuit : Circuit} {setupLayout : InitsTeardowns.Layout}
    {challenges : NativeMemory.Challenges E} {physical : GKRAddress → F} {values : GKRAddress → E}
    (holds : NativeMemory.InitializationHolds circuit setupLayout challenges physical values)
    {relation : GKRRelation} (member : relation ∈ compiledRelations circuit) :
    NativeMemory.InitializationGateHolds (InitsTeardowns.topShift setupLayout) challenges physical values
      relation := by
  obtain ⟨gate, inside, rfl⟩ := List.mem_map.mp member
  simp only [Extract.allGates, Array.toList_flatMap, List.mem_flatMap] at inside
  obtain ⟨layer, layerMember, gateMember⟩ := inside
  exact holds layer (Array.mem_toList_iff.mp layerMember) gate (by simpa using gateMember)

/-- One side of the compiled pair is the leaf factor, given the setup address limbs of a four-byte word row and a
    shifted window that fits in a `u32`. -/
theorem tuple_factor (layout : Layout) (setupLayout : InitsTeardowns.Layout) (words : setupLayout.wordBits = 2)
    (shift : Nat) (stride : layout.stride = 2 ^ shift) (challenges : NativeMemory.Challenges E)
    (physical : GKRAddress → F) (raw : Raw babyBearModulus) (row : Nat)
    (bank : ∀ column, physical (.BaseLayerMemory column) = raw row column)
    (mode : InitsOrTeardownsTimestampAndValue) (setup : Fixed 2 GKRAddress) (side : Nat) (leaf : Leaf)
    (inputs : setup.values.toList = [.VirtualSetup .InitsAndTeardownsLow, .VirtualSetup .InitsAndTeardownsHigh])
    (matched : leafMatches mode side leaf = true) (bounded : challenges.memory.windows leaf.set * 2 ^ shift < 2 ^ 32) :
    NativeMemory.initializationTuple challenges (withSetupAddresses setupLayout row physical) shift mode setup
        leaf.set side = some (leaf.factor layout challenges.memory raw row) := by
  have lowLimb : ((InitsTeardowns.setupLow setupLayout row : Nat) : F) = ((addressLo row : Nat) : F) := by
    unfold InitsTeardowns.setupLow addressLo
    rw [words, Nat.mul_comm]
    rfl
  have highLimb : (((InitsTeardowns.setupHigh setupLayout row : Nat) : F) +
      (((challenges.memory.windows leaf.set <<< shift) % 2 ^ 32 : Nat) : F)) =
      ((addressHi layout challenges.memory leaf.set row : Nat) : F) := by
    unfold InitsTeardowns.setupHigh addressHi
    rw [words, stride, Nat.shiftLeft_eq, Nat.mod_eq_of_lt bounded, Nat.cast_add]
    rfl
  have lowTerm : challenges.embed ((InitsTeardowns.setupLow setupLayout row : Nat) : F) =
      challenges.memory.embed ((addressLo row : Nat) : ZMod babyBearModulus) := by
    rw [NativeMemory.Challenges.embed, lowLimb]
  have highTerm : challenges.embed ((InitsTeardowns.setupHigh setupLayout row : Nat) : F) +
      challenges.embed (((challenges.memory.windows leaf.set <<< shift) % 2 ^ 32 : Nat) : F) =
      challenges.memory.embed ((addressHi layout challenges.memory leaf.set row : Nat) : ZMod babyBearModulus) := by
    rw [NativeMemory.Challenges.embed, NativeMemory.Challenges.embed, ← map_add, highLimb]
  unfold NativeMemory.initializationTuple
  rw [inputs]
  simp only [withSetupAddresses]
  cases mode with
  | Init =>
    simp only [leafMatches, beq_iff_eq] at matched
    simp only [NativeMemory.teardownTerms, Option.map_some, Option.some.injEq, Leaf.factor, Leaf.time, Leaf.value,
      matched]
    rw [lowTerm, highTerm, NativeMemory.Challenges.embed, map_one]
    simp only [map_zero, mul_zero, add_zero]
  | Teardown leftTime leftValue rightTime rightValue =>
    simp only [leafMatches, Bool.and_eq_true, beq_iff_eq] at matched
    obtain ⟨⟨phase, time⟩, value⟩ := matched
    by_cases first : side = 0
    all_goals
      simp only [first, ↓reduceIte] at time value
      simp only [NativeMemory.teardownTerms, first, beq_iff_eq, ↓reduceIte, time, value, Option.map_some,
        Option.some.injEq, Leaf.factor, Leaf.time, Leaf.value, phase, NativeMemory.Challenges.column,
        withSetupAddresses, bank]
      rw [lowTerm, highTerm, NativeMemory.Challenges.embed, NativeMemory.Challenges.embed,
        NativeMemory.Challenges.embed, NativeMemory.Challenges.embed, NativeMemory.Challenges.embed, map_one]
      ring

/-- A compiled gate gives the tree semantics of its decoded gate. -/
theorem gate_sat (layout : Layout) (setupLayout : InitsTeardowns.Layout) (words : setupLayout.wordBits = 2)
    (shift : Nat) (stride : layout.stride = 2 ^ shift) (challenges : NativeMemory.Challenges E)
    (physical : GKRAddress → F) (values : Nat → GKRAddress → E) (raw : Raw babyBearModulus) (row : Nat)
    (bank : ∀ column, physical (.BaseLayerMemory column) = raw row column)
    {relation : GKRRelation} {gate : Gate} (decoded : correspond relation gate = true)
    (bounded : ∀ set ∈ pairSets gate, challenges.memory.windows set * 2 ^ shift < 2 ^ 32)
    (holds : NativeMemory.InitializationGateHolds shift challenges (withSetupAddresses setupLayout row physical)
      (values row) relation) :
    gate.Sat layout challenges.memory raw (fun port row => values row (Extract.address port)) row := by
  cases relation <;> cases gate <;> simp only [correspond, Bool.false_eq_true] at decoded
  case TrivialProduct.product input output out left right =>
    simp only [Bool.and_eq_true, beq_iff_eq] at decoded
    obtain ⟨inputs, rfl⟩ := decoded
    simp only [NativeMemory.InitializationGateHolds, NativeMemory.GateHolds, inputs] at holds
    exact holds
  case CopyInExtensionField.copy input output out source =>
    simp only [Bool.and_eq_true, beq_iff_eq] at decoded
    obtain ⟨rfl, rfl⟩ := decoded
    exact holds
  case InitsOrTeardownsInitialPair.pair mode setup output sets out left right =>
    simp only [Bool.and_eq_true, beq_iff_eq] at decoded
    obtain ⟨⟨⟨⟨inputs, setIndices⟩, rfl⟩, leftMatches⟩, rightMatches⟩ := decoded
    simp only [NativeMemory.InitializationGateHolds, setIndices] at holds
    obtain ⟨leftValue, rightValue, leftTuple, rightTuple, product⟩ := holds
    rw [tuple_factor layout setupLayout words shift stride challenges physical raw row bank mode setup 0 left
      inputs leftMatches (bounded _ List.mem_cons_self), Option.some.injEq] at leftTuple
    rw [tuple_factor layout setupLayout words shift stride challenges physical raw row bank mode setup 1 right
      inputs rightMatches (bounded _ (List.mem_cons_of_mem _ List.mem_cons_self)), Option.some.injEq] at rightTuple
    simp only [Gate.Sat]
    rw [product, ← leftTuple, ← rightTuple]

/-- Compiled acceptance on every row gives the tree semantics of the extracted graph. -/
theorem accepted_of_compiled (artifact : Artifact) (circuit : Circuit) (setupLayout : InitsTeardowns.Layout)
    (words : setupLayout.wordBits = 2) (stride : artifact.layout.stride = 2 ^ InitsTeardowns.topShift setupLayout)
    (sourced : ∀ gate ∈ artifact.gates.toList, ∃ relation ∈ compiledRelations circuit, correspond relation gate = true)
    (challenges : NativeMemory.Challenges E)
    (bounded : ∀ gate ∈ artifact.gates.toList, ∀ set ∈ pairSets gate,
      challenges.memory.windows set * 2 ^ InitsTeardowns.topShift setupLayout < 2 ^ 32)
    (physical : Nat → GKRAddress → F) (values : Nat → GKRAddress → E)
    (raw : Raw babyBearModulus) (bank : ∀ row column, physical row (.BaseLayerMemory column) = raw row column)
    (holds : ∀ row < artifact.layout.rows, NativeMemory.InitializationHolds circuit setupLayout challenges
      (withSetupAddresses setupLayout row (physical row)) (values row)) :
    Accepted artifact challenges.memory raw (fun port row => values row (Extract.address port)) := by
  intro row gate member
  obtain ⟨relation, relationMember, decoded⟩ := sourced gate member
  exact gate_sat artifact.layout setupLayout words _ stride challenges (physical row) values raw row (bank row)
    decoded (bounded gate member) (holds_member (holds row row.isLt) relationMember)

end Airbender.InitsTeardowns.Native.Proofs
