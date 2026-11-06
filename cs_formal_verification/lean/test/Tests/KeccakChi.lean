import Slop.Keccak.Claims
import Slop.BabyBear
import Mathlib.Tactic.IntervalCases
import Slop.Keccak.Completeness.Bytes

namespace Tests.KeccakChi
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

private def referenceState : Vector Nat 25 := Vector.ofFn fun i =>
  if i.val % 5 = 2 then
    (#v[0xffffffffffffffff, 0x0123456789abcdef, 0x8080808080808080,
      0xaaaaaaaaaaaaaaaa, 0x5555555555555555] : Vector Nat 5)[i.val / 5]
  else 0

private def control (_ : Fin 4096) : Vector Nat 6 := #v[0, 5, 10, 15, 20, 25]
private abbrev setup : Table (ZMod babyBearModulus) (fields 8) := Keccak.setupTable control
private def stateLane (i : Fin 5) : Nat := referenceState[5 * i.val + 2]
private def andn (a b : Nat) : Nat := (not64 a) &&& b
private def temps (second : Bool) : Vector Nat 3 :=
  if second then #v[andn (stateLane 4) (stateLane 0), andn (stateLane 0) (stateLane 1), 0]
  else #v[andn (stateLane 2) (stateLane 3), andn (stateLane 3) (stateLane 4), 0]
private def reads (second : Bool) : Vector Nat 6 :=
  if second then #v[stateLane 0, stateLane 3, stateLane 4, andn (stateLane 1) (stateLane 2), stateLane 1, 0xfedcba9876543210]
  else #v[stateLane 1, stateLane 2, stateLane 3, stateLane 4, 0, 0]
private def writes (second : Bool) : Vector Nat 6 :=
  if second then #v[stateLane 0 ^^^ andn (stateLane 1) (stateLane 2), stateLane 3 ^^^ andn (stateLane 4) (stateLane 0),
    stateLane 4 ^^^ andn (stateLane 0) (stateLane 1), andn (stateLane 1) (stateLane 2), stateLane 1, 0xfedcba9876543210]
  else #v[stateLane 1 ^^^ andn (stateLane 2) (stateLane 3), stateLane 2 ^^^ andn (stateLane 3) (stateLane 4),
    stateLane 3, stateLane 4, andn (stateLane 1) (stateLane 2), stateLane 1]
private def aWords (second : Bool) : Vector Nat 5 :=
  if second then #v[stateLane 4, stateLane 3, stateLane 0, stateLane 4, stateLane 0] else #v[stateLane 1, stateLane 2, stateLane 1, stateLane 3, stateLane 2]
private def bWords (second : Bool) : Vector Nat 5 :=
  if second then #v[stateLane 0, (temps true)[0], stateLane 1, (temps true)[1], andn (stateLane 1) (stateLane 2)]
  else #v[stateLane 2, stateLane 3, (temps false)[0], stateLane 4, (temps false)[1]]
private def isAndn (second : Bool) (op : Nat) : Bool :=
  if second then op = 0 || op = 2 else op = 0 || op = 1 || op = 3

private def base (second : Bool) (v : Nat) : ZMod babyBearModulus :=
  if v = 0 ∨ v = 70 ∨ v = (if second then 69 else 68) then 1
  else if v = 3 then (if second then 6 else 5)
  else if v = 5 then (if second then 13 else 6)
  else if 7 ≤ v ∧ v < 13 then (5 * (v - 7) : Nat)
  else if h : 15 ≤ v ∧ v < 63 then
    let lane : Fin 6 := ⟨(v - 15) / 8, by omega⟩
    let limb := ((v - 15) % 8) / 4 * 2 + (v - 15) % 2
    let value := if (v - 15) % 4 < 2 then (reads second)[lane] else (writes second)[lane]
    (value / 2 ^ (16 * limb) % 65536 : Nat)
  else if v = 86 then 8192 else if v = 87 then 24640
  else if v = 88 then 41088 else if v = 89 then 57536
  else if h : 90 ≤ v ∧ v < 102 then
    let temporary : Fin 3 := ⟨(v - 90) / 4, by omega⟩
    ((temps second)[temporary] / 2 ^ (16 * ((v - 90) % 4)) % 65536 : Nat)
  else 0

-- Byte query `i` (operation `i / 8`, byte `i % 8`): ANDN or XOR of the operation's two words.
private def bytes (second : Bool) (part : Fin 3) (i : Fin 40) : Nat :=
  let op : Fin 5 := ⟨i.val / 8, by omega⟩
  let a := (aWords second)[op]
  let b := (bWords second)[op]
  Keccak.Proofs.wordByte (if part.val = 0 then a else if part.val = 1 then b
    else if isAndn second op.val then andn a b else a ^^^ b) (i.val % 8)

private def row (second : Bool) : Nat → ZMod babyBearModulus :=
  Keccak.Proofs.bytesRow (base second) (bytes second)

private theorem modes (second : Bool) (j : Fin 7) :
    row second Keccak.Variables.modeColumns[j] = if j = (if second then 6 else 5) then 1 else 0 := by
  cases second <;> fin_cases j <;> decide

private theorem chi_tags (second : Bool) (op : Fin 5) :
    Keccak.Proofs.operationTag (if second then 6 else 5) op = if isAndn second op.val then 39 else 4 := by
  cases second <;> revert op <;> decide

private theorem bytesHold (second : Bool) (i : Fin 40) :
    (Keccak.Proofs.byteQuery setup i).Contains (Verification.environment (row second)) := by
  have tag := Keccak.Proofs.byte_tag_of_mode setup _ (modes second) i
  have byte (part : Fin 3) : row second (Keccak.Proofs.byteColumn part i) =
      (bytes second part i : Nat) := Keccak.Proofs.bytes_row_byte _ _ part i
  rw [chi_tags] at tag
  by_cases selected : isAndn second (i.val / 8)
  · rw [ite_eq_left selected] at tag
    refine Keccak.Proofs.andn_query i _ _ (byte 0) (byte 1) ?_ tag
    rw [byte]; simp only [bytes, selected, ↓reduceIte, Fin.isValue]; rfl
  · rw [ite_eq_right selected] at tag
    refine Keccak.Proofs.xor_query i _ _ (byte 0) (byte 1) ?_ tag
    rw [byte]; simp only [bytes, selected, ↓reduceIte, Fin.isValue, Bool.false_eq_true]; rfl

private theorem controllerHolds (second : Bool) :
    ((FlatOperation.lookups (Keccak.importedConstraints setup)).get
      ⟨1, by rw [Keccak.lookup_count]; decide⟩).Contains (Verification.environment (row second)) := by
  refine Keccak.Proofs.controller_query (key := if second then 2054 else 2053) (by cases second <;> decide) ?_ ?_
  · cases second <;> decide
  · cases second <;> decide

theorem satisfies (second : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row second))
      (Keccak.importedConstraints setup) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · cases second <;> decide
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 42 := by simpa only [Keccak.lookup_count] using hi
    by_cases range : i = 0
    · subst i
      apply Trace.Proofs.range_contains
      cases second <;> decide
    by_cases controller : i = 1
    · subst i
      simpa only [List.get_eq_getElem] using controllerHolds second
    have relation := bytesHold second ⟨i - 2, by omega⟩
    have index : i - 2 + 2 = i := by omega
    simpa only [Keccak.Proofs.byteQuery, List.get_eq_getElem, Fin.val_mk, index] using relation

theorem nativeMapping : Keccak.ChiMapping referenceState (2 : Fin 5) (row false) (row true) := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · intro i; fin_cases i <;> decide
  · decide
  · intro i; fin_cases i <;> decide
  · decide

theorem referenceRow : Keccak.ChiResult referenceState (2 : Fin 5) (row false) (row true) :=
  Keccak.chi_row_soundness (by decide) (satisfies false) (satisfies true) nativeMapping

private theorem reference_nonzero : (Specs.Keccak256.chi referenceState)[2] ≠ 0 := by decide

theorem wrongWriteRejected {first second : Nat → ZMod babyBearModulus}
    (firstHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment first)
      (Keccak.importedConstraints setup))
    (mapping : Keccak.ChiMapping referenceState (2 : Fin 5) first second)
    (wrong : Keccak.writeLane second 0 = 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment second)
      (Keccak.importedConstraints setup) := by
  intro secondHolds
  have result := (Keccak.chi_row_soundness (by decide) firstHolds secondHolds mapping).1 (0 : Fin 5)
  change Keccak.writeLane second 0 = (Specs.Keccak256.chi referenceState)[2] at result
  rw [wrong] at result
  exact reference_nonzero result.symm

end Tests.KeccakChi
