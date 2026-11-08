module
public import Slop.Deleg.Calls
public import Slop.ISA.RV.Same
public import Slop.ISA.RV.MemSubword
public import Slop.Trace.RVHistory

@[expose] public section

/-! The delegate link, generic part: a worker call's RV post-state is the spec's run of one `.delegate` call
    (`RV.calls`, `RV.Delegation.effect`), up to the spec's PC advance, and a span of such calls is the spec's run of
    the span (`RV.calls (List.replicate n k)`). Memory is compared word by word (`mem_ext_of_words`); the delegation
    memory is RAM at every address, the shadow RAM below `ROM_END` included (`RV.State.delegationRAM`). -/

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs
set_option warningAsError true

/-- RV histories change only registers and RAM: never the PC, the ROM image or the input stream. -/
theorem rv_history_fields {cells : List Cell} {events : List MemoryAccess} {before after : RV.State}
    (history : RVHistory cells events before after) :
    after.pc = before.pc ∧ after.rom = before.rom ∧ after.input = before.input := by
  induction history with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons past cell member address read write ih =>
    unfold Cell.applyRV at write
    split at write
    · cases Option.some.inj write
      exact ih
    · obtain ⟨pc, input⟩ := writeRV_pc write
      exact ⟨pc.trans ih.1, (writeRV_rom write).trans ih.2.1, input.trans ih.2.2⟩

/-- Two byte memories agreeing on every aligned word are equal. -/
theorem mem_ext_of_words {m m' : RV.Word → BitVec 8}
    (words : ∀ a : RV.Word, a.toNat % 4 = 0 → RV.read m a 4 = RV.read m' a 4) : m = m' := by
  funext b
  obtain ⟨j, hjdef⟩ : ∃ j, j = b.toNat % 4 := ⟨_, rfl⟩
  have hj : j < 4 := by omega
  let a := b - BitVec.ofNat 32 j
  have small := b.isLt
  have jval : (BitVec.ofNat 32 j).toNat = j := by simp only [BitVec.toNat_ofNat]; omega
  have aligned : a.toNat % 4 = 0 := by
    simp only [a, BitVec.toNat_sub, jval]
    omega
  have back : a + BitVec.ofNat 32 j = b := by simp only [a, BitVec.sub_add_cancel]
  have left := RV.read_byte m a 4 j hj (le_refl _)
  have right := RV.read_byte m' a 4 j hj (le_refl _)
  rw [back] at left right
  rw [← left, ← right, words a aligned]

/-- One call: if the circuit's post-state `T` agrees with the effect's writes and register update on every register
    and aligned word, the spec's call from `S` is `T` with the spec's PC. -/
theorem call_same {S T : RV.State} {k : RV.DelegationKind} {e : RV.Effect}
    (effect : RV.Delegation.effect k (S.getReg 10) (S.getReg 11) (S.getReg 12) S.mem = some e)
    (alignedWrites : ∀ aw ∈ e.writes, aw.1.toNat % 4 = 0)
    (rom : T.rom = S.rom) (input : T.input = S.input)
    (regs : ∀ r, T.getReg r = if r = e.reg ∧ r ≠ 0 then e.val else S.getReg r)
    (words : ∀ a : RV.Word, a.toNat % 4 = 0 → RV.read T.mem a 4 = RV.read (S.storeAll e.writes).mem a 4) :
    ∃ U, RV.calls [k] S = some U ∧ RV.Same U (T.setPC (S.pc + 4)) := by
  have applied : ∃ U, S.applyEffect e = some U := by
    unfold RV.State.applyEffect
    rw [ite_eq_left (List.all_eq_true.mpr fun aw member => decide_eq_true (alignedWrites aw member))]
    exact ⟨_, rfl⟩
  obtain ⟨U, applyU⟩ := applied
  obtain ⟨mem, pc, inputU, regsU⟩ := RV.applyEffect_some applyU
  refine ⟨U, ?_, ?_⟩
  · simp only [RV.calls, RV.State.delegationRAM, effect, Option.bind_some, applyU]
  · refine ⟨pc, ?_, (RV.applyEffect_rom applyU).trans rom.symm, ?_, inputU.trans input.symm⟩
    · intro r
      rw [regsU r]
      exact (regs r).symm
    · rw [mem]
      exact (mem_ext_of_words words).symm

/-- `RV.calls` respects `RV.Same`. -/
theorem calls_same {ks : List RV.DelegationKind} {s t s' : RV.State} (same : RV.Same s t)
    (run : RV.calls ks s = some s') : ∃ t', RV.calls ks t = some t' ∧ RV.Same s' t' := by
  induction ks generalizing s t with
  | nil => exact ⟨t, rfl, (Option.some.inj run) ▸ same⟩
  | cons k rest ih =>
    have regs := same.2.1
    have mem := same.2.2.2.1
    simp only [RV.calls, RV.State.delegationRAM] at run ⊢
    rw [regs 10, regs 11, regs 12, mem] at run
    cases effect : RV.Delegation.effect k (t.getReg 10) (t.getReg 11) (t.getReg 12) t.mem with
    | none => rw [effect] at run; simp at run
    | some e =>
      rw [effect] at run
      simp only [Option.bind_some] at run ⊢
      cases applyS : s.applyEffect e with
      | none => rw [applyS] at run; simp at run
      | some u =>
        rw [applyS, Option.bind_some] at run
        obtain ⟨v, applyT, sameUV⟩ := RV.SameOpt.some_left (RV.Same.applyEffect same e) applyS
        rw [applyT, Option.bind_some]
        exact ih sameUV run

/-- The PC after `m` calls and one more step is the PC after `m + 1` calls. -/
theorem pc_step (pc : RV.Word) (m : Nat) :
    pc + BitVec.ofNat 32 (4 * m) + 4 = pc + BitVec.ofNat 32 (4 * (m + 1)) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have four : (4 : RV.Word).toNat = 4 := by rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, four]
  omega

/-- A span: if every call, from the chronological circuit state `chron m` (at any PC), is the spec's call landing
    on `chron (m + 1)`, then the spec's run of the `n` calls from `chron 0` is `chron n` with the spec's PC. -/
theorem calls_replicate_link {k : RV.DelegationKind} {n : Nat} (chron : Nat → RV.State)
    (step : ∀ m < n, ∀ x, ∃ U, RV.calls [k] ((chron m).setPC x) = some U ∧
      RV.Same U ((chron (m + 1)).setPC (x + 4))) :
    ∃ s', RV.calls (List.replicate n k) (chron 0) = some s' ∧
      RV.Same s' ((chron n).setPC ((chron 0).pc + BitVec.ofNat 32 (4 * n))) := by
  have general : ∀ m ≤ n, ∃ s', RV.calls (List.replicate m k) (chron 0) = some s' ∧
      RV.Same s' ((chron m).setPC ((chron 0).pc + BitVec.ofNat 32 (4 * m))) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨chron 0, rfl, ?_⟩
      have : (chron 0).setPC ((chron 0).pc + BitVec.ofNat 32 (4 * 0)) = chron 0 := by
        simp [RV.State.setPC]
      rw [this]
      exact RV.Same.refl _
    | succ m ih =>
      intro bound
      obtain ⟨s', run, same⟩ := ih (by omega)
      obtain ⟨U, call, landing⟩ := step m (by omega) ((chron 0).pc + BitVec.ofNat 32 (4 * m))
      obtain ⟨U', call', sameU⟩ := calls_same same.symm call
      refine ⟨U', ?_, ?_⟩
      · rw [RV.calls_replicate_succ, run, Option.bind_some]
        exact call'
      · rw [← pc_step]
        exact sameU.symm.trans landing
  exact general n (le_refl _)

theorem storeAll_setPC (s : RV.State) (x : RV.Word) (ws : List (RV.Word × RV.Word)) :
    (s.setPC x).storeAll ws = (s.storeAll ws).setPC x := by
  induction ws generalizing s with
  | nil => rfl
  | cons aw ws ih => exact ih (s.store aw.1 aw.2 4)

/-- An aligned word outside the `n` words at aligned `pointer` is disjoint from every write of `writesAt`. -/
theorem writesAt_disjoint {n : Nat} (pointer a : RV.Word) (v : Vector RV.Word n)
    (pointerAligned : pointer.toNat % 4 = 0) (fits : pointer.toNat + 4 * n ≤ 2 ^ 32)
    (alignedA : a.toNat % 4 = 0) (outside : ∀ j : Fin n, a ≠ pointer + BitVec.ofNat 32 (4 * j.val)) :
    ∀ aw ∈ RV.writesAt pointer v, aw.1.toNat + 4 ≤ 2 ^ 32 ∧
      (aw.1.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ aw.1.toNat) := by
  have below : a.toNat < pointer.toNat ∨ pointer.toNat + 4 * n ≤ a.toNat := by
    by_contra inside
    have small := a.isLt
    apply outside ⟨(a.toNat - pointer.toNat) / 4, by omega⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  intro aw member
  obtain ⟨j, bound, address⟩ := RV.writesAt_addr pointer v fits aw member
  omega

/-- The `j`-th word of `writesAt pointer v` reads back as `v[j]` when no later write touches the block. -/
theorem read_writesAt_at {n : Nat} (s : RV.State) (pre rest : List (RV.Word × RV.Word)) (pointer : RV.Word)
    (v : Vector RV.Word n) (fits : pointer.toNat + 4 * n ≤ 2 ^ 32)
    (restDisjoint : ∀ aw ∈ rest, aw.1.toNat + 4 ≤ 2 ^ 32 ∧
      (aw.1.toNat + 4 ≤ pointer.toNat ∨ pointer.toNat + 4 * n ≤ aw.1.toNat)) (j : Fin n) :
    RV.read (s.storeAll (pre ++ RV.writesAt pointer v ++ rest)).mem (pointer + BitVec.ofNat 32 (4 * j.val)) 4 =
      v[j] := by
  have words := RV.readWords_storeAll s pre rest pointer v fits restDisjoint
  have entry := congrArg (fun words : Vector RV.Word n => words[j]) words
  simpa only [RV.readWords, Fin.getElem_fin, Vector.getElem_ofFn] using entry

end Airbender.Delegation.Proofs
