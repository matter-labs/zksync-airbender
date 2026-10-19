import Slop.RV.Halt
import Slop.RV.Input
import Slop.RV.CopyRun
import Human.Theorems

/-! A run that gets stuck never reached the halt loop (which runs forever): what "the program fails" means. And
ROM never changes. -/

namespace RV

/-- `T` is at `zksync_os_finish_error`'s `csrrw x0, cycle, x0`: no next state (Airbender cannot prove the run). -/
def AtFinishError (T : State) : Prop :=
  T.pc.toNat % 4 = 0 ∧ T.pc.toNat + 4 ≤ ROM_END ∧ read T.mem T.pc 4 = 0xc0001073#32

theorem AtFinishError.step_none {T : State} (h : AtFinishError T) : step T = none := by
  rw [step_fetch T _ h.1 h.2.1 h.2.2, show decode 0xc0001073#32 = none by decide +kernel]; rfl

theorem storeAll_rom : ∀ (ws : List (Word × Word)) (s : State), (ws.all fun aw => decide (writable aw.1 4 ∧ aligned aw.1 4)) →
    ∀ b : Word, b.toNat < ROM_END → (s.storeAll ws).mem b = s.mem b
  | [], _, _, _, _ => rfl
  | (a, w) :: ws, s, h, b, hb => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    show ((s.store a w 4).storeAll ws).mem b = s.mem b
    rw [storeAll_rom ws _ h.2 b hb]
    exact write_rom _ _ _ _ h.1.1 _ hb

theorem applyEffect_rom {s t : State} {e : Effect} (h : s.applyEffect e = some t) :
    ∀ b : Word, b.toNat < ROM_END → t.mem b = s.mem b := by
  unfold State.applyEffect at h
  split_ifs at h with hw; cases h
  exact storeAll_rom _ _ hw

/-- No instruction writes ROM. -/
theorem exec_rom {s t : State} {i : Instr} (h : exec s i = some t) : ∀ b : Word, b.toNat < ROM_END → t.mem b = s.mem b := by
  intro b hb
  cases i
  case store n rs2 rs1 off =>
    simp only [exec] at h
    split_ifs at h with hc; cases h
    exact write_rom _ _ _ _ hc.2 _ hb
  case delegate k =>
    simp only [exec] at h
    obtain ⟨e, -, he⟩ := Option.bind_eq_some_iff.mp h
    exact applyEffect_rom he b hb
  all_goals simp only [exec, State.jumpAligned] at h
  all_goals (repeat' split at h) <;> simp_all [Option.map, State.setReg, State.nextInstr, State.setPC] <;>
    (subst_vars; rfl)

theorem step_rom {s t : State} (h : step s = some t) : ∀ b : Word, b.toNat < ROM_END → t.mem b = s.mem b := by
  unfold step at h
  split_ifs at h
  obtain ⟨i, -, hex⟩ := Option.bind_eq_some_iff.mp h
  exact exec_rom hex

theorem run_rom : ∀ (n : Nat) (s t : State), run n s = some t → ∀ b : Word, b.toNat < ROM_END → t.mem b = s.mem b
  | 0, s, t, h, b, _ => by simp only [run, Option.some.injEq] at h; subst h; rfl
  | n + 1, s, t, h, b, hb => by
    obtain ⟨s1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    rw [run_rom n s1 t h b hb, step_rom h1 b hb]

/-- A run that gets stuck (at `T`) never was at the halt loop at `H`. -/
theorem stuck_never_halts (s T : State) (m : Nat) (h : run m s = some T) (hT : step T = none) (H : Word)
    (hal : H.toNat % 4 = 0) (hrom : H.toNat + 4 ≤ ROM_END) (hw : read s.mem H 4 = 0x0000006f#32) :
    ∀ n F, run n s = some F → F.pc ≠ H := by
  intro n F hF hpc
  have hwF : read F.mem F.pc 4 = 0x0000006f#32 := by
    rw [hpc, read_congr F.mem s.mem _ 4 (fun j hj => run_rom n s F hF _ (by bv_omega))]; exact hw
  by_cases hnm : n ≤ m
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [run_add, hF, Option.bind_some] at h
    obtain ⟨F', hF', -⟩ := halt_forever F (by rw [hpc]; exact hal) (by rw [hpc]; exact hrom) hwF (k + 1)
    rw [run_add, h, Option.bind_some, run_succ, hT] at hF'
    cases hF'
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_not_le hnm)
    rw [hk, show m + k + 1 = m + (k + 1) by omega, run_add, h, Option.bind_some, run_succ, hT] at hF
    cases hF

/-- With a wrong Fiat–Shamir claim the program ends at `zksync_os_finish_error` (for the Sail-side transfer). -/
def StuckOnBadClaim (bytes : Array (BitVec 8)) : Prop :=
  ∀ (start : State) (x y0 y1 y2 y3 v0 v1 v2 v3 : Word) (root : Vector Word 8) (path : List Spec.MerkleStep)
    (rest : List Word), start.pc = 0 → ImageLoaded bytes start → RamZero start →
    start.input = x :: y0 :: y1 :: y2 :: y3 :: v0 :: v1 :: v2 :: v3 :: (Spec.pathInput root path ++ rest) →
    path.length ≤ 32 → x.toNat ≤ Spec.P →
    y0.toNat < BabyBearP → y1.toNat < BabyBearP → y2.toNat < BabyBearP → y3.toNat < BabyBearP →
    ¬ (Spec.claimOK #v[x, y0, y1, y2, y3] #v[v0, v1, v2, v3] ∧ Spec.pathOK #v[x, y0, y1, y2, y3] root path) →
    ∃ m W, run m start = some W ∧ AtFinishError W

end RV
