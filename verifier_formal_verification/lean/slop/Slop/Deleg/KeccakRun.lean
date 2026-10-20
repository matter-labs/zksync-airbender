import Slop.Deleg.KeccakRound
import Slop.Deleg.KeccakCalls

/-! 649 Keccak special5 calls from `x10 = 0` are Keccak-f[1600] (`keccak_special5_run`): 24 rounds of 27 calls
(`round_rep`), then the last delayed ι. -/

namespace RV
open Spec Delegation
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

theorem getElem_eq_of_eq {α : Type} {n : Nat} (v : Vector α n) {i j : Nat} (h : i = j) (hi : i < n) :
    v[i] = v[j]'(h ▸ hi) := by subst h; rfl

theorem laneSlot_24 : ∀ p, laneSlot 24 p = p := by decide

theorem readLanes_25 (mem : Word → BitVec 8) (p : Word) (i : Fin 25) :
    (readLanes mem p 25)[i] = (readLanes mem p 31)[i.val] := by simp [readLanes]

/-- Round `r`'s calls with their kind. -/
def s5Round : List (DelegationKind × Nat × Fin 5) := roundCalls.map fun c => (.keccak, c.1, c.2)

theorem s5Round_chain (r : Nat) : Chain special5Next r (0, 0, r) s5Round (0, 0, r + 1) := by
  simp [Chain, s5Round, roundCalls, special5Next]

theorem s5_effect : ∀ x10 x11 x12 mem, effect .keccak x10 x11 x12 mem =
    keccakCall (fun op _ _ => op < 7) special5Step special5Next x10 x11 mem := fun _ _ _ _ => rfl

theorem s5Round_calls (r : Nat) (hr : r < 24) : ∀ q ∈ s5Round, OneCall special5Step special5Next q.1 q.2.1 q.2.2 r := by
  intro q hq
  have hop : q.2.1 < 7 ∧ q.1 = .keccak := by
    simp only [s5Round, roundCalls, List.map_append, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h <;> subst h <;> exact ⟨by decide, rfl⟩
  rw [hop.2]
  exact oneCall _ _ _ _ s5_effect _ _ r (by omega) (by have := q.2.2.isLt; omega) hop.1

theorem s5Round_kinds : s5Round.map Prod.fst = .replicate 27 .keccak := rfl

theorem s5_rounds (s : State) (p : Word) (hp : Buffer p 248 256) (h10 : s.getReg 10 = 0) (h11 : s.getReg 11 = p) :
    ∀ n ≤ 24, ∃ t, calls (.replicate (27 * n) .keccak) s = some t ∧
      (∃ W, Rep n (fun q => (kB (readLanes s.mem p 25) n)[q]) W (readLanes t.mem p 31)) ∧
      t.getReg 10 = ctl (0, 0, n) ∧ ChangesOnly s t p 248 10
  | 0, _ => ⟨s, rfl, ⟨fun i => (readLanes s.mem p 31)[25 + i.val], fun q => by simp [kB, laneSlot, readLanes],
      fun _ => rfl⟩, by rw [h10]; rfl, .refl _ _ _ _⟩
  | n + 1, hn => by
    obtain ⟨t, h1, ⟨W, hW⟩, t10, ch⟩ := s5_rounds s p hp h10 h11 n (by omega)
    obtain ⟨u, h2, hl, u10, ch'⟩ := calls_chain special5Step special5Next n s5Round _ _ (s5Round_chain n)
      (s5Round_calls n (by omega)) t p hp t10 ((ch.2 11 (by decide)).trans h11)
    rw [s5Round, List.foldl_map] at hl
    obtain ⟨W', hW'⟩ := round_rep n (by omega) _ W _ hW
    refine ⟨u, ?_, ⟨W', ?_⟩, u10, ch.trans ch'⟩
    · rw [show 27 * (n + 1) = 27 * n + 27 by omega, ← List.replicate_append_replicate, calls_append, h1,
        Option.bind_some, ← s5Round_kinds, h2]
    · rw [hl]; exact hW'

/-- After the last delayed ι the lanes at `p` are Keccak-f[1600] of `B`. -/
theorem lanes_final (B : Vector Lane 25) (W : Fin 6 → Lane) (mem : Word → BitVec 8) (p : Word)
    (h : Rep 24 (Function.update (fun q => (kB B 24)[q]) (lane 0 0)
      ((kB B 24)[lane 0 0] ^^^ if (0 : Fin 5) = 0 then delayedRC 24 else 0)) W (readLanes mem p 31)) :
    readLanes mem p 25 = keccakF B := by
  refine Eq.trans ?_ (keccakF_kB _)
  apply Vector.ext; intro i hi
  have e0 : i = (laneSlot 24 ⟨i, hi⟩).val := by rw [laneSlot_24]
  have e1 : (readLanes mem p 25)[i] = (readLanes mem p 31)[i] := by simp only [readLanes, Vector.getElem_ofFn]
  refine e1.trans ((getElem_eq_of_eq _ e0 (by omega)).trans ((h.1 ⟨i, hi⟩).trans ?_))
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp [Function.update_apply, iota', lane]
  · simp [Function.update_apply, iota', lane, Fin.ext_iff, Vector.getElem_set, show i ≠ 0 by omega,
      show 0 ≠ i by omega]

theorem keccak_special5_run : KeccakSpecial5Run := by
  intro s p hp h10 h11
  obtain ⟨t, h1, ⟨W, hW⟩, t10, ch⟩ := s5_rounds s p hp h10 h11 24 le_rfl
  obtain ⟨u, h2, hl, -, ch'⟩ := oneCall _ _ _ _ s5_effect 0 0 24 (by omega) (by omega) (by omega) t p hp t10
    ((ch.2 11 (by decide)).trans h11)
  have hu := op0_rep 24 le_rfl 0 _ _ _ hW _ rfl
  rw [← hl] at hu
  exact ⟨u, by rw [show 649 = 27 * 24 + 1 from rfl, ← List.replicate_append_replicate, calls_append, h1,
    Option.bind_some, List.replicate_one, h2], ch.trans ch', lanes_final _ _ _ _ hu⟩

end RV
