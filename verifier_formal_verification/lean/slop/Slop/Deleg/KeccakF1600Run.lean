import Slop.Deleg.KeccakF1600
import Slop.Deleg.KeccakRun

/-! 361 Keccak-f1600 calls from `x10 = 0` (per round 5 column parity, 5 θ+ρ, 5 χ; then one column parity) are
Keccak-f[1600] (`keccak_f1600_run`). -/

namespace RV
open Spec Delegation
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-- Round `r`'s calls with their kind. -/
def fRound : List (DelegationKind × Nat × Fin 5) :=
  [(.keccakParity, 0, 0), (.keccakParity, 0, 1), (.keccakParity, 0, 2), (.keccakParity, 0, 3),
   (.keccakParity, 0, 4), (.keccakThetaRho, 3, 0), (.keccakThetaRho, 3, 1), (.keccakThetaRho, 3, 2),
   (.keccakThetaRho, 3, 3), (.keccakThetaRho, 3, 4), (.keccakChi5, 5, 0), (.keccakChi5, 5, 1), (.keccakChi5, 5, 2),
   (.keccakChi5, 5, 3), (.keccakChi5, 5, 4)]

theorem fRound_chain (r : Nat) : Chain f1600Next r (0, 0, r) fRound (0, 0, r + 1) := by
  simp [Chain, fRound, f1600Next]

theorem f1600_effect (op : Nat) (k : DelegationKind)
    (hk : ∀ x10 x11 x12 mem, effect k x10 x11 x12 mem = keccakF1600 op x10 x11 mem) :
    ∀ x10 x11 x12 mem, effect k x10 x11 x12 mem = keccakCall (fun op' x r => op' = op ∧ (r < 24 ∨ r = 24 ∧ x = 0 ∧ op = 0))
      f1600Step f1600Next x10 x11 mem := hk

theorem fRound_calls (r : Nat) (hr : r < 24) : ∀ q ∈ fRound, OneCall f1600Step f1600Next q.1 q.2.1 q.2.2 r := by
  intro q hq
  simp only [fRound, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> dsimp only <;>
    first
    | exact oneCall _ _ _ _ (f1600_effect 0 .keccakParity fun _ _ _ _ => rfl) _ _ r (by omega)
        (by omega) ⟨rfl, Or.inl hr⟩
    | exact oneCall _ _ _ _ (f1600_effect 3 .keccakThetaRho fun _ _ _ _ => rfl) _ _ r (by omega)
        (by omega) ⟨rfl, Or.inl hr⟩
    | exact oneCall _ _ _ _ (f1600_effect 5 .keccakChi5 fun _ _ _ _ => rfl) _ _ r (by omega)
        (by omega) ⟨rfl, Or.inl hr⟩

theorem fRound_kinds : fRound.map Prod.fst =
    .replicate 5 .keccakParity ++ .replicate 5 .keccakThetaRho ++ .replicate 5 .keccakChi5 := rfl

theorem fRound_steps (r : Nat) (S : Vector Lane 31) :
    fRound.foldl (fun S q => f1600Step q.2.1 q.2.2 r S) S = fsteps r fRoundCalls S := by
  simp only [fRound, fRoundCalls, fsteps, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append]

theorem f1600_rounds (s : State) (p : Word) (hp : Buffer p 248 256) (h10 : s.getReg 10 = 0) (h11 : s.getReg 11 = p) :
    ∀ n ≤ 24, ∃ t, calls (List.replicate n (.replicate 5 .keccakParity ++ .replicate 5 .keccakThetaRho ++
        .replicate 5 .keccakChi5)).flatten s = some t ∧
      (∃ W, Rep n (fun q => (kB (readLanes s.mem p 25) n)[q]) W (readLanes t.mem p 31)) ∧
      t.getReg 10 = ctl (0, 0, n) ∧ ChangesOnly s t p 248 10
  | 0, _ => ⟨s, rfl, ⟨fun i => (readLanes s.mem p 31)[25 + i.val], fun q => by simp [kB, laneSlot, readLanes],
      fun _ => rfl⟩, by rw [h10]; rfl, .refl _ _ _ _⟩
  | n + 1, hn => by
    obtain ⟨t, h1, ⟨W, hW⟩, t10, ch⟩ := f1600_rounds s p hp h10 h11 n (by omega)
    obtain ⟨u, h2, hl, u10, ch'⟩ := calls_chain f1600Step f1600Next n fRound _ _ (fRound_chain n)
      (fRound_calls n (by omega)) t p hp t10 ((ch.2 11 (by decide)).trans h11)
    rw [fRound_steps] at hl
    obtain ⟨W', hW'⟩ := f1600_round n _ W _ hW
    refine ⟨u, ?_, ⟨W', ?_⟩, u10, ch.trans ch'⟩
    · rw [List.replicate_succ', List.flatten_append, List.flatten_singleton, calls_append, h1, Option.bind_some,
        ← fRound_kinds, h2]
    · rw [hl]; exact hW'

theorem keccak_f1600_run : KeccakF1600Run := by
  intro s p hp h10 h11
  obtain ⟨t, h1, ⟨W, hW⟩, t10, ch⟩ := f1600_rounds s p hp h10 h11 24 le_rfl
  obtain ⟨u, h2, hl, -, ch'⟩ := oneCall _ _ _ _ (f1600_effect 0 .keccakParity fun _ _ _ _ => rfl) 0 0 24 (by omega)
    (by omega) ⟨rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩ t p hp t10 ((ch.2 11 (by decide)).trans h11)
  have hu := par_rep 24 0 _ _ _ hW _ rfl
  rw [← hl] at hu
  exact ⟨u, by rw [f1600Calls, calls_append, h1, Option.bind_some, h2], ch.trans ch', lanes_final _ _ _ _ hu⟩

end RV
