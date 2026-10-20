import Slop.Deleg.Calls

/-! A Keccak delegation call on memory (any of the four CSRs: `keccakCall`): the lanes it writes read back as the
step's result, `x10` advances; a run of calls along a chain of control words (`calls_chain`). -/

namespace RV
open Spec Delegation
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

theorem control_toNat (op x r : Nat) (h : op + 8 * x + 64 * r < 2 ^ 32) : (control op x r).toNat = op + 8 * x + 64 * r := by
  simp only [Delegation.control, BitVec.toNat_ofNat]; omega

theorem keccakCall_ctl (valid : Nat → Nat → Nat → Prop) [∀ op x r, Decidable (valid op x r)]
    (step : Nat → Fin 5 → Nat → Vector Lane 31 → Vector Lane 31) (next : Nat → Nat → Nat → Nat × Nat × Nat)
    (op x r op' x' r' : Nat) (hop : op < 8) (hx : x < 5) (hr : op + 8 * x + 64 * r < 2 ^ 11) (hv : valid op x r)
    (hn : next op x r = (op', x', r')) (p : Word) (hp : Buffer p 248 256) (mem : Word → BitVec 8) :
    keccakCall valid step next (control op x r) p mem = some
      { writes := writesAt p (laneWords (step op ⟨x, hx⟩ r (readLanes mem p 31))), reg := 10, val := control op' x' r' } := by
  obtain ⟨hp1, hp2, -⟩ := hp
  have ht := control_toNat op x r (by omega)
  have e1 : (control op x r).toNat % 8 = op := by rw [ht]; omega
  have e2 : (control op x r).toNat / 8 % 8 = x := by rw [ht]; omega
  have e3 : (control op x r).toNat / 64 = r := by rw [ht]; omega
  unfold keccakCall
  simp only [e1, e2, e3]
  rw [dif_pos ⟨hp1, hp2, by rw [ht]; omega, hx, hv⟩, hn]

theorem lane_split (l : Lane) : l.extractLsb' 32 32 ++ l.extractLsb' 0 32 = l := by
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  split
  · rw [Nat.zero_add, BitVec.getLsbD_eq_getElem]
  · rw [show 32 + (i - 32) = i by omega, BitVec.getLsbD_eq_getElem]

/-- Lanes written as words read back as lanes. -/
theorem readLanes_of_words {n : Nat} (mem : Word → BitVec 8) (p : Word) (S : Vector Lane n)
    (h : readWords mem p (2 * n) = laneWords S) (hp : p.toNat + 8 * n ≤ 2 ^ 32) : readLanes mem p n = S := by
  apply Vector.ext; intro i hi
  have h1 := congrArg (·[2 * i + 1]'(by omega)) h
  have h0 := congrArg (·[2 * i]'(by omega)) h
  simp only [readWords, laneWords, Vector.getElem_ofFn] at h1 h0
  simp only [show (2 * i + 1) / 2 = i by omega, show (2 * i) / 2 = i by omega, show (2 * i + 1) % 2 = 1 by omega,
    show (2 * i) % 2 = 0 by omega, show 4 * (2 * i + 1) = 8 * i + 4 by omega, show 4 * (2 * i) = 8 * i by omega,
    Nat.mul_one, Nat.mul_zero] at h1 h0
  simp only [readLanes, Vector.getElem_ofFn, h1, h0]
  exact lane_split _

/-- The control word of a piece. -/
def ctl (c : Nat × Nat × Nat) : Word := control c.1 c.2.1 c.2.2

/-- One call of kind `k` on piece `(op, x, r)`: the 31 lanes at `x11` become `step`'s, `x10` the next piece's. -/
def OneCall (step : Nat → Fin 5 → Nat → Vector Lane 31 → Vector Lane 31) (next : Nat → Nat → Nat → Nat × Nat × Nat)
    (k : DelegationKind) (op : Nat) (x : Fin 5) (r : Nat) : Prop :=
  ∀ (s : State) (p : Word), Buffer p 248 256 → s.getReg 10 = control op x r → s.getReg 11 = p →
    ∃ t, calls [k] s = some t ∧ readLanes t.mem p 31 = step op x r (readLanes s.mem p 31) ∧
      t.getReg 10 = ctl (next op x r) ∧ ChangesOnly s t p 248 10

theorem oneCall (valid : Nat → Nat → Nat → Prop) [∀ op x r, Decidable (valid op x r)]
    (step : Nat → Fin 5 → Nat → Vector Lane 31 → Vector Lane 31) (next : Nat → Nat → Nat → Nat × Nat × Nat)
    (k : DelegationKind) (hk : ∀ x10 x11 x12 mem, effect k x10 x11 x12 mem = keccakCall valid step next x10 x11 mem)
    (op : Nat) (x : Fin 5) (r : Nat) (hop : op < 8) (hr : op + 8 * x.val + 64 * r < 2 ^ 11) (hv : valid op x r) :
    OneCall step next k op x r := by
  intro s p hp h10 h11
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have he := keccakCall_ctl valid step next op x r _ _ _ hop x.isLt hr hv rfl p ⟨hp1, hp2, hp3⟩ s.mem
  obtain ⟨t, h1, m', ch', r'⟩ := calls_one (k := k) (s := s) (by rw [hk, h10, h11]; exact he) p 248 hp3
    (show (10 : Reg) ≠ 0 by decide)
    (writesAt_in (n := 2 * 31) p _ hp1 (by omega) (by simp only [RAM_END] at hp3 ⊢; omega))
  refine ⟨t, h1, ?_, r', ch'⟩
  apply readLanes_of_words _ _ _ _ (by simp only [RAM_END] at hp3; omega)
  rw [m']
  exact readWords_writesAt s p _ (by simp only [RAM_END] at hp3; omega)

/-- The calls `l` (kind, op, x) follow the control words from `c` to `e` in round `r`. -/
def Chain (next : Nat → Nat → Nat → Nat × Nat × Nat) (r : Nat) :
    Nat × Nat × Nat → List (DelegationKind × Nat × Fin 5) → Nat × Nat × Nat → Prop
  | c, [], e => c = e
  | c, (_, op, x) :: l, e => c = (op, x.val, r) ∧ Chain next r (next op x r) l e

theorem calls_chain (step : Nat → Fin 5 → Nat → Vector Lane 31 → Vector Lane 31)
    (next : Nat → Nat → Nat → Nat × Nat × Nat) (r : Nat) :
    ∀ (l : List (DelegationKind × Nat × Fin 5)) (c e : Nat × Nat × Nat), Chain next r c l e →
      (∀ q ∈ l, OneCall step next q.1 q.2.1 q.2.2 r) →
      ∀ (s : State) (p : Word), Buffer p 248 256 → s.getReg 10 = ctl c → s.getReg 11 = p →
      ∃ t, calls (l.map Prod.fst) s = some t ∧
        readLanes t.mem p 31 = l.foldl (fun S q => step q.2.1 q.2.2 r S) (readLanes s.mem p 31) ∧
        t.getReg 10 = ctl e ∧ ChangesOnly s t p 248 10
  | [], c, e, hc, _, s, p, _, h10, _ => ⟨s, rfl, rfl, by rw [h10, show c = e from hc], .refl _ _ _ _⟩
  | (k, op, x) :: l, c, e, hc, hq, s, p, hp, h10, h11 => by
    obtain ⟨rfl, hc'⟩ := hc
    obtain ⟨t, h1, hl, h10', ch⟩ := hq (k, op, x) List.mem_cons_self s p hp h10 h11
    obtain ⟨u, h2, hl', h10'', ch'⟩ := calls_chain step next r l _ e hc' (fun q hq' => hq q (List.mem_cons_of_mem _ hq'))
      t p hp h10' ((ch.2 11 (by decide)).trans h11)
    refine ⟨u, ?_, by rw [hl', hl, List.foldl_cons], h10'', ch.trans ch'⟩
    rw [List.map_cons, show k :: l.map Prod.fst = [k] ++ l.map Prod.fst from rfl, calls_append, h1, Option.bind_some, h2]

end RV
