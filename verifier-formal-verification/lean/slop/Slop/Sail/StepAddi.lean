import Slop.Sail.StepDemo

/-! `step` on `addi a0, a0, 1` at `0xd8`, via one oracle run of the whole `try_step` with x10 and
minstret left symbolic (they are the only GPR / counter values the step reads or writes). -/

open Sail Sail.ArchSem SailRV32 SailRV32.Functions Human
namespace Slop
open Human Wr


theorem agrees_set_self (K : Known) (s : FState) (hK : K.Agrees s) (r : Register) :
    (K.set r (s.regs r)).Agrees s := by
  refine ⟨fun r' w hw => ?_, fun i b hb => hK.2.1 i b hb, hK.2.2⟩
  unfold Known.set at hw
  dsimp only at hw
  by_cases h : r = r'
  · subst h
    rw [dif_pos rfl] at hw
    cases hw
    rfl
  · rw [dif_neg h] at hw
    exact hK.1 r' w hw

theorem K0_agrees (s : FState) (hs : Sys s) (hpc : s.regs .PC = 0xd8#32)
    (hcode : ∀ i < 4, s.mem (0xd8 + i) = (0x00150513#32).extractLsb' (8 * i) 8) : (K0 s.mem).Agrees s := by
  refine ⟨fun r v hv => ?_, fun i b hb => ?_, rfl⟩
  · unfold K0 at hv
    unfold Known.set at hv
    dsimp only at hv
    by_cases h : Register.PC = r
    · subst h
      rw [dif_pos rfl] at hv
      cases hv
      exact hpc
    · rw [dif_neg h] at hv
      unfold K0base at hv
      simp only at hv
      split at hv
      · cases hv
      · rename_i hvol
        cases hv
        apply hs r
        simpa using hvol
  · unfold K0 at hb
    unfold Known.set at hb
    unfold K0base at hb
    dsimp only at hb
    split at hb
    · rename_i hr
      have hb' := (Option.some.inj hb).symm
      subst hb'
      have h := hcode (i - 0xd8) (by omega)
      rw [show (0xd8 + (i - 0xd8) : Nat) = i by omega] at h
      exact h
    · simp at hb

set_option maxRecDepth 1000000 in
theorem try_step_run (s : FState) :
    (Wr.oracleGo 100000 (Ks s) (try_step 0 false)).map
      (fun p => (p.1, p.2.regs .PC, p.2.regs .x10, p.2.regs .minstret))
    = some (false, some (0xdc#32), some (s.regs .x10 + 1), some (s.regs .minstret + 1)) := by
  kernel_rfl

set_option maxRecDepth 1000000 in
theorem fetch_run (mem : Nat → BitVec 8) :
    (Wr.oracleGo 1000 (K0 mem) (fetch ())).map Prod.fst = some (FetchResult.F_Base 0x00150513#32) := by
  kernel_rfl

set_option maxRecDepth 1000000 in
theorem try_step_wr (s : FState) :
    (Wr.oracleGo 100000 (Ks s) (try_step 0 false)).map (fun p => p.2.wr) =
    some [.written_event_index, .minstret, .PC, .x10, .nextPC, .minstret_increment, .mip, .minstret, .x10, .PC] := by
  kernel_rfl

set_option maxRecDepth 1000000 in
theorem try_step_sysvals (s : FState) :
    (Wr.oracleGo 100000 (Ks s) (try_step 0 false)).map
      (fun p => (p.2.regs .written_event_index, p.2.regs .mip)) =
    some (some (stInit.regs .written_event_index), some (stInit.regs .mip)) := by
  kernel_rfl

set_option maxRecDepth 1000000 in
/-- The oracle run of the whole `try_step` leaves the data memory unchanged (`addi` stores nothing). -/
theorem try_step_data (s : FState) :
    (Wr.oracleGo 100000 (Ks s) (try_step 0 false)).map (fun p => p.2.data) = some s.mem := by
  kernel_rfl

/-- A register the oracle run did not write keeps its value. -/
theorem frame_of_not_written {α : Type} (n : Nat) (K K' : Known) (m : SailM α) (a : α) (s s' : FState)
    (hK : K.Agrees s) (h : Wr.oracleGo n K m = some (a, K')) (hK' : K'.Agrees s')
    (hnone : ∀ r, K'.regs r = none → s'.regs r = s.regs r) (r : Register) (hr : r ∉ K'.wr) :
    s'.regs r = s.regs r := by
  have heq : K'.regs r = K.regs r :=
    Classical.byContradiction fun hne => hr ((Wr.oracleGo_wr n K m a K' h).2 r hne)
  cases hk : K'.regs r with
  | none => exact hnone r hk
  | some v =>
    rw [hK'.1 r v hk]
    rw [heq] at hk
    exact (hK.1 r v hk).symm

theorem step_addi (s : FState) (hs : Sys s) (hpc : s.regs .PC = 0xd8#32)
    (hcode : ∀ i < 4, s.mem (0xd8 + i) = (0x00150513#32).extractLsb' (8 * i) 8) :
    ∃ s', step s = some s' ∧ s'.regs .x10 = s.regs .x10 + 1 ∧ s'.regs .PC = 0xdc#32 ∧
      s'.regs .minstret = s.regs .minstret + 1 ∧ s'.mem = s.mem ∧ Sys s' ∧
      (∀ r, r ≠ .x10 → r ≠ .PC → r ≠ .nextPC → r ≠ .minstret → r ≠ .minstret_increment →
        Volatile r = true → s'.regs r = s.regs r) := by
  have hK0 := K0_agrees s hs hpc hcode
  have hKs : (Ks s).Agrees s := agrees_set_self _ s (agrees_set_self (K0 s.mem) s hK0 .x10) .minstret
  have hcur : current s = some (.ITYPE (1#12, .Regidx 10#5, .Regidx 10#5, .ADDI)) := by
    cases hf : Wr.oracleGo 1000 (K0 s.mem) (fetch ()) with
    | none => have hfr := fetch_run s.mem; simp [hf] at hfr
    | some p =>
      have hp1 : p.1 = FetchResult.F_Base 0x00150513#32 := by simpa [hf] using fetch_run s.mem
      obtain ⟨sf, hsf, -⟩ := Wr.oracleGo_sound 1000 (K0 s.mem) s (fetch ()) p.1 p.2 hK0 hf
      rw [hp1] at hsf
      unfold current
      rw [hsf]
      dsimp only
      rw [demo_runF s hs]
  cases ht : Wr.oracleGo 100000 (Ks s) (try_step 0 false) with
  | none => have htr := try_step_run s; simp [ht] at htr
  | some q =>
    have hq := try_step_run s
    simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨hq1, hqpc, hqx, hqm⟩ := hq
    have hwr := try_step_wr s
    simp only [ht, Option.map_some, Option.some.injEq] at hwr
    have hsv := try_step_sysvals s
    simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsv
    obtain ⟨hsv1, hsv2⟩ := hsv
    obtain ⟨s', hs', hKs', hm', hnone, -⟩ :=
      Wr.oracleGo_sound 100000 (Ks s) s (try_step 0 false) q.1 q.2 hKs ht
    have hdata : q.2.data = s.mem := by simpa [ht] using try_step_data s
    rw [hq1] at hs'
    have hfr := frame_of_not_written 100000 (Ks s) q.2 (try_step 0 false) q.1 s s' hKs ht hKs' hnone
    rw [hwr] at hfr
    refine ⟨s', ?_, hKs'.1 .x10 _ hqx, hKs'.1 .PC _ hqpc, hKs'.1 .minstret _ hqm, hm'.trans hdata, ?_, ?_⟩
    · unfold step
      rw [hcur]
      simp only [Supported, if_true]
      rw [hs']
    · intro r hvol
      by_cases hr : r = .written_event_index
      · subst hr; exact hKs'.1 _ _ hsv1
      by_cases hr2 : r = .mip
      · subst hr2; exact hKs'.1 _ _ hsv2
      rw [hfr r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (h|h|h|h|h|h|h|h|h|h) <;> subst h <;> simp_all [Volatile])]
      exact hs r hvol
    · intro r h1 h2 h3 h4 h5 _
      by_cases hr : r = .written_event_index
      · subst hr; simp [Volatile] at *
      by_cases hr2 : r = .mip
      · subst hr2; simp [Volatile] at *
      exact hfr r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (h|h|h|h|h|h|h|h|h|h) <;> subst h <;> simp_all)

end Slop
