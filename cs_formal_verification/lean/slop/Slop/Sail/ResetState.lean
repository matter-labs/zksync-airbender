import Slop.Sail.ResetRun
import Slop.Sail.DecoderFrame

/-! `resetMachine` (every register at its reset value) is `Configured`; on every `Configured` state the
decoder returns `decodeOnReset`'s result (`decode_on_reset_run`). Fixtures build on `resetMachine` and
compute `decodeOnReset` with the kernel (`decode_on_reset_of_kernel`). -/

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail Configuration

set_option maxRecDepth 100000

private noncomputable abbrev resetInsert (regs : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType) (n : Nat) :=
  regs.insert (SailRV32.Register.ofNat n) (resetState.regs (SailRV32.Register.ofNat n))

private theorem fold_reset_get (r : SailRV32.Register) :
    ∀ (l : List Nat) (m : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType),
      (m.get? r = none ∨ m.get? r = some (resetState.regs r)) →
      (l.foldl resetInsert m).get? r =
        if r ∈ l.map SailRV32.Register.ofNat then some (resetState.regs r) else m.get? r
  | [], m, _ => by simp
  | n :: rest, m, inv => by
    rw [List.foldl_cons, fold_reset_get r rest _ ?inv]
    case inv =>
      by_cases same : SailRV32.Register.ofNat n = r
      · subst same; right; simp [resetInsert]
      · simp only [resetInsert, Std.ExtDHashMap.get?_insert, beq_iff_eq, same, ↓reduceDIte]; exact inv
    by_cases same : SailRV32.Register.ofNat n = r
    · subst same; simp [resetInsert]
    · by_cases inside : r ∈ rest.map SailRV32.Register.ofNat
      · simp [inside]
      · have notHere : r ∉ (n :: rest).map SailRV32.Register.ofNat := by
          simp only [List.map_cons, List.mem_cons, not_or]
          exact ⟨Ne.symm same, inside⟩
        rw [ite_eq_right_iff.mpr (fun h => absurd h inside), ite_eq_right_iff.mpr (fun h => absurd h notHere)]
        simp only [resetInsert, Std.ExtDHashMap.get?_insert, beq_iff_eq, same, ↓reduceDIte]

private theorem mem_reset_registers (r : SailRV32.Register) :
    r ∈ (List.range 256).map SailRV32.Register.ofNat := by
  refine List.mem_map.mpr ⟨r.ctorIdx, List.mem_range.mpr ?_, ?_⟩
  · cases r <;> decide
  · cases r <;> rfl

theorem reset_machine_get (r : SailRV32.Register) :
    resetMachine.regs.get? r = some (resetState.regs r) := by
  have h := fold_reset_get r (List.range 256) ∅ (Or.inl Std.ExtDHashMap.get?_empty)
  simp only [mem_reset_registers r, ite_true] at h
  exact h

theorem configured_reset_machine : Configured resetMachine := fun r _ => reset_machine_get r

/-- On a `Configured` state the decoder returns `decodeOnReset`'s result and keeps the state. -/
theorem decode_on_reset_run {bits : BitVec 32} {state : State} (configured : Configured state)
    {instruction : SailRV32.instruction} (decoded : decodeOnReset bits = some instruction) :
    run (SailRV32.Functions.encdec_backwards bits) state = .ok instruction state := by
  unfold decodeOnReset at decoded
  split at decoded
  · rename_i value after result
    cases decoded
    exact (decoded_misa_frame bits result).2 state (configured_same configured_reset_machine configured)
  · cases decoded

/-- `decodeOnReset` from kernel facts: the decoder reads only configuration registers and decodes on the
    reset state. -/
theorem decode_on_reset_of_kernel {bits : BitVec 32} {instruction : SailRV32.instruction} {after : SailState}
    (reads : ConfigReads resetState (SailRV32.Functions.encdec_backwards bits) = true)
    (decoded : runSail (SailRV32.Functions.encdec_backwards bits) resetState = .ok instruction after) :
    decodeOnReset bits = some instruction := by
  unfold decodeOnReset
  rw [decode_configured configured_reset_machine reads decoded]

/-- Inserting a register a program writes keeps a state `Configured`. -/
theorem Configured.insert {state : State} (configured : Configured state) {key : SailRV32.Register}
    (written : writtenByProgram key = true) (value : SailRV32.RegisterType key) :
    Configured { state with regs := state.regs.insert key value } := by
  intro r outside
  have distinct : key ≠ r := by
    rintro rfl
    rw [written] at outside
    cases outside
  simp only [Std.ExtDHashMap.get?_insert, beq_iff_eq, distinct, ↓reduceDIte]
  exact configured r outside

/-- Memory does not affect `Configured`. -/
theorem Configured.with_mem {state : State} (configured : Configured state)
    (mem : Std.ExtHashMap Nat (BitVec 8)) : Configured { state with mem := mem } := configured

end Airbender.Reference.RiscV.Sail
