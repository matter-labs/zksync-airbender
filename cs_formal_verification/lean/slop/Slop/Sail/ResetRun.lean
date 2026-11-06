import Slop.Sail.PC
import Slop.Sail.Sequential
import Slop.Sail.Configured

/-! Running a register-reading computation on the reset state (`Configuration.runSail` on
`Configuration.resetState`, which the kernel evaluates) decides its run on every `Configured` state, provided
it only reads registers a program never writes (`ConfigReads`, also evaluated by the kernel). -/

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail Configuration
open _root_.Sail.ArchSem

/-- Run on `σ`, the computation only reads registers a program never writes (and performs no other effect). -/
def ConfigReads (σ : SailState) {α : Type} : SailRV32.SailM α → Bool
  | .pure _ => true
  | .impure (.inl (.ok (.regRead r _))) next => !writtenByProgram r && ConfigReads σ (next (σ.regs r))
  | _ => false

theorem config_reads_run {α : Type} (σ : SailState) {state : State}
    (agree : ∀ r, writtenByProgram r = false → state.regs.get? r = some (σ.regs r)) :
    ∀ (m : SailRV32.SailM α) {value : α} {after : SailState},
      ConfigReads σ m = true → runSail m σ = .ok value after → run m state = .ok value state := by
  intro m
  induction m with
  | pure v =>
    intro value after _ result
    cases result
    rfl
  | impure eff next ih =>
    intro value after reads result
    rcases eff with (error | eff) | n
    · simp [ConfigReads] at reads
    · cases eff with
      | regRead r access =>
        simp only [ConfigReads, Bool.and_eq_true, Bool.not_eq_true'] at reads
        have step : runSail (FreeM.impure (.inl (.ok (.regRead r access))) next) σ =
            runSail (next (σ.regs r)) σ := rfl
        rw [step] at result
        have present := agree r reads.1
        have unfold : run (FreeM.impure (.inl (.ok (.regRead r access))) next) state =
            run (next (σ.regs r)) state := by
          dsimp [run, interpretSailEffects, FreeM.liftM, interpretInstructionEffect]
          simp [present, EStateM.run, bind, pure, EStateM.pure, get, getThe, MonadStateOf.get]
        rw [unfold]
        exact ih _ reads.2 result
      | _ => simp [ConfigReads] at reads
    · simp [ConfigReads] at reads

/-- The decoder on a `Configured` state is the decoder on the reset state. -/
theorem decode_configured {bits : BitVec 32} {state : State} (configured : Configured state)
    {instruction : SailRV32.instruction} {after : SailState}
    (reads : ConfigReads resetState (SailRV32.Functions.encdec_backwards bits) = true)
    (decoded : runSail (SailRV32.Functions.encdec_backwards bits) resetState = .ok instruction after) :
    run (SailRV32.Functions.encdec_backwards bits) state = .ok instruction state :=
  config_reads_run resetState configured _ reads decoded

end Airbender.Reference.RiscV.Sail
