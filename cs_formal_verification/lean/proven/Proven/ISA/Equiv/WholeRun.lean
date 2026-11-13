import Human.ISA.Sail.WholeRun
import Proven.ISA.Equiv.StepIsAirbender

open Sail SailRV32 SailRV32.Functions Human
namespace Proven.Equiv

/-- Compose the proved single-step equivalence by induction on the execution length. -/
theorem run_is_airbender : Airbender.RunIsAirbenderClaim := by
  intro n
  induction n with
  | zero =>
    intro s s' machine agreement run
    have same : s = s' := Option.some.inj run
    exact ⟨machine, rfl, same ▸ agreement⟩
  | succ n ih =>
    intro s s' machine agreement run
    obtain ⟨next, first, rest⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨middle, step, middleAgreement⟩ := step_is_airbender.1 s next machine agreement first
    obtain ⟨finish, tail, finishAgreement⟩ := ih next s' middle middleAgreement rest
    exact ⟨finish, by simp only [Airbender.Machine.run, step, Option.bind_some, tail], finishAgreement⟩

/-- Copy architectural values into Sail and retain every fixed configuration register. -/
noncomputable def bootMachine (s : RV.State) : Airbender.Machine :=
  ⟨⟨(fun register => if Airbender.writtenByProgram register then match register with
      | .PC => s.pc
      | .x1 => s.getReg 1
      | .x2 => s.getReg 2
      | .x3 => s.getReg 3
      | .x4 => s.getReg 4
      | .x5 => s.getReg 5
      | .x6 => s.getReg 6
      | .x7 => s.getReg 7
      | .x8 => s.getReg 8
      | .x9 => s.getReg 9
      | .x10 => s.getReg 10
      | .x11 => s.getReg 11
      | .x12 => s.getReg 12
      | .x13 => s.getReg 13
      | .x14 => s.getReg 14
      | .x15 => s.getReg 15
      | .x16 => s.getReg 16
      | .x17 => s.getReg 17
      | .x18 => s.getReg 18
      | .x19 => s.getReg 19
      | .x20 => s.getReg 20
      | .x21 => s.getReg 21
      | .x22 => s.getReg 22
      | .x23 => s.getReg 23
      | .x24 => s.getReg 24
      | .x25 => s.getReg 25
      | .x26 => s.getReg 26
      | .x27 => s.getReg 27
      | .x28 => s.getReg 28
      | .x29 => s.getReg 29
      | .x30 => s.getReg 30
      | .x31 => s.getReg 31
      | other => Airbender.resetState.regs other
      else Airbender.resetState.regs register),
    fun address => s.loadView (BitVec.ofNat 32 address)⟩, s.mem, s.input⟩

/-- The machine register bank has every public architectural value. -/
theorem boot_registers (s : RV.State) (index : RV.Reg) :
    Airbender.getReg (bootMachine s).sail index = s.getReg index := by
  rw [reg_eq]
  obtain ⟨⟨n, bound⟩⟩ := index
  interval_cases n <;> rfl

/-- Every public RV state has an agreeing configured machine. -/
theorem agree_exists : Airbender.AgreeExistsClaim := by
  intro s
  refine ⟨bootMachine s, ⟨?_, rfl, boot_registers s, ?_⟩, fun _ _ => rfl, rfl⟩
  · intro register fixed
    change (if Airbender.writtenByProgram register then _ else Airbender.resetState.regs register) = _
    rw [fixed]
    rfl
  · intro address
    change s.loadView (BitVec.ofNat 32 address.toNat) = s.loadView address
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Fetch returns the same state for every supported aligned instruction in ROM. -/
theorem fetch_keeps_configured : Airbender.FetchKeepsConfiguredClaim := by
  intro state word instruction result state' configured aligned inROM bytes decoded fetched
  have unchanged := fetch_rom state configured aligned inROM (bytes ▸ decode_not_rvc decoded)
  rw [unchanged] at fetched
  have same := (EStateM.Result.ok.inj fetched).2
  exact same ▸ configured

/-- Agreement transports every tracked architectural cell. -/
theorem read_cell_agrees {s : RV.State} {machine : Airbender.Machine}
    (agreement : Airbender.Agree s machine) (cell : Airbender.Trace.Cell) :
    machine.readCell cell = cell.readRV s := by
  cases cell with
  | register index => exact congrArg some (agreement.1.2.2.1 index)
  | ram address =>
    simp only [Airbender.Machine.readCell, Airbender.Trace.Cell.readRV,
      ramView_eq agreement.1 agreement.2.1]

/-- An accepted RV run has a machine-level terminal state and the same tracked values. -/
theorem sail_realizes {Kind : Type} [Airbender.Trace.CircuitLayout Kind] {p : Nat} [_root_.Fact p.Prime]
    {trace : Airbender.Trace.Data p Kind} {initial : RV.State} {cells : List Airbender.Trace.Cell}
    (realizes : Airbender.Trace.RVRealizes trace initial cells) :
    Airbender.Trace.SailRealizes trace initial cells := by
  obtain ⟨machine, agreement⟩ := agree_exists initial
  obtain ⟨n, after, run, terminal, memory⟩ := realizes
  obtain ⟨finish, executed, finishAgreement⟩ := run_is_airbender n initial after machine agreement run
  refine ⟨machine, finish, n, agreement, executed, finishAgreement.1.2.1.trans terminal, ?_⟩
  intro sink member
  obtain ⟨cell, included, address, value⟩ := memory sink member
  exact ⟨cell, included, address, (read_cell_agrees finishAgreement cell).trans value⟩

end Proven.Equiv
