import Airbender.Proofs.Sail.RiscV

namespace Tests.ZeroRegister
open Airbender.Reference.RiscV
open Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

private def before : State :=
  { (default : State) with
    regs := (default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType).insert .x1 (123 : BitVec 32) }

/-- ADDI x0,x1,-1: the original operand and immediate are nonzero, while
    Airbender preprocesses both to zero. This was excluded by the old contracts. -/
private def input : Input where
  row := ⟨.addi, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  rs1 := .Regidx 1
  rs2 := .Regidx 0
  rd := zeroRegister
  encodedImmediate := 4095
  encodedUpperImmediate := 0
  before := before

private theorem contract : Contract input := by
  constructor
  · intro _
    refine ⟨123, ?_, ?_⟩
    · change run (SailRV32.readReg .x1) before = .ok (123 : BitVec 32) before
      dsimp [run, SailRV32.readReg, PreSail.readReg, interpretSailEffects,
        FreeM.liftM, interpretInstructionEffect]
      simp [before]
    · intro nonzero
      exact False.elim (nonzero rfl)
  · simp [input]
  · intro nonzero
    exact False.elim (nonzero rfl)
  · intro nonzero
    exact False.elim (nonzero rfl)
  · simp [input]

example : spec input ⟨65535, 65535⟩ := spec_zero_write contract rfl

end Tests.ZeroRegister
