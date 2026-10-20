import Human.Helpers.Context.Registries.Pooled
import Slop.JumpBranchSlt.Trace
import Slop.MulDiv.Trace
import Slop.ShiftBinop.Trace
import Slop.SubwordMemory.Trace

namespace Airbender.Trace.Proofs

/-- Pooled matching reuses the proved clock laws of each imported circuit.
    Every family participates in one global state/access order. -/
instance pooledClockLaws [Fact p.Prime] : ClockLaws PooledFamily p where
  finalBound setup row h := by
    cases row with
    | mk family w =>
      cases family with
      | addSub => exact ClockLaws.finalBound (Kind := Family) setup.wordMemory ⟨.addSub, w⟩ h
      | wordMemory => exact ClockLaws.finalBound (Kind := Family) setup.wordMemory ⟨.wordMemory, w⟩ h
      | jumpBranchSlt => exact ClockLaws.finalBound (Kind := JumpBranchSlt.TraceKind) setup.wordMemory ⟨.jumpBranchSlt, w⟩ h
      | mulDiv => exact ClockLaws.finalBound (Kind := MulDiv.TraceKind) setup.wordMemory ⟨.mulDiv, w⟩ h
      | shiftBinop => exact ClockLaws.finalBound (Kind := ShiftBinop.TraceKind) setup.wordMemory ⟨.shiftBinop, w⟩ h
      | subwordMemory => exact ClockLaws.finalBound (Kind := SubwordMemory.TraceKind) setup.subwordMemory ⟨.subwordMemory, w⟩ h
  advance hp inverse setup row h bound := by
    cases row with
    | mk family w =>
      cases family with
      | addSub => exact ClockLaws.advance (Kind := Family) hp inverse setup.wordMemory ⟨.addSub, w⟩ h bound
      | wordMemory => exact ClockLaws.advance (Kind := Family) hp inverse setup.wordMemory ⟨.wordMemory, w⟩ h bound
      | jumpBranchSlt => exact ClockLaws.advance (Kind := JumpBranchSlt.TraceKind) hp inverse setup.wordMemory ⟨.jumpBranchSlt, w⟩ h bound
      | mulDiv => exact ClockLaws.advance (Kind := MulDiv.TraceKind) hp inverse setup.wordMemory ⟨.mulDiv, w⟩ h bound
      | shiftBinop => exact ClockLaws.advance (Kind := ShiftBinop.TraceKind) hp inverse setup.wordMemory ⟨.shiftBinop, w⟩ h bound
      | subwordMemory => exact ClockLaws.advance (Kind := SubwordMemory.TraceKind) hp inverse setup.subwordMemory ⟨.subwordMemory, w⟩ h bound
  effects hp inverse setup row h inputs := by
    cases row with
    | mk family w =>
      cases family with
      | addSub => exact ClockLaws.effects (Kind := Family) hp inverse setup.wordMemory ⟨.addSub, w⟩ h inputs
      | wordMemory => exact ClockLaws.effects (Kind := Family) hp inverse setup.wordMemory ⟨.wordMemory, w⟩ h inputs
      | jumpBranchSlt => exact ClockLaws.effects (Kind := JumpBranchSlt.TraceKind) hp inverse setup.wordMemory ⟨.jumpBranchSlt, w⟩ h inputs
      | mulDiv => exact ClockLaws.effects (Kind := MulDiv.TraceKind) hp inverse setup.wordMemory ⟨.mulDiv, w⟩ h inputs
      | shiftBinop => exact ClockLaws.effects (Kind := ShiftBinop.TraceKind) hp inverse setup.wordMemory ⟨.shiftBinop, w⟩ h inputs
      | subwordMemory => exact ClockLaws.effects (Kind := SubwordMemory.TraceKind) hp inverse setup.subwordMemory ⟨.subwordMemory, w⟩ h inputs
  portsClocks row := by
    cases row with
    | mk family w =>
      cases family with
      | addSub => exact AddSub.memory_clocks
      | wordMemory => exact WordMemory.memory_clocks
      | jumpBranchSlt => exact JumpBranchSlt.memory_clocks
      | mulDiv => exact MulDiv.memory_clocks
      | shiftBinop => exact ShiftBinop.memory_clocks
      | subwordMemory => exact SubwordMemory.memory_clocks
  offsets row := by cases row with | mk family w => cases family <;> rfl

end Airbender.Trace.Proofs
