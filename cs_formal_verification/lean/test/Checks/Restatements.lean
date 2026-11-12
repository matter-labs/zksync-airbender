module
public import Proven.Final.Circuits.AddSub.RVTheorems
public import Proven.Final.Circuits.JumpBranchSlt.RVTheorems
public import Proven.Final.Circuits.MulDiv.RVTheorems
public import Proven.Final.Circuits.ShiftBinop.RVTheorems
public import Proven.Final.Circuits.SubwordMemory.RVTheorems
public import Proven.Final.Circuits.WordMemory.RVTheorems

@[expose] public section

/-! Equivalence checks for the reviewed claim statements. -/

namespace Checks.Restatements
open Airbender Airbender.Trace

/-- The shape of the per-row RV claims: for every public setup meeting `assumptions`, every row the model relates
    satisfies `conclusion`. -/
def OldRVRowSoundness {Input Output : Type} (family : PooledFamily) (before : Input → RV.State)
    (instruction : Input → RV.Instr) (words : Input → Output → (Nat → ZMod babyBearModulus) → Prop)
    (assumptions : PooledTrace babyBearModulus → RV.State → List Cell → List RVPooledProgramEntry → Prop)
    (conclusion : Input → Output → Prop) : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    assumptions trace initial cells program →
    ∀ input output w, (rvRowModel family before instruction words trace initial cells program).relation input output w →
      conclusion input output

/-- The assumptions of a per-row RV claim can be met (lean-strategies 3.3): some public setup meeting `assumptions`
    has a row of `family` that the model relates to some input and output. -/
def OldRVRowSatisfiable {Input Output : Type} (family : PooledFamily) (before : Input → RV.State)
    (instruction : Input → RV.Instr) (words : Input → Output → (Nat → ZMod babyBearModulus) → Prop)
    (assumptions : PooledTrace babyBearModulus → RV.State → List Cell → List RVPooledProgramEntry → Prop) : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) (input : Input) (output : Output) (w : Nat → ZMod babyBearModulus),
    assumptions trace initial cells program ∧
      (rvRowModel family before instruction words trace initial cells program).relation input output w

/-- A per-row RV claim: `OldRVRowSoundness`, and its assumptions can be met (`OldRVRowSatisfiable`). -/
def OldRVRowClaim {Input Output : Type} (family : PooledFamily) (before : Input → RV.State)
    (instruction : Input → RV.Instr) (words : Input → Output → (Nat → ZMod babyBearModulus) → Prop)
    (assumptions : PooledTrace babyBearModulus → RV.State → List Cell → List RVPooledProgramEntry → Prop)
    (conclusion : Input → Output → Prop) : Prop :=
  OldRVRowSoundness family before instruction words assumptions conclusion ∧
    OldRVRowSatisfiable family before instruction words assumptions

end Checks.Restatements

namespace Airbender.AddSub.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .addSub RVInput.before rvInstruction RVWordMapping RVInterfaceAssumptions fun input output =>
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .addSub RVInput.before rvInstruction RVWordMapping RVInterfaceAssumptions := Iff.rfl

end Airbender.AddSub.Restatement

namespace Airbender.MulDiv.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .mulDiv RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs fun input output =>
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .mulDiv RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs := Iff.rfl

end Airbender.MulDiv.Restatement

namespace Airbender.ShiftBinop.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .shiftBinop RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs fun input output =>
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .shiftBinop RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs := Iff.rfl

end Airbender.ShiftBinop.Restatement

namespace Airbender.SubwordMemory.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .subwordMemory RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs fun input output =>
    output.cell.toBitVec.toNat = (input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4 ∧
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' (if input.store then
          (input.before.store output.cell.toBitVec output.data.toBitVec 4).setPC output.pc.toBitVec
        else (input.before.setReg input.rd output.data.toBitVec).setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .subwordMemory RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs := Iff.rfl

end Airbender.SubwordMemory.Restatement

namespace Airbender.WordMemory.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .wordMemory RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs fun input output =>
    output.address.toBitVec = input.source.toBitVec + input.immediate.toBitVec ∧
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' (if input.store then
          (input.before.store output.address.toBitVec output.data.toBitVec 4).setPC output.pc.toBitVec
        else (input.before.setReg input.rd output.data.toBitVec).setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .wordMemory RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs := Iff.rfl

end Airbender.WordMemory.Restatement

namespace Airbender.JumpBranchSlt.Comparison.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .jumpBranchSlt RVInput.before rvInstruction RVWordMapping RVTraceInputs fun input output =>
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .jumpBranchSlt RVInput.before rvInstruction RVWordMapping RVTraceInputs := Iff.rfl

end Airbender.JumpBranchSlt.Comparison.Restatement

namespace Airbender.JumpBranchSlt.Branch.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .jumpBranchSlt RVInput.before rvInstruction RVWordMapping RVTraceInputs fun input output =>
    ∃ s', RV.step input.before = some s' ∧ RV.Same s' (input.before.setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .jumpBranchSlt RVInput.before rvInstruction RVWordMapping RVTraceInputs := Iff.rfl

end Airbender.JumpBranchSlt.Branch.Restatement

namespace Airbender.JumpBranchSlt.Jump.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .jumpBranchSlt RVInput.before rvInstruction RVWordMapping RVTraceInputs fun input output =>
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .jumpBranchSlt RVInput.before rvInstruction RVWordMapping RVTraceInputs := Iff.rfl

end Airbender.JumpBranchSlt.Jump.Restatement
