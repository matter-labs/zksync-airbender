module
import Human.Compiler.NativeSetups.AddSub
import Human.Compiler.NativeSetups.Bigint
import Human.Compiler.NativeSetups.BlakeG
import Human.Compiler.NativeSetups.InitsTeardowns
import Human.Compiler.NativeSetups.JumpBranch
import Human.Compiler.NativeSetups.Keccak
import Human.Compiler.NativeSetups.MulDiv
import Human.Compiler.NativeSetups.ShiftBinop
import Human.Compiler.NativeSetups.SubwordMemory
import Human.Compiler.NativeSetups.Unified
import Human.Compiler.NativeSetups.WordMemory
import Human.Circuits.Blake2Round.SetupArtifact
import Human.Circuits.KeccakSplit.ColumnParity.SetupArtifact
import Human.Circuits.KeccakSplit.ThetaRho.SetupArtifact
import Human.Circuits.KeccakSplit.Chi5.SetupArtifact

meta section

open Lean Elab Command Airbender.Import.Setup

/- The emitted setup has exactly the fields the claims read. -/
run_cmd do
  let constructor ← getConstInfoCtor ``SetupData.mk
  unless constructor.numFields = 4 do
    throwError "The emitted setup contains unused fields."

/- Every imported setup is emitted as `SetupData`. -/
run_cmd do
  for name in [
      `Airbender.Compiler.NativeSetups.bigintSetup,
      `Airbender.Compiler.NativeSetups.blakeGSetup,
      `Airbender.Compiler.NativeSetups.keccakSetup,
      `Airbender.Compiler.NativeSetups.mulDivSetup,
      `Airbender.Compiler.NativeSetups.addSubSetup,
      `Airbender.Compiler.NativeSetups.jumpBranchSetup,
      `Airbender.Compiler.NativeSetups.subwordMemorySetup,
      `Airbender.Compiler.NativeSetups.wordMemorySetup,
      `Airbender.Compiler.NativeSetups.shiftBinopSetup,
      `Airbender.Compiler.NativeSetups.initsTeardownsSetup,
      `Airbender.Compiler.NativeSetups.unifiedSetup,
      `Airbender.Blake2Round.blake2RoundSetup,
      `Airbender.Keccak.Split.ColumnParity.columnParitySetup,
      `Airbender.Keccak.Split.ThetaRho.thetaRhoSetup,
      `Airbender.Keccak.Split.Chi5.chi5Setup] do
    let info ← getConstInfoDefn name
    unless info.type.isConstOf ``SetupData do
      throwError "Consumed setup data is absent: {name}"
