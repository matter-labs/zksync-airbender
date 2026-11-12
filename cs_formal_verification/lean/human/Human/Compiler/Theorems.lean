module
public import Human.Compiler.Captures.AddSub
public import Human.Compiler.Captures.Bigint
public import Human.Compiler.Captures.BlakeG
public import Human.Compiler.Captures.BlakeRound
public import Human.Compiler.Captures.JumpBranch
public import Human.Compiler.Captures.Keccak
public import Human.Compiler.Captures.MulDiv
public import Human.Compiler.Captures.ShiftBinop
public import Human.Compiler.Captures.SubwordMemory
public import Human.Compiler.Captures.Unified
public import Human.Compiler.Captures.WordMemory
public import Human.Circuits.AddSub.Artifact
public import Human.Circuits.Bigint.Artifact
public import Human.Circuits.Blake2G.Artifact
public import Human.Circuits.Blake2Round.Artifact
public import Human.Circuits.JumpBranchSlt.Artifact
public import Human.Circuits.Keccak.Artifact
public import Human.Circuits.MulDiv.Artifact
public import Human.Circuits.ShiftBinop.Artifact
public import Human.Circuits.SubwordMemory.Artifact
public import Human.Circuits.UnifiedReduced.Artifact
public import Human.Circuits.WordMemory.Artifact

@[expose] public section

namespace Airbender.Compiler

/-- The add-sub cached capture has the existing constraint description. Only its compiled layers differ. -/
def AddSubCachedDescriptionClaim : Prop :=
  { Captures.AddSub.imported.circuit with layers := AddSub.importedCircuit.layers } =
    AddSub.importedCircuit

/-- The bigint cached capture has the existing constraint description. Only its compiled layers differ. -/
def BigintCachedDescriptionClaim : Prop :=
  { Captures.Bigint.imported.circuit with layers := Bigint.importedCircuit.layers } =
    Bigint.importedCircuit

/-- The blake-g cached capture has the existing constraint description. Only its compiled layers differ. -/
def BlakeGCachedDescriptionClaim : Prop :=
  { Captures.BlakeG.imported.circuit with layers := Blake2G.importedCircuit.layers } =
    Blake2G.importedCircuit

/-- The blake-round cached capture has the existing constraint description. Only its compiled layers differ. -/
def BlakeRoundCachedDescriptionClaim : Prop :=
  { Captures.BlakeRound.imported.circuit with layers := Blake2Round.importedCircuit.layers } =
    Blake2Round.importedCircuit

/-- The jump-branch cached capture has the existing constraint description. Only its compiled layers differ. -/
def JumpBranchCachedDescriptionClaim : Prop :=
  { Captures.JumpBranch.imported.circuit with layers := JumpBranchSlt.importedCircuit.layers } =
    JumpBranchSlt.importedCircuit

/-- The keccak cached capture has the existing constraint description. Only its compiled layers differ. -/
def KeccakCachedDescriptionClaim : Prop :=
  { Captures.Keccak.imported.circuit with layers := Keccak.importedCircuit.layers } =
    Keccak.importedCircuit

/-- The mul-div cached capture has the existing constraint description. Only its compiled layers differ. -/
def MulDivCachedDescriptionClaim : Prop :=
  { Captures.MulDiv.imported.circuit with layers := MulDiv.importedCircuit.layers } =
    MulDiv.importedCircuit

/-- The shift-binop cached capture has the existing constraint description. Only its compiled layers differ. -/
def ShiftBinopCachedDescriptionClaim : Prop :=
  { Captures.ShiftBinop.imported.circuit with layers := ShiftBinop.importedCircuit.layers } =
    ShiftBinop.importedCircuit

/-- The subword-memory cached capture has the existing constraint description. Only its compiled layers differ. -/
def SubwordMemoryCachedDescriptionClaim : Prop :=
  { Captures.SubwordMemory.imported.circuit with layers := SubwordMemory.importedCircuit.layers } =
    SubwordMemory.importedCircuit

/-- The unified cached capture has the existing constraint description. Only its compiled layers differ. -/
def UnifiedCachedDescriptionClaim : Prop :=
  { Captures.Unified.imported.circuit with layers := UnifiedReduced.importedCircuit.layers } =
    UnifiedReduced.importedCircuit

/-- The word-memory cached capture has the existing constraint description. Only its compiled layers differ. -/
def WordMemoryCachedDescriptionClaim : Prop :=
  { Captures.WordMemory.imported.circuit with layers := WordMemory.importedCircuit.layers } =
    WordMemory.importedCircuit

end Airbender.Compiler
