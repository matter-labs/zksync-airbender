module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations
public import Mathlib.Tactic.FinCases
public import Human.Circuits.Blake2Round.Artifact

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Blake2Round/Artifact.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Blake2Round
set_option maxRecDepth 16384
namespace Variables
abbrev controlReadLo := 135
abbrev controlReadHi := 136
abbrev controlWriteLo := 137
abbrev controlWriteHi := 138
def stateReads : Vector (Nat × Nat) 8 := Vector.ofFn fun i => (5 + 4 * i.val, 6 + 4 * i.val)
def extendedReads : Vector (Nat × Nat) 16 := Vector.ofFn fun i => (37 + 4 * i.val, 38 + 4 * i.val)
def messageReads : Vector (Nat × Nat) 16 := Vector.ofFn fun i => (103 + 2 * i.val, 104 + 2 * i.val)
def chainingInputs : Vector (Nat × Nat) 8 :=
  #v[(154, 156), (158, 160), (162, 164), (166, 168),
    (170, 172), (174, 176), (178, 180), (182, 184)]
def preparedState : Vector (Nat × Nat) 16 :=
  #v[(155, 157), (159, 161), (163, 165), (167, 169),
    (171, 173), (175, 177), (179, 181), (183, 185),
    (186, 187), (188, 189), (190, 191), (192, 193),
    (198, 199), (194, 195), (200, 201), (196, 197)]
def scheduledMessage : Vector (Nat × Nat) 16 := Vector.ofFn fun i => (224 + 2 * i.val, 225 + 2 * i.val)
end Variables
end Airbender.Blake2Round
