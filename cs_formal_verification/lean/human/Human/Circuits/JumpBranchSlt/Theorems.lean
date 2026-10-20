import Human.Circuits.AddSub.Reference
import Human.Circuits.JumpBranchSlt.Branch
import Human.Circuits.JumpBranchSlt.Jump
import Human.Circuits.MulDiv.Model
import Human.Circuits.ShiftBinop.Model
import Human.Helpers.Context.Registries.SubwordMemory
import Human.Helpers.Core.BabyBearPrime
import Human.Helpers.Memory.SailHistory
import Human.Trace.Families.JumpBranchSlt.Execution
import Human.Trace.Families.MulDiv.Execution
import Human.Trace.Families.ShiftBinop.Execution

-- The statements proven in slop/Slop/Final/Circuits/JumpBranchSlt/Theorems.lean (checked by verify.sh).

namespace Airbender.JumpBranchSlt

namespace Comparison

/-- Original Sail execution with register/PC effects. Shared history supplies
    local ranges and reads; public conditions remain visible in the model. -/
def SoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec

def BabyBearSoundnessClaim : Prop :=
  ∀ (trace : Trace.PooledTrace babyBearModulus) (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec

end Comparison

namespace Branch

/-- Original Sail execution with register/PC effects. Shared history supplies
    local ranges and reads; public conditions remain visible in the model. -/
def SoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec

def BabyBearSoundnessClaim : Prop :=
  ∀ (trace : Trace.PooledTrace babyBearModulus) (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry),
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec

end Branch

namespace Jump

/-- Original Sail execution with register/PC effects. Shared history supplies
    local ranges and reads; public conditions remain visible in the model. -/
def SoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry),
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) spec

def BabyBearSoundnessClaim : Prop :=
  ∀ (trace : Trace.PooledTrace babyBearModulus) (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry),
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) spec

end Jump

end Airbender.JumpBranchSlt
