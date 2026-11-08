module
public import Slop.UnifiedReduced.Delegation
public import Slop.UnifiedReduced.ComparisonSoundness
public import Slop.UnifiedReduced.Trace
public import Slop.UnifiedReduced.Values
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Circuits.UnifiedReduced.Binary
public import Human.Circuits.WordMemory.Output
public import Human.Trace.UnifiedReduced.PreparedRoundWindows
public import Slop.AddSub
public import Slop.Arithmetic.ShiftAssembly
public import Slop.Arithmetic.SignExtend
public import Slop.Arithmetic.WordBytes
public import Slop.Arithmetic.WordRotation
public import Slop.Blake2G.CallGroups
public import Slop.Blake2G.PhysicalWords
public import Slop.Delegation.NativeSegments
public import Slop.Delegation.RequestWindows
public import Slop.Delegation.SharedOperations
public import Slop.Delegation.WorkerProjection
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.Keccak.CallPermutation
public import Slop.Trace.BytePorts
public import Slop.Trace.CompositionCore
public import Slop.Trace.ROMView
public import Slop.Trace.WindowCounts
public import Slop.UnifiedReduced.Binary
public import Slop.UnifiedReduced.WordROM
public import Human.Circuits.Bigint.PointerABI
public import Slop.Bigint.Addresses

@[expose] public section

namespace Airbender.UnifiedReduced


open Airbender.Reference.RiscV


theorem native_clocks {p : Nat} [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Trace.UnifiedTrace p} (accepted : Trace.Accepted trace)
    (boundary : Trace.ClockBoundary trace) :
    ∀ row ∈ trace.rows, Trace.ClockEffects row.columns row.assignment :=
  Trace.Proofs.trace_clocks hp inverse accepted boundary


end Airbender.UnifiedReduced
