import Airbender.Proofs.SubwordMemory.Soundness
import Airbender.Proofs.BabyBear
import Airbender.Proofs.SubwordMemory.Trace
import Airbender.Proofs.SubwordMemory.Composition

namespace Airbender.SubwordMemory
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- RAM LB/LBU/LH/LHU/SB/SH execute the public program in native time order
    and reach its terminal PC and cell values. Global history supplies all input
    bounds and reads; the public boundary contains no per-row assumptions. -/
theorem ram_trace_soundness {p : Nat} [Fact p.Prime]
    (hp : 33554432 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {program : List ProgramEntry} (inputs : RAMInputs trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (SailStep program) trace initial cells :=
  Proofs.ram_trace_execution hp inverse inputs accepted decoded


omit [MemoryPlatform SailRV32.exception] in
/-- Actual public Sail decoding binds native immediate/selector columns;
    native register/memory reads are separate obligations. -/
theorem fetched {p : Nat} [Fact p.Prime] (hp : Arithmetic.limbBase < p)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (member : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before :=
  Proofs.fetched hp image h member

omit [MemoryPlatform SailRV32.exception] in
/-- Imported timestamps enforce four-tick advancement and all three strict
    prior-write comparisons for every selected byte/halfword operation. -/
theorem clocks {setup : Table (ZMod babyBearModulus) (fields 9)} {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup))
    (inputs : Trace.ClockInputs importedConstraintsTraceColumns w) :
    Trace.ClockEffects importedConstraintsTraceColumns w :=
  Proofs.clocks (by decide) (by decide) h inputs
/-- RAM/ROM LB/LBU/LH/LHU and RAM SB/SH agree with native Sail: cell address, exact register
    or memory effects and PC+4. Input, decoder and native transport obligations
    are explicit in `InterfaceAssumptions`; merged writes preserve other bytes. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) (program : Nat → BitVec 32) :
    (circuitModel (p := p) program).SoundnessUnder (InterfaceAssumptions program) spec :=
  Proofs.soundness hp inverse program

theorem babyBear_soundness (program : Nat → BitVec 32) :
    (circuitModel (p := babyBearModulus) program).SoundnessUnder (InterfaceAssumptions program) spec :=
  soundness (by decide) (by decide) program

end Airbender.SubwordMemory
