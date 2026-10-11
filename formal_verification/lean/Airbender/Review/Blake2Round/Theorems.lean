import Airbender.Proofs.Blake2Round.NativeExecution
import Airbender.Proofs.Blake2Round.CallExecution
import Airbender.Proofs.Blake2Round.CompressionBinding
import Airbender.Proofs.Blake2Round.Control
import Airbender.Proofs.Blake2Round.Lookups
import Airbender.Proofs.Blake2Round.Addresses
import Airbender.Proofs.Blake2Round.Preparation
import Airbender.Proofs.Blake2Round.Schedule
import Airbender.Proofs.Blake2Round.Soundness
import Airbender.Proofs.Blake2Round.Finalization
import Airbender.Proofs.Blake2Round.PortAddresses
import Airbender.Proofs.Blake2Round.Row
import Airbender.Proofs.Blake2Round.MemorySoundness
import Airbender.Proofs.BabyBear

namespace Airbender.Blake2Round.Row

/-- Joint local soundness: all components refer to the same imported witness.
    Read the row contract and its source-word, pointer and round-mask interfaces. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec := Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end Airbender.Blake2Round.Row

namespace Airbender.Blake2Round.Control

/-- x12's thirteen-bit high limb and next mask are forced by the artifact. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 8192 ≤ p)
    (setup : Table (ZMod p) (fields 4)) :
    Properties.Soundness (circuitModel setup).relation spec := Proofs.soundness hp setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 4)) :
    Properties.Soundness (circuitModel setup).relation spec := soundness (by decide) setup

end Airbender.Blake2Round.Control

namespace Airbender.Blake2Round.Preparation

/-- The imported equations enforce state initialization and left/right message
    preparation for every control combination. G calls and writeback are separate. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (setup : Table (ZMod p) (fields 4)) :
    Properties.Soundness (circuitModel setup).relation spec := Proofs.soundness hp setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 4)) :
    Properties.Soundness (circuitModel setup).relation spec := soundness (by decide) setup

end Airbender.Blake2Round.Preparation

namespace Airbender.Blake2Round.Schedule

/-- The sixteen G inputs follow the shared SIGMA schedule, under the caller's
    exclusive round mask. This condition is not derived from the local circuit. -/
theorem soundness {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := Proofs.soundness setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 4)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := soundness setup

end Airbender.Blake2Round.Schedule

namespace Airbender.Blake2Round.Mixing

/-- All eight G calls and the allocated extended-state writeback agree with
    Clean's round. Only the stated addition-input and message bounds are assumed. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.mixing_soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder
      (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide) (by decide)

end Airbender.Blake2Round.Mixing

namespace Airbender.Blake2Round.Finalization

/-- All eight chaining writes match final three-way XOR or non-final preservation.
    The caller supplies the round mask; queries derive all final-XOR bounds. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.finalization_soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder
      (InterfaceAssumptions (p := babyBearModulus)) spec := soundness (by decide) (by decide)

/-- Non-final rounds preserve all eight original chaining-state words.
    The final-XOR flag is derived from the round mask and reduction mode. -/
theorem nonfinal_soundness {p : Nat} [Fact p.Prime] :
    (circuitModel (p := p)).SoundnessUnder (NonFinalAssumptions (p := p)) spec :=
  Proofs.nonfinal_soundness

theorem babyBear_nonfinal_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder
      (NonFinalAssumptions (p := babyBearModulus)) spec := nonfinal_soundness

end Airbender.Blake2Round.Finalization

namespace Airbender.Blake2Round.Addresses

/-- Actual JSON ports address all 24 state and 16 message words. Imported
    alignment queries exclude low-limb carry; pointer bounds remain external. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p)
    (compatible : 128 * (-15728640 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec := Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end Airbender.Blake2Round.Addresses

namespace Airbender.Blake2Round.Memory

/-- One extended round in an initialized native memory pool agrees with the
    existing project preparation, Clean mixing, finalization and addresses.
    Shared history derives every source-word and pointer bound. Read the memory
    interface for the public state, modeled table and remaining caller conditions. -/
theorem soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (data : Delegation.MemoryData p)
    (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell) :
    (circuitModel data).SoundnessUnder (InterfaceAssumptions data before cells) Row.spec :=
  Proofs.soundness hp compatible data before cells

theorem babyBear_soundness (data : Delegation.MemoryData babyBearModulus)
    (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell) :
    (circuitModel data).SoundnessUnder (InterfaceAssumptions data before cells) Row.spec :=
  soundness (by decide) (by decide) data before cells

end Airbender.Blake2Round.Memory

namespace Airbender.Blake2Round.Native

/-- Every call in the public seven- or ten-round span matches its existing
    preparation, Clean mixing and finalization references on actual Sail port
    values. Shared history derives the public mode flags, exclusive masks,
    reads and word bounds.
    Whole compression is covered by `compression_soundness`; caller request matching remains open. -/
theorem call_execution [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {flags : Fin 8} (accepted : Delegation.MemoryAccepted data)
    (inputs : CallInputs data initial cells flags) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    CallModes data flags ∧ Delegation.MemoryExecution data initial cells ∧
      ∀ row ∈ data.rows, ∃ round, Memory.RoundMask row.assignment round ∧
        Row.spec (input round row.assignment) (output row.assignment) :=
  Airbender.Blake2Round.Proofs.call_execution hp inverse accepted inputs aligned

/-- The complete extended row matches its existing preparation, Clean eight-G
    round, chaining, control and address references on actual Sail port values.
    Other delegation families may share the history; source/pointer ranges and
    reads are derived internally. The exclusive round mask remains a visible
    caller condition in `OperationInputs`; full compression/caller ABI is separate. -/
theorem operation_execution [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.OperationInputs data before cells control)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeRound →
        ∃ round, Memory.RoundMask row.assignment round ∧ Row.spec (input round row.assignment) (output row.assignment) :=
  Proofs.operation_execution hp inverse accepted inputs aligned

/-- The complete seven or ten round compression reaches its reference output in
    actual Sail RAM. `WordMapping` identifies successful initial/final block
    reads; all word bounds and intermediate reads are proved from matching.
    `CallInputs` retains the public request span and modeled-table boundary. -/
theorem compression_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {flags : Fin 8} (accepted : Delegation.MemoryAccepted data)
    (inputs : CallInputs data initial cells flags) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : Reference.RiscV.Sail.State) (statePointer messagePointer : BitVec 32)
      (input : Compression.State) (message : Vector Arithmetic.Word 16) (output : Compression.State),
      Compression.WordMapping initial after statePointer messagePointer input output message ∧
        Delegation.TraceMapping data initial after cells ∧
        output = Compression.run flags input message :=
  Airbender.Blake2Round.Proofs.compression_binding hp inverse accepted inputs aligned

end Airbender.Blake2Round.Native
