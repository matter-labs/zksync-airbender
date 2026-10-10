import Airbender.Proofs.Blake2G.NativeExecution
import Airbender.Proofs.Blake2G.Soundness
import Airbender.Proofs.Blake2G.MemorySoundness
import Airbender.Proofs.Blake2G.Control
import Airbender.Proofs.Blake2G.Addresses
import Airbender.Proofs.Blake2G.State
import Airbender.Proofs.Blake2G.Row
import Airbender.Proofs.BabyBear

namespace Airbender.Blake2G

namespace Row

/-- Primary active-row claim: controller, complete G state update and six byte
    addresses for one assignment. Memory transport and setup provenance remain
    explicit interfaces; component claims below support reuse and inspection. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end Row

/-- Imported G mixing agrees with Clean's reference, under the four documented
    input bounds. This does not assert control, address or memory-transport soundness. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    (control : Fin 512 → Vector Nat 7) :
    (circuitModel (p := p) control).SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.soundness hp compatible control

theorem babyBear_soundness (control : Fin 512 → Vector Nat 7) :
    (circuitModel (p := babyBearModulus) control).SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide) (by decide) control

namespace Control

/-- The imported controller query enforces the modeled register update and
    all six word indices for active and inactive rows. The eight-bit ABI input
    domain and unproved Rust setup binding are explicit in the model. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 512 ≤ p) :
    Properties.Soundness (circuitModel (p := p)).relation spec :=
  Proofs.soundness hp

theorem babyBear_soundness :
    Properties.Soundness (circuitModel (p := babyBearModulus)).relation spec :=
  soundness (by decide)

end Control

namespace Addresses

/-- The six addresses described by imported memory metadata select the modeled
    controller's words within the ABI blocks. Pointer bounds and global memory
    transport remain external; alignment and offset bounds are proved locally. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end Addresses

namespace State

/-- An active row agrees with Clean's G on all sixteen state words, under
    the explicit port/read/frame interface. Selected lanes are proved distinct
    from the modeled controller; global memory enforcement remains external. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end State

namespace Memory

/-- Clean's G reference follows from native constraints and initialized memory
    history. Public initialization, logical matching, caller-clock alignment and
    the modeled G table remain explicit; operand ranges are derived internally. -/
theorem soundness [Fact p.Prime] (hp : 4194304 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1) (data : Delegation.MemoryData p)
    (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell) :
    (circuitModel data).SoundnessUnder (InterfaceAssumptions data before cells) Blake2G.spec :=
  Proofs.soundness hp inverse data before cells

theorem babyBear_soundness (data : Delegation.MemoryData babyBearModulus)
    (before : Reference.RiscV.Sail.State) (cells : List Trace.Cell) :
    (circuitModel data).SoundnessUnder (InterfaceAssumptions data before cells) Blake2G.spec :=
  soundness (by decide) (by decide) data before cells

end Memory

end Airbender.Blake2G

namespace Airbender.Blake2G.Native

/-- Native G reads and writes agree with Clean's original G reference within
    actual Sail memory execution. Other families may share the initialized pool;
    shared operation/history helpers derive every operand bound. The remaining
    inputs are public state/alignment, modeled tables and caller/padding rules.
    Request/controller ABI and whole compression remain separate. -/
theorem operation_execution [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.OperationInputs data before cells control)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeG → Blake2G.spec (input row.assignment) (output row.assignment) :=
  Proofs.operation_execution hp inverse accepted inputs aligned

end Airbender.Blake2G.Native
