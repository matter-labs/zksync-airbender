import Human.Circuits.UnifiedReduced.WordMemory
import Human.Helpers.UnifiedReduced.NativeROM

namespace Airbender.UnifiedReduced.WordMemory.NativeROM
open Reference.RiscV.Sail Trace

/-- Public inputs for unified LW/SW with readonly ROM. `boot` binds the native
    zero seeds and actual public ROM bytes. Shared history derives operands and
    reads; the ROM query derives the loaded word. Configuration and ordinary
    addresses select the reviewed Sail memory path. LW to x0 is excluded because
    Airbender routes it as a NOP rather than Sail's memory-access instruction. -/
structure InterfaceAssumptions [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry)
    (input : Airbender.WordMemory.Input) (_output : Airbender.WordMemory.Output)
    (_w : Nat → ZMod p) : Prop where
  boot : BootInputs trace initial cells program
  configuration : FlatMemoryConfiguration initial
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  destination : input.store = false → input.rd ≠ zeroRegister

/-- The imported native rows and their logical matching remain the proof target.
    `ROMView.data` interprets zero shadow reads as actual public ROM words;
    its preservation proof supplies the existing word-memory model. The reused
    `TraceMapping` names operands and state position in that physical view. -/
def circuitModel [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) :
    Verification.CircuitModel Airbender.WordMemory.Input Airbender.WordMemory.Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ Decoded trace program ∧
    (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ (ROMView.data initial trace).rows
  represents := WordMemory.TraceMapping (ROMView.data initial trace) initial cells program

end Airbender.UnifiedReduced.WordMemory.NativeROM
