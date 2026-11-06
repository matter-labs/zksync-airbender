import Airbender.Proofs.Trace.ZeroValues
import Airbender.Proofs.Trace.Families.ReducedMachine.ArithmeticDecoder
import Airbender.Proofs.Trace.Families.ReducedMachine.History
import Airbender.Proofs.ReducedMachine.NativeArithmeticPorts

namespace Airbender.ReducedMachine.NativeArithmeticRegisterProofs
open Native Arithmetic Trace Verification
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Native mixed-port addressing and the original decoded zero flag prove x0
    preservation. Readonly aliases retain their actual initialized reads. -/
theorem row_zero_preserving (row : Row mersenne31Modulus NativeReducedFamily)
    {fixed : Table (ZMod mersenne31Modulus) (fields 4)} {entry : ArithmeticProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints fixed))
    (fields : arithmeticDecoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) : RowZeroPreserving row := by
  cases row with
  | mk family w =>
    cases family
    intro port member address reads
    change port ∈ importedConstraintsMemoryPorts at member
    simp [importedConstraintsMemoryPorts] at member
    rcases member with rfl | rfl | rfl
    · exact reads importedConstraintsMemoryPorts[0]
        (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _) address
    · exact reads importedConstraintsMemoryPorts[1]
        (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _) address
    · have destination := NativeArithmeticPortProofs.register_addresses holds fields query 2
      have same : Cell.register entry.data.rd = Cell.register 0 :=
        cell_address_injective (destination.symm.trans address)
      have zero : entry.data.rd = 0 := Cell.register.inj same
      have decoded := NativeArithmeticDecoderProofs.decoded_fields fields query
      have mask := decoded.mask
      have flag : rdZeroFlag w = 1 := by rw [decoded.zero,if_pos zero]
      have write := (NativeArithmeticFieldProofs.write holds entry.data.family mask).2
      have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) write
      have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) write
      simp [flag,arithmeticCandidate] at low high
      change Nat.pair (rdWrite w)[0].val (rdWrite w)[1].val = 0
      rw [low,high]
      rfl

/-- Actual original public decoding derives local preservation for every row. -/
theorem decoded_zero_preserving {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {initial : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : ArithmeticDecodedTrace trace setup) : ZeroPreserving trace := by
  intro row member
  obtain ⟨entry,_,source,query,_⟩ := NativeArithmeticDecoderProofs.trace_decoding image accepted decoded row member
  cases row with
  | mk family w =>
    cases family
    exact row_zero_preserving _ (accepted.constraints _ member) source.fields query

/-- Public seeds and native matching propagate the proved x0 rule through all
    reads and writes. No expected zero read/write is supplied per row. -/
theorem native_zero_writes {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {initial : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (seeds : initialImage initial cells = some trace.initialMemory)
    (decoded : ArithmeticDecodedTrace trace setup) :
    ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0 :=
  zero_writes_of_preserving (by decide) accepted boundary seeds
    (decoded_zero_preserving image accepted decoded)

/-- Unchanged shared Clean-to-Sail realization constructs every state in native
    clock order, retaining actual mixed-port addresses and masked writes. -/
theorem image_row_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {initial : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : ArithmeticDecodedTrace trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row mersenne31Modulus NativeReducedFamily)) (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
        initial after ∧ SailStateMatches cells history after := by
  have boundary := image_clock_boundary (by decide) inputs
  exact native_row_history (by decide) accepted boundary inputs.image inputs.domain aligned
    (native_zero_writes image accepted boundary inputs.image decoded)

end Airbender.ReducedMachine.NativeArithmeticRegisterProofs
