import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.ExternalBoundary.Initialization
import Airbender.Proofs.ExternalBoundary.Decoder
import Airbender.Proofs.ExternalBoundary.Requests
import Airbender.Proofs.ExternalBoundary.BigintABI
import Airbender.Proofs.ExternalBoundary.WorkerRAM

namespace Airbender.ExternalBoundary
open Trace

/-- Conditional domain uniqueness under the AIH-334 window-validation interface.
    The source check is tested; correspondence to `Selection.unique` is external. -/
theorem initialization_soundness (selection : Initialization.Selection geometry) :
    ((Initialization.cells selection).map Cell.addressCode).Nodup ∧
    (∀ cell ∈ Initialization.cells selection, cell.Aligned) ∧
    (∀ index, Cell.register index ∈ Initialization.cells selection) :=
  ⟨Initialization.Proofs.addresses_distinct selection,
    Initialization.Proofs.aligned selection, Initialization.Proofs.all_registers selection⟩

/-- Conditional public-program membership under a corrected decoder setup.
    AIH-336 remains open until the implementation enforces this interface. -/
theorem decoder_soundness {Kind : Type} [DecidableEq Kind] [CircuitLayout Kind] [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 65536) {trace : Data p Kind} {program : List (ProgramEntry Kind)}
    {rows : Decoder.Rows p Kind} {column : Fin 9}
    (temporary : Decoder.Binding trace program rows column) :
    ∀ row ∈ trace.rows, (decoderTable program row.family).Contains #[] row.decoderQuery :=
  Decoder.Proofs.decoded hp temporary

/-- Conditional total worker coverage under a full occurrence ledger.
    This ledger is stronger than native cancelling-token matching (AIH-339/F03). -/
theorem participation_soundness [Fact p.Prime] {data : UnifiedReduced.Caller.RequestTrace p}
    {before : Reference.RiscV.Sail.State} (native : UnifiedReduced.Caller.RequestBinding data before)
    (temporary : Requests.Binding data) : Requests.Covered data ∧
    ∀ worker ∈ data.workers.rows, (Delegation.Requests.fulfillment worker).time ≠ (0, 0) :=
  ⟨Requests.Proofs.covered native temporary, Requests.Proofs.no_zero native temporary⟩

/-- Conditional native branch selection under full x12 control validation.
    F02 and full custom-CSR execution remain open; no valid-control premise is
    inserted into the existing general native soundness theorem. -/
theorem bigint_control_soundness [Fact p.Prime] (hp : FieldCapacity.AtLeast p 256)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraints setup)) {command : BigintABI.Command}
    (temporary : BigintABI.Binding w command) :
    w Bigint.Variables.operations[command.opcode] = 1 ∧
    Vector.ofFn (fun i : Fin 8 => (w Bigint.Variables.controlBits[i]).val == 1) = command.bits :=
  ⟨BigintABI.Proofs.selected hp holds temporary, BigintABI.Proofs.native_bits hp holds temporary⟩

/-- Conditional worker-token transport under the temporary RAM-only restriction.
    This address binding leaves the accepted native ROM-shadow finding F04 open. -/
theorem worker_ram_soundness (before : Reference.RiscV.Sail.State)
    {data : Delegation.MemoryData p} (temporary : WorkerRAM.Binding data.rows) :
    data.steps.map (fun edge => (ROMView.token before edge.1, ROMView.token before edge.2)) = data.steps :=
  WorkerRAM.Proofs.pool_transfers_unchanged before temporary

end Airbender.ExternalBoundary
