import Airbender.Proofs.Reduced.RoundCall
import Airbender.Proofs.Trace.CodeHistory

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail Delegation.Caller Delegation.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- The complete virtual CSR query binds the actual worker family. -/
theorem caller_worker_family [Fact p.Prime] (hp : FieldCapacity.AtLeast p 2048)
    {w : Nat → ZMod p} {entry : Delegation.Caller.ProgramEntry} {worker : Delegation.Row p}
    (query : Delegation.Caller.nativeQuery w = Delegation.Caller.query entry)
    (matched : Delegation.Requests.fulfillment worker = Delegation.Requests.caller w) :
    worker.family = entry.data.family := by
  have field := congrArg (fun fields : Vector (ZMod p) 9 => fields[3]) query
  change w 6 = (Delegation.Requests.csr entry.data.family : ZMod p) at field
  have bound : Delegation.Requests.csr entry.data.family < p := by
    cases entry.data.family <;> simp only [Delegation.Requests.csr] <;> omega
  have csr := congrArg Delegation.Requests.Request.csr matched
  change Delegation.Requests.csr worker.family = (w 6).val at csr
  rw [field, ZMod.val_natCast_of_lt bound] at csr
  exact Delegation.Caller.Proofs.csr_injective csr

/-- The native caller PC equations retire any actual state at that caller's PC. -/
theorem caller_pc_retirement_raw [Fact p.Prime]
    {data : RequestTrace p} {initial after : State}
    (requests : RequestBinding data initial) {row : Trace.Row p PooledFamily}
    (member : row ∈ data.callers)
    (pc : run (SailRV32.Functions.get_arch_pc ()) after = .ok row.start.word.toBitVec after) :
    run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ()) after =
      .ok () (retiredState after row.finish.word.toBitVec) := by
  have family := (caller_member member).2
  have native := (requests.callers row member).2
  cases row with
  | mk kind w =>
    cases family
    exact native.sail after pc

/-- Rebased caller states retain the same complete native PC retirement. -/
theorem caller_pc_retirement [Fact p.Prime]
    {data : RequestTrace p} {initial after : State}
    (requests : RequestBinding data initial) {row : Trace.Row p PooledFamily}
    (member : row ∈ data.callers) :
    run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ())
      (retiredState after row.start.word.toBitVec) = .ok () (retiredState after row.finish.word.toBitVec) := by
  have native := caller_pc_retirement_raw requests member (retired_state_pc after row.start.word.toBitVec)
  simpa only [retired_state_overwrite] using native

/-- Readonly shared history transports the caller's public source to its actual cut. -/
theorem caller_source_readonly [Fact p.Prime] (hp : FieldCapacity.NoWrap p 65536)
    {data : RequestTrace p} {initial before : State} {ca : List (BitVec 32)} {cells : List Cell}
    {events : List MemoryAccess}
    (accepted : RequestChecks data) (inputs : RequestInputs data initial ca)
    (code : ∀ entry ∈ data.program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (unchanged : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.callers)
    (past : SailHistory cells (events.filter fun event => decide (event.1 ≤ row.clock)) initial before) :
    ∃ entry ∈ data.program, Delegation.Caller.nativeQuery row.assignment = Delegation.Caller.query entry ∧
      row.start.word.toBitVec = entry.pc ∧
      entry.SourceWith before Delegation.Caller.decoderFields := by
  have decoded := accepted.decoded row member
  change ∃ i : Fin data.program.length,
    Delegation.Caller.nativeQuery row.assignment = Delegation.Caller.query (data.program.get i) at decoded
  obtain ⟨i, query⟩ := decoded
  let entry := data.program.get i
  have present : entry ∈ data.program := List.get_mem _ _
  have source := run_program_sources inputs.image entry present
  have actual := entry_source_after_history past
    (fun event included => unchanged event (List.mem_filter.mp included).1)
    source (code entry present).1 (code entry present).2
  have pcWord := Delegation.Caller.Proofs.query_pc hp query
  have family := (caller_member member).2
  cases row with
  | mk kind w =>
    cases family
    refine ⟨entry, present, query, ?_, actual⟩
    exact (congrArg Word.toBitVec pcWord).trans (Word.ofBitVec_roundtrip _)

/-- A full-width public caller query disables the external-input read flag. -/
theorem native_caller_read_disabled [Fact p.Prime] (hp : FieldCapacity.NoWrap p 65536)
    {w : Nat → ZMod p} {entry : Delegation.Caller.ProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (query : Delegation.Caller.nativeQuery w = Delegation.Caller.query entry) :
    NonDeterminism.Pooled.isRead (⟨.addSub, w⟩ : Trace.Row p PooledFamily) = false := by
  have flags := (AddSub.Proofs.local_flags core).2
  have boolean : ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 0 ∨
      w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 1 := by
    intro i
    have bit := flags i
    fin_cases i <;> simpa using bit
  have packed := congrArg (fun values : Vector (ZMod p) 9 => values[8]) query
  change (∑ i : Fin 9, (2 ^ i.val : Nat) * w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i]) =
    (128 : ZMod p) at packed
  have bits := unpack_decoder_bits (by omega) (by decide) boolean packed
  have zero : w 18 = 0 := bits 8
  simp [NonDeterminism.Pooled.isRead, NonDeterminism.isRead, zero]

end Airbender.AddSub.Modular.External.Caller.Proofs
