import Airbender.Review.Trace.Families.ReducedMachine.FetchedExecution
import Airbender.Review.Trace.Families.ReducedMachine.Execution

namespace Tests.NativeReducedExecution
open Airbender Arithmetic Trace ReducedMachine Native Verification
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Reuse only original instructions/bytes and their actual reduced projection.
-- These positive Sail tests do not claim full 117-equation native acceptance.
private def entries : Vector ShiftProgramEntry 12 :=
  #v[⟨0,0x2091b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SLL),⟨.left,1,2,3,⟨0,0⟩,4099,1⟩⟩,
    ⟨4,0x20d1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SRL),⟨.right,1,2,3,⟨0,0⟩,69635,5⟩⟩,
    ⟨8,0x4020d1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SRA),⟨.arithmetic,1,2,3,⟨0,0⟩,102403,5⟩⟩,
    ⟨24,0x1f09193,.SHIFTIOP (31,.Regidx 1,.Regidx 3,.SLLI),⟨.left,1,0,3,⟨31,0⟩,4097,1⟩⟩,
    ⟨28,0x1f0d193,.SHIFTIOP (31,.Regidx 1,.Regidx 3,.SRLI),⟨.right,1,0,3,⟨31,0⟩,69633,5⟩⟩,
    ⟨32,0x41f0d193,.SHIFTIOP (31,.Regidx 1,.Regidx 3,.SRAI),⟨.arithmetic,1,0,3,⟨1055,0⟩,102401,5⟩⟩,
    ⟨48,0x209033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SLL),⟨.left,1,2,0,⟨0,0⟩,4099,1⟩⟩,
    ⟨52,0x20d033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SRL),⟨.right,1,2,0,⟨0,0⟩,69635,5⟩⟩,
    ⟨56,0x4020d033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SRA),⟨.arithmetic,1,2,0,⟨0,0⟩,102403,5⟩⟩,
    ⟨72,0x1f09013,.SHIFTIOP (31,.Regidx 1,.Regidx 0,.SLLI),⟨.left,1,0,0,⟨31,0⟩,4097,1⟩⟩,
    ⟨76,0x1f0d013,.SHIFTIOP (31,.Regidx 1,.Regidx 0,.SRLI),⟨.right,1,0,0,⟨31,0⟩,69633,5⟩⟩,
    ⟨80,0x41f0d013,.SHIFTIOP (31,.Regidx 1,.Regidx 0,.SRAI),⟨.arithmetic,1,0,0,⟨1055,0⟩,102401,5⟩⟩]

private def before : State :=
  { (default : State) with regs := (Std.ExtDHashMap.emptyWithCapacity
      |>.insert .x1 (0x8000ffff : BitVec 32) |>.insert .x2 (3 : BitVec 32)
      |>.insert .x3 (0 : BitVec 32) |>.insert .PC (0 : BitVec 32)) }

private def leftInput : Word := ⟨65535,32768⟩
private def registerInput (i : Fin 12) : Word :=
  if shiftUsesRegister entries[i].instruction then ⟨3,0⟩ else ⟨0,0⟩
private def selectedInput (i : Fin 12) : Word :=
  if shiftUsesRegister entries[i].instruction then registerInput i else entries[i].data.immediate
private def outputs : Vector (BitVec 32) 12 :=
  #v[0x0007fff8,0x10001fff,0xf0001fff,0x80000000,1,0xffffffff,
     0x0007fff8,0x10001fff,0xf0001fff,0x80000000,1,0xffffffff]

/-- All twelve original ordinary/x0 projections retain their actual forms. -/
private theorem selected_forms (i : Fin 12) :
    shiftDecoderFields entries[i].instruction = some entries[i].data ∧
      shiftUsesRegister entries[i].instruction = decide (i.val % 6 < 3) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

/-- Independent concrete complete results, including encoded SRAI 1055→31. -/
private theorem reference_outputs (i : Fin 12) :
    entries[i].data.family.result leftInput.toBitVec
      ((selectedInput i).toBitVec.extractLsb' 0 5).toNat = outputs[i] := by
  fin_cases i <;> decide +kernel

private theorem left_read (i : Fin 12) :
    run (SailRV32.Functions.rX_bits (.Regidx entries[i].data.rs1)) before =
      .ok leftInput.toBitVec before := by
  fin_cases i
  all_goals apply read_register
  all_goals simp [before,leftInput,Word.toBitVec,Word.value,limbBase,Std.ExtDHashMap.get?_insert]

private theorem right_read (i : Fin 12) :
    run (SailRV32.Functions.rX_bits (.Regidx entries[i].data.rs2)) before =
      .ok (registerInput i).toBitVec before := by
  fin_cases i
  all_goals first
    | rfl
    | (apply read_register
       simp [before,registerInput,entries,shiftUsesRegister,Word.toBitVec,Word.value,limbBase,Std.ExtDHashMap.get?_insert])

/-- All twelve retained original clauses perform original nextPC preparation
    and retirement, both at ordinary public PCs and full RV32 rollover. This is
    a positive original Sail fixture, not full native117-equation acceptance. -/
theorem original_retirement (i : Fin 12) (wrap : Bool) :
    let pc := if wrap then (0xfffffffc : BitVec 32) else entries[i].pc
    ∃ clause, registerClause entries[i].instruction = some clause ∧
      stepSpec (retiredState before pc) clause (.Regidx entries[i].data.rd)
        ⟨Word.ofBitVec outputs[i],Word.ofBitVec (pc + 4)⟩ := by
  let pc := if wrap then (0xfffffffc : BitVec 32) else entries[i].pc
  let start := retiredState before pc
  let output : Output := ⟨Word.ofBitVec outputs[i],Word.ofBitVec (pc + 4)⟩
  let prepared := { start with regs := start.regs.insert .nextPC output.pc.toBitVec }
  obtain ⟨after,write⟩ := write_success (.Regidx entries[i].data.rd) outputs[i] prepared
  have actual : run (SailRV32.Functions.wX_bits (.Regidx entries[i].data.rd)
      (entries[i].data.family.result leftInput.toBitVec ((selectedInput i).toBitVec.extractLsb' 0 5).toNat))
      prepared = .ok () after := by rw [reference_outputs]; exact write
  have leftRead : run (SailRV32.Functions.rX_bits (.Regidx entries[i].data.rs1)) prepared =
      .ok leftInput.toBitVec prepared :=
    rX_nextPC _ (pc := output.pc.toBitVec) (rX_PC _ (pc := pc) (rX_nextPC _ (pc := pc) (left_read i)))
  have rightRead : run (SailRV32.Functions.rX_bits (.Regidx entries[i].data.rs2)) prepared =
      .ok (registerInput i).toBitVec prepared :=
    rX_nextPC _ (pc := output.pc.toBitVec) (rX_PC _ (pc := pc) (rX_nextPC _ (pc := pc) (right_read i)))
  obtain ⟨clause,dispatch,execute⟩ := NativeShiftClauseProofs.decoded_clause_of_reads
    (selected_forms i).1 _ _ _ leftRead rightRead rfl actual
  have projected : run (writeResult (.Regidx entries[i].data.rd) output.destination) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
    simp only [writeResult,output,Word.ofBitVec_roundtrip]
    rw [run_bind_of_ok _ _ _ _ _ write]
    rfl
  exact ⟨clause,dispatch,retire_of_destination (Trace.Proofs.retired_state_pc before pc)
    (Word.ofBitVec_roundtrip (pc + 4)) ⟨after,execute,projected⟩⟩

/-- Original discarded instructions keep every data component, but their PC
    and nextPC still retire to PC+4, including top-word wrap. -/
theorem discarded_retirement (i : Fin 6) (wrap : Bool) :
    let sample : Fin 12 := ⟨6 + i.val,by omega⟩
    let pc := if wrap then (0xfffffffc : BitVec 32) else entries[sample].pc
    ∃ clause, registerClause entries[sample].instruction = some clause ∧
      run (normalStep clause) (retiredState before pc) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState before (pc + 4)) := by
  let sample : Fin 12 := ⟨6 + i.val,by omega⟩
  let pc := if wrap then (0xfffffffc : BitVec 32) else entries[sample].pc
  obtain ⟨clause,dispatch,after,normal,projected⟩ := original_retirement sample wrap
  have zero : entries[sample].data.rd = 0 := by fin_cases i <;> rfl
  have written : run (SailRV32.Functions.wX_bits (.Regidx entries[sample].data.rd)
      (Word.ofBitVec outputs[sample]).toBitVec) (retiredState before pc) =
      .ok () (retiredState before pc) := by rw [zero]; rfl
  have actual := Trace.Proofs.projected_step_of_write entries[sample].data.rd
    (⟨Word.ofBitVec outputs[sample],Word.ofBitVec (pc + 4)⟩ : Output) written
  have same := (EStateM.Result.ok.inj (projected.symm.trans actual)).2
  exact ⟨clause,dispatch,by
    simpa only [same,Word.ofBitVec_roundtrip,Trace.Proofs.retired_state_overwrite] using normal⟩

/-- This rejection uses initialized public execution; no terminal-PC bound or
    expected intermediate state is supplied. -/
theorem oversized_terminal_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells)
    (decoded : ShiftDecodedTrace (fixedData trace) setup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (oversized : limbBase ≤ trace.terminal.word.lo) : ¬ Accepted (fixedData trace) := by
  intro accepted
  exact Nat.not_le_of_gt (public_shift_execution image inputs accepted decoded aligned).1.1 oversized

/-- Actual native initialized matching constructs the segment states and runs
    original preparation/retirement. No per-row source bound or state answer. -/
theorem initialized_retirement {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, ∃ before after clause,
      entry.SourceWith initial shiftDecoderFields ∧ row.decoderQuery = entry.query ∧
      SailHistory cells (rowEvents (fixedData trace).memoryEpoch row).reverse before after ∧
      registerClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (initialPCWord row.assignment).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (finalPCWord row.assignment).toBitVec) := by
  obtain ⟨registers,execution⟩ := public_shift_instruction_history image inputs accepted decoded aligned
  obtain ⟨_,rows,_,_,permutation,_,_,_,_,_,transfers⟩ := registers
  obtain ⟨newer,older,shape⟩ := List.mem_iff_append.mp (permutation.mem_iff.mpr present)
  obtain ⟨_,_,before,after,_,_,_,_,current,_,_⟩ := transfers newer row older shape
  obtain ⟨entry,member,source,query,runRow⟩ := execution row present
  obtain ⟨clause,dispatch,execute⟩ := runRow.2 before after current
  exact ⟨entry,member,before,after,clause,source,query,current,dispatch,execute⟩

end Tests.NativeReducedExecution
