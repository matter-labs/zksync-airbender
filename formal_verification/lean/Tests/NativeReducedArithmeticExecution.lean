import Airbender.Review.Trace.Families.ReducedMachine.ArithmeticFetchedExecution
import Airbender.Review.Trace.Families.ReducedMachine.ArithmeticExecution

namespace Tests.NativeReducedArithmeticExecution
open Airbender Arithmetic Trace ReducedMachine Native Verification
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Reuse only original instructions/bytes and their actual reduced projection.
-- These positive Sail tests do not claim full 117-equation native acceptance.
private def entries : Vector ArithmeticProgramEntry 10 :=
  #v[⟨0,0x002081b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.ADD),⟨.add,1,2,3,⟨0,0⟩,11,0⟩⟩,
    ⟨4,0xfff08193,.ITYPE (4095,.Regidx 1,.Regidx 3,.ADDI),⟨.addi,1,0,3,⟨65535,65535⟩,9,0⟩⟩,
    ⟨8,0x402081b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SUB),⟨.sub,1,2,3,⟨0,0⟩,8195,0⟩⟩,
    ⟨12,0xfffff1b7,.UTYPE (1048575,.Regidx 3,.LUI),⟨.lui,0,0,3,⟨61440,65535⟩,513,7⟩⟩,
    ⟨0x12340000,0x00005197,.UTYPE (5,.Regidx 3,.AUIPC),⟨.auipc,0,0,3,⟨20480,0⟩,17,5⟩⟩,
    ⟨16,0x00208033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.ADD),⟨.add,1,2,0,⟨0,0⟩,11,0⟩⟩,
    ⟨20,0xfff08013,.ITYPE (4095,.Regidx 1,.Regidx 0,.ADDI),⟨.addi,1,0,0,⟨65535,65535⟩,9,0⟩⟩,
    ⟨24,0x40208033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SUB),⟨.sub,1,2,0,⟨0,0⟩,8195,0⟩⟩,
    ⟨28,0xfffff037,.UTYPE (1048575,.Regidx 0,.LUI),⟨.lui,0,0,0,⟨61440,65535⟩,513,7⟩⟩,
    ⟨0x12340000,0x00005017,.UTYPE (5,.Regidx 0,.AUIPC),⟨.auipc,0,0,0,⟨20480,0⟩,17,5⟩⟩]

private def before : State :=
  { (default : State) with regs := (Std.ExtDHashMap.emptyWithCapacity
      |>.insert .x1 (0xffffffff : BitVec 32) |>.insert .x2 (3 : BitVec 32)
      |>.insert .x3 (0 : BitVec 32) |>.insert .PC (0 : BitVec 32)) }

private def leftInput (i : Fin 10) : Word := if i.val % 5 < 3 then ⟨65535,65535⟩ else ⟨0,0⟩
private def registerInput (i : Fin 10) : Word :=
  if entries[i].data.family.useRegister then ⟨3,0⟩ else ⟨0,0⟩
private def selectedInput (i : Fin 10) : Word :=
  if entries[i].data.family.useRegister then registerInput i else entries[i].data.immediate
private def outputs (wrap : Bool) : Vector (BitVec 32) 10 :=
  #v[2,0xfffffffe,0xfffffffc,0xfffff000,(if wrap then 0x4ffc else 0x12345000),
     2,0xfffffffe,0xfffffffc,0xfffff000,(if wrap then 0x4ffc else 0x12345000)]

/-- All original arithmetic forms retain the actual reduced projection. -/
theorem selected_forms (i : Fin 10) :
    arithmeticDecoderFields entries[i].instruction = some entries[i].data := by
  fin_cases i <;> rfl

/-- Independent arithmetic boundaries: carry, borrow, negative immediate, upper
    immediate above M31 and AUIPC at a nonzero incoming PC or RV32 wrap. -/
theorem reference_outputs (i : Fin 10) (wrap : Bool) :
    entries[i].data.family.result (leftInput i).toBitVec
      ((selectedInput i).toBitVec)
      (if wrap then 0xfffffffc else entries[i].pc) entries[i].data.immediate.toBitVec = (outputs wrap)[i] := by
  fin_cases i <;> cases wrap <;> decide +kernel

private theorem left_read (i : Fin 10) :
    run (SailRV32.Functions.rX_bits (.Regidx entries[i].data.rs1)) before =
      .ok (leftInput i).toBitVec before := by
  fin_cases i
  all_goals first | rfl | (apply read_register; simp [before,leftInput,Word.toBitVec,Word.value,limbBase,Std.ExtDHashMap.get?_insert])

private theorem right_read (i : Fin 10) :
    run (SailRV32.Functions.rX_bits (.Regidx entries[i].data.rs2)) before =
      .ok (registerInput i).toBitVec before := by
  fin_cases i
  all_goals first
    | rfl
    | (apply read_register
       simp [before,registerInput,entries,ArithmeticMode.useRegister,Word.toBitVec,Word.value,limbBase,Std.ExtDHashMap.get?_insert])

/-- All ten retained original clauses perform original nextPC preparation
    and retirement, both at ordinary public PCs and full RV32 rollover. This is
    a positive original Sail fixture, not full native117-equation acceptance. -/
theorem original_retirement (i : Fin 10) (wrap : Bool) :
    let pc := if wrap then (0xfffffffc : BitVec 32) else entries[i].pc
    ∃ clause, registerClause entries[i].instruction = some clause ∧
      stepSpec (retiredState before pc) clause (.Regidx entries[i].data.rd)
        ⟨Word.ofBitVec (outputs wrap)[i],Word.ofBitVec (pc + 4)⟩ := by
  let pc := if wrap then (0xfffffffc : BitVec 32) else entries[i].pc
  let start := retiredState before pc
  let output : Output := ⟨Word.ofBitVec (outputs wrap)[i],Word.ofBitVec (pc + 4)⟩
  let prepared := { start with regs := start.regs.insert .nextPC output.pc.toBitVec }
  obtain ⟨after,write⟩ := write_success (.Regidx entries[i].data.rd) (outputs wrap)[i] prepared
  have actual : run (SailRV32.Functions.wX_bits (.Regidx entries[i].data.rd)
      (entries[i].data.family.result (leftInput i).toBitVec (selectedInput i).toBitVec pc entries[i].data.immediate.toBitVec))
      prepared = .ok () after := by rw [reference_outputs i wrap]; exact write
  have leftRead : run (SailRV32.Functions.rX_bits (.Regidx entries[i].data.rs1)) prepared =
      .ok (leftInput i).toBitVec prepared :=
    rX_nextPC _ (pc := output.pc.toBitVec) (rX_PC _ (pc := pc) (rX_nextPC _ (pc := pc) (left_read i)))
  have rightRead : run (SailRV32.Functions.rX_bits (.Regidx entries[i].data.rs2)) prepared =
      .ok (registerInput i).toBitVec prepared :=
    rX_nextPC _ (pc := output.pc.toBitVec) (rX_PC _ (pc := pc) (rX_nextPC _ (pc := pc) (right_read i)))
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) prepared = .ok pc prepared := by
    apply read_register
    simp [prepared,start,retiredState,Std.ExtDHashMap.get?_insert]
  obtain ⟨clause,dispatch,execute⟩ := NativeArithmeticClauseProofs.decoded_clause_of_reads
    (selected_forms i) _ _ _ (Word.ofBitVec pc) leftRead rightRead rfl
    (by simpa only [Word.ofBitVec_roundtrip] using pcRead)
    (by simpa only [Word.ofBitVec_roundtrip,selectedInput] using actual)
  have projected : run (writeResult (.Regidx entries[i].data.rd) output.destination) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
    simp only [writeResult,output,Word.ofBitVec_roundtrip]
    rw [run_bind_of_ok _ _ _ _ _ write]
    rfl
  exact ⟨clause,dispatch,retire_of_destination (Trace.Proofs.retired_state_pc before pc)
    (Word.ofBitVec_roundtrip (pc + 4)) ⟨after,execute,projected⟩⟩

/-- Original discarded instructions keep every data component, but their PC
    and nextPC still retire to PC+4, including top-word wrap. -/
theorem discarded_retirement (i : Fin 5) (wrap : Bool) :
    let sample : Fin 10 := ⟨5 + i.val,by omega⟩
    let pc := if wrap then (0xfffffffc : BitVec 32) else entries[sample].pc
    ∃ clause, registerClause entries[sample].instruction = some clause ∧
      run (normalStep clause) (retiredState before pc) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState before (pc + 4)) := by
  let sample : Fin 10 := ⟨5 + i.val,by omega⟩
  let pc := if wrap then (0xfffffffc : BitVec 32) else entries[sample].pc
  obtain ⟨clause,dispatch,after,normal,projected⟩ := original_retirement sample wrap
  have zero : entries[sample].data.rd = 0 := by fin_cases i <;> rfl
  have written : run (SailRV32.Functions.wX_bits (.Regidx entries[sample].data.rd)
      (Word.ofBitVec (outputs wrap)[sample]).toBitVec) (retiredState before pc) =
      .ok () (retiredState before pc) := by rw [zero]; rfl
  have actual := Trace.Proofs.projected_step_of_write entries[sample].data.rd
    (⟨Word.ofBitVec (outputs wrap)[sample],Word.ofBitVec (pc + 4)⟩ : Output) written
  have same := (EStateM.Result.ok.inj (projected.symm.trans actual)).2
  exact ⟨clause,dispatch,by
    simpa only [same,Word.ofBitVec_roundtrip,Trace.Proofs.retired_state_overwrite] using normal⟩

/-- This rejection uses initialized public execution; no terminal-PC bound or
    expected intermediate state is supplied. -/
theorem oversized_terminal_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells)
    (decoded : ArithmeticDecodedTrace trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (oversized : limbBase ≤ trace.terminal.word.lo) : ¬ Accepted trace := by
  intro accepted
  exact Nat.not_le_of_gt (public_arithmetic_execution image inputs accepted decoded aligned).1.1 oversized

/-- Actual native initialized matching constructs the segment states and runs
    original preparation/retirement. No per-row source bound or state answer. -/
theorem initialized_retirement {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : ArithmeticDecodedTrace trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, ∃ before after clause,
      entry.SourceWith initial arithmeticDecoderFields ∧ row.decoderQuery = entry.query ∧
      SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after ∧
      registerClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (initialPCWord row.assignment).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (finalPCWord row.assignment).toBitVec) := by
  obtain ⟨registers,execution⟩ := public_arithmetic_instruction_history image inputs accepted decoded aligned
  obtain ⟨_,rows,_,_,permutation,_,_,_,_,_,transfers⟩ := registers
  obtain ⟨newer,older,shape⟩ := List.mem_iff_append.mp (permutation.mem_iff.mpr present)
  obtain ⟨_,_,before,after,_,_,_,_,current,_,_⟩ := transfers newer row older shape
  obtain ⟨entry,member,source,query,runRow⟩ := execution row present
  obtain ⟨clause,dispatch,execute⟩ := runRow.2 before after current
  exact ⟨entry,member,before,after,clause,source,query,current,dispatch,execute⟩

end Tests.NativeReducedArithmeticExecution
