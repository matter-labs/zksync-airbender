import Airbender.Proofs.ReducedMachine.NativeComparisonExecution
import Airbender.Review.Trace.Families.ReducedMachine.SupportedExecution

namespace Tests.NativeReducedComparisonExecution
open Airbender Arithmetic Trace ReducedMachine Native Verification
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Positive retained original Sail clauses; these are not full native witnesses.
private def entries : Vector ComparisonProgramEntry 8 :=
  #v[⟨0,0x0020a1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SLT),⟨⟨true,true⟩,1,2,3,⟨0,0⟩,67,2⟩⟩,
    ⟨0,0x0020b1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SLTU),⟨⟨false,true⟩,1,2,3,⟨0,0⟩,67,3⟩⟩,
    ⟨0,0xfff0a193,.ITYPE (4095,.Regidx 1,.Regidx 3,.SLTI),⟨⟨true,false⟩,1,0,3,⟨65535,65535⟩,65,2⟩⟩,
    ⟨0,0xfff0b193,.ITYPE (4095,.Regidx 1,.Regidx 3,.SLTIU),⟨⟨false,false⟩,1,0,3,⟨65535,65535⟩,65,3⟩⟩,
    ⟨0,0x0020a033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SLT),⟨⟨true,true⟩,1,2,0,⟨0,0⟩,67,2⟩⟩,
    ⟨0,0x0020b033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SLTU),⟨⟨false,true⟩,1,2,0,⟨0,0⟩,67,3⟩⟩,
    ⟨0,0xfff0a013,.ITYPE (4095,.Regidx 1,.Regidx 0,.SLTI),⟨⟨true,false⟩,1,0,0,⟨65535,65535⟩,65,2⟩⟩,
    ⟨0,0xfff0b013,.ITYPE (4095,.Regidx 1,.Regidx 0,.SLTIU),⟨⟨false,false⟩,1,0,0,⟨65535,65535⟩,65,3⟩⟩]

private def before : State :=
  { (default : State) with regs := (Std.ExtDHashMap.emptyWithCapacity
      |>.insert .x1 (0x80000000 : BitVec 32) |>.insert .x2 (0x7fffffff : BitVec 32)
      |>.insert .x3 (0 : BitVec 32) |>.insert .PC (0 : BitVec 32)) }
private def leftInput : Word := ⟨0,32768⟩
private def registerInput (i : Fin 8) : Word :=
  if entries[i].data.family.useRegister then ⟨65535,32767⟩ else ⟨0,0⟩
private def selectedInput (i : Fin 8) : Word :=
  if entries[i].data.family.useRegister then registerInput i else entries[i].data.immediate
private def outputs : Vector (BitVec 32) 8 := #v[1,0,1,1,1,0,1,1]

/-- All four original forms retain raw operands, exact native masks/tags and x0. -/
theorem selected_forms (i : Fin 8) :
    comparisonDecoderFields entries[i].instruction = some entries[i].data := by
  fin_cases i <;> rfl

/-- Independent cross-limb/sign-bit and negative-immediate values. -/
theorem reference_outputs (i : Fin 8) :
    entries[i].data.family.result leftInput.toBitVec (selectedInput i).toBitVec = outputs[i] := by
  fin_cases i <;> decide +kernel

private theorem left_read (i : Fin 8) :
    run (SailRV32.Functions.rX_bits (.Regidx entries[i].data.rs1)) before =
      .ok leftInput.toBitVec before := by
  fin_cases i
  all_goals apply read_register
  all_goals simp [before,leftInput,Word.toBitVec,Word.value,limbBase,Std.ExtDHashMap.get?_insert]

private theorem right_read (i : Fin 8) :
    run (SailRV32.Functions.rX_bits (.Regidx entries[i].data.rs2)) before =
      .ok (registerInput i).toBitVec before := by
  fin_cases i
  all_goals first
    | rfl
    | (apply read_register
       simp [before,registerInput,entries,Word.toBitVec,Word.value,limbBase,Std.ExtDHashMap.get?_insert])

/-- Retained original clauses, preparation and retirement at ordinary and RV32
    wrap PCs, with actual original Sail reads/writes rather than supplied results. -/
theorem original_retirement (i : Fin 8) (wrap : Bool) :
    let pc := if wrap then (0xfffffffc : BitVec 32) else 16
    ∃ clause, registerClause entries[i].instruction = some clause ∧
      stepSpec (retiredState before pc) clause (.Regidx entries[i].data.rd)
        ⟨Word.ofBitVec outputs[i],Word.ofBitVec (pc + 4)⟩ := by
  let pc := if wrap then (0xfffffffc : BitVec 32) else 16
  let start := retiredState before pc
  let output : Output := ⟨Word.ofBitVec outputs[i],Word.ofBitVec (pc + 4)⟩
  let prepared := { start with regs := start.regs.insert .nextPC output.pc.toBitVec }
  obtain ⟨after,write⟩ := write_success (.Regidx entries[i].data.rd) outputs[i] prepared
  have actual : run (SailRV32.Functions.wX_bits (.Regidx entries[i].data.rd)
      (entries[i].data.family.result leftInput.toBitVec (selectedInput i).toBitVec))
      prepared = .ok () after := by rw [reference_outputs i]; exact write
  have leftRead : run (SailRV32.Functions.rX_bits (.Regidx entries[i].data.rs1)) prepared =
      .ok leftInput.toBitVec prepared :=
    rX_nextPC _ (pc := output.pc.toBitVec) (rX_PC _ (pc := pc) (rX_nextPC _ (pc := pc) (left_read i)))
  have rightRead : run (SailRV32.Functions.rX_bits (.Regidx entries[i].data.rs2)) prepared =
      .ok (registerInput i).toBitVec prepared :=
    rX_nextPC _ (pc := output.pc.toBitVec) (rX_PC _ (pc := pc) (rX_nextPC _ (pc := pc) (right_read i)))
  obtain ⟨clause,dispatch,execute⟩ := NativeComparisonClauseProofs.decoded_clause_of_reads
    (selected_forms i) _ _ _ leftRead rightRead rfl actual
  have projected : run (writeResult (.Regidx entries[i].data.rd) output.destination) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
    simp only [writeResult,output,Word.ofBitVec_roundtrip]
    rw [run_bind_of_ok _ _ _ _ _ write]
    rfl
  exact ⟨clause,dispatch,retire_of_destination (Trace.Proofs.retired_state_pc before pc)
    (Word.ofBitVec_roundtrip (pc + 4)) ⟨after,execute,projected⟩⟩

/-- Every original discarded form stutters all data components while PC advances. -/
theorem discarded_retirement (i : Fin 4) (wrap : Bool) :
    let sample : Fin 8 := ⟨4 + i.val,by omega⟩
    let pc := if wrap then (0xfffffffc : BitVec 32) else 16
    ∃ clause, registerClause entries[sample].instruction = some clause ∧
      run (normalStep clause) (retiredState before pc) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState before (pc + 4)) := by
  let sample : Fin 8 := ⟨4 + i.val,by omega⟩
  let pc := if wrap then (0xfffffffc : BitVec 32) else 16
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

/-- The actual original decoder tag retains signed versus unsigned selection. -/
theorem corrupted_tag_rejected {w : Nat → ZMod mersenne31Modulus}
    (query : decoderQuery w = entries[0].query) : w 11 ≠ 3 := by
  have selected := NativeComparisonDecoderProofs.decoded_fields (selected_forms 0) query
  rw [selected.funct3]
  decide +kernel

/-- Original decoded rd=x0 plus actual native mask forces the discarded word,
    with no range/result/expected write premise. -/
theorem discarded_native_write {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (query : decoderQuery w = entries[4].query) : writtenWord w = ⟨0,0⟩ := by
  have decoded := NativeComparisonDecoderProofs.decoded_fields (selected_forms 4) query
  have flag : rdZeroFlag w = 1 := decoded.zero
  have write := (NativeComparisonFieldProofs.write native entries[4].data.family.useRegister decoded.mask).2
  have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) write
  have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) write
  simp [flag,arithmeticCandidate] at low high
  simp [writtenWord,low,high]

end Tests.NativeReducedComparisonExecution
