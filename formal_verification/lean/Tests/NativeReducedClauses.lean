import Airbender.Review.Trace.Families.ReducedMachine.Clauses

namespace Tests.NativeReducedClauses
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
theorem selected_forms (i : Fin 12) :
    shiftDecoderFields entries[i].instruction = some entries[i].data ∧
      shiftUsesRegister entries[i].instruction = decide (i.val % 6 < 3) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

/-- Independent concrete complete results, including encoded SRAI 1055→31. -/
theorem reference_outputs (i : Fin 12) :
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

/-- Actual original Sail clauses execute all twelve forms. The same after-state
    is obtained by Sail's own destination write; no state/result premise is given.
    This is an original-clause fixture, not a complete accepted native row. -/
theorem original_clauses (i : Fin 12) :
    ∃ after : State, ∃ clause,
      registerClause entries[i].instruction = some clause ∧
      run clause before = .ok SailRV32.Functions.RETIRE_SUCCESS after ∧
      run (SailRV32.Functions.wX_bits (.Regidx entries[i].data.rd) outputs[i]) before = .ok () after := by
  obtain ⟨after,write⟩ := write_success (.Regidx entries[i].data.rd) outputs[i] before
  have actual : run (SailRV32.Functions.wX_bits (.Regidx entries[i].data.rd)
      (entries[i].data.family.result leftInput.toBitVec ((selectedInput i).toBitVec.extractLsb' 0 5).toNat))
      before = .ok () after := by rw [reference_outputs]; exact write
  obtain ⟨clause,dispatch,execute⟩ := NativeShiftClauseProofs.decoded_clause_of_reads
    (selected_forms i).1 leftInput (selectedInput i) (registerInput i)
    (left_read i) (right_read i) rfl actual
  exact ⟨after,clause,dispatch,execute,write⟩

/-- All six original discarded shift clauses execute into the unchanged state. -/
theorem discarded_original_clauses (i : Fin 6) :
    ∃ clause, registerClause entries[6 + i.val].instruction = some clause ∧
      run clause before = .ok SailRV32.Functions.RETIRE_SUCCESS before := by
  let sample : Fin 12 := ⟨6 + i.val,by omega⟩
  obtain ⟨after,clause,dispatch,execute,write⟩ := original_clauses sample
  have pureWrite : run (SailRV32.Functions.wX_bits (.Regidx entries[sample].data.rd)
      outputs[sample]) before = .ok () before := by fin_cases i <;> rfl
  have same := (EStateM.Result.ok.inj (write.symm.trans pureWrite)).2
  exact ⟨clause,dispatch,by simpa only [same] using execute⟩

/-- Actual SRAI native routing selects encoded 1055, while the readonly rs2=x0
    access and its address remain present in the original native relation. -/
theorem native_immediate_alias {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (query : decoderQuery w = entries[5].query) :
    operandWord w = ⟨1055,0⟩ ∧ importedConstraintsMemoryPorts[1].writeValue = none ∧
      importedConstraintsMemoryPorts[1].address.code w = (Cell.register 0).addressCode := by
  have selected := NativeShiftOperandProofs.entry_selected_operand native (selected_forms 5).1 query
  refine ⟨?_,NativeShiftPortProofs.readonly_sources.2,?_⟩
  · change operandWord w = (⟨1055,0⟩ : Word) at selected
    exact selected
  · exact NativeShiftPortProofs.register_addresses native (selected_forms 5).1 query 1

/-- Full native constraints, transfer and derived local arithmetic execute a
    retained x0 clause, even before PC preparation/retirement is composed. -/
theorem discarded_native_clause {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (source : (sourceWord w).Bounded)
    {before after : State}
    (transfer : ShiftRegisterTransfer (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily) entry before after)
    (discarded : entry.data.rd = 0) :
    ∃ clause, registerClause entry.instruction = some clause ∧
      run clause before = .ok SailRV32.Functions.RETIRE_SUCCESS before := by
  obtain ⟨clause,dispatch,execute⟩ := NativeShiftClauseProofs.native_clause native fields query source transfer
  have write := transfer.2
  rw [discarded] at write
  change EStateM.Result.ok () before = EStateM.Result.ok () after at write
  have same := (EStateM.Result.ok.inj write).2
  exact ⟨clause,dispatch,by simpa only [same] using execute⟩

/-- Public history supplies actual row states; the original clause runs between
    those same constructed states, without a per-row state or source-bound input. -/
theorem initialized_row_clause {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : shiftDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, ∃ before after : State, ∃ clause,
      row.decoderQuery = entry.query ∧ registerClause entry.instruction = some clause ∧
      SailHistory cells (rowEvents (fixedData trace).memoryEpoch row).reverse before after ∧
      run clause before = .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  obtain ⟨registers,clauses⟩ := public_shift_clause_history image inputs accepted decoded aligned
  obtain ⟨_,rows,_,_,permutation,_,_,_,_,_,segments⟩ := registers
  obtain ⟨newer,older,shape⟩ := List.mem_iff_append.mp (permutation.mem_iff.mpr present)
  obtain ⟨_,_,before,after,_,_,_,_,current,_,_⟩ := segments newer row older shape
  obtain ⟨entry,member,_,query,execute⟩ := clauses row present
  obtain ⟨clause,dispatch,result⟩ := execute before after current
  exact ⟨entry,member,before,after,clause,query,dispatch,current,result⟩

/-- New clause composition does not widen the original RV32 immediate profile. -/
theorem illegal_immediates :
    ∀ op ∈ [SailRV32.sop.SLLI,.SRLI,.SRAI],
      shiftDecoderFields (.SHIFTIOP (32,.Regidx 1,.Regidx 3,op)) = none ∧
      shiftDecoderFields (.SHIFTIOP (63,.Regidx 1,.Regidx 0,op)) = none := by decide +kernel

end Tests.NativeReducedClauses
