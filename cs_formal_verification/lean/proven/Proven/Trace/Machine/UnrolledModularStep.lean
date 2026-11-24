module
public import Proven.Trace.Machine.ModularWords
public import Proven.Trace.RVPooled.AddSub
public import Proven.Trace.RVRowReads

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs AddSub
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- A native modular row with a nonzero destination executes its RV field instruction. -/
theorem unrolled_modular_row_step {trace : PooledTrace babyBearModulus} {initial : RV.State} {cells : List Cell}
    {w : Nat → ZMod babyBearModulus} {before after : RV.State} {entry : RVPooledProgramEntry}
    (opcode : AddSub.Modular.Opcode) (rs1 rs2 rd : BitVec 5) (nonzero : rd ≠ 0)
    (facts : RVPooledRowFacts trace initial cells ⟨.addSub, w⟩ before after entry)
    (dataEq : entry.data = (modularData opcode rs1 rs2 rd).mapFamily pooledArithmeticFamily) :
    RVPooledRowStep ⟨.addSub, w⟩ before after (.mop opcode.rvOp rd rs1 rs2) := by
  obtain ⟨entryPC, entryBits, entryData⟩ := entry
  change entryData = _ at dataEq
  subst entryData
  have core := Verification.holds_of_sublist facts.constraints
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  obtain ⟨left, right, written, finish⟩ := rv_addsub_frame (by decide) (by decide) facts rfl
  have query := facts.query
  have query0 : (⟨.addSub, w⟩ : Row babyBearModulus).decoderQuery =
      (⟨entryPC, entryBits, modularData opcode rs1 rs2 rd⟩ : RVProgramEntry).query := query
  have flags := rv_row_query_selectors_of_bound (by decide) trace.rom.wordMemory facts.constraints
    (modular_mask_bound opcode rs1 rs2 rd) query0
  change ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] =
    (if (modularData opcode rs1 rs2 rd).mask.testBit i.val then 1 else 0) at flags
  have pcWord := rv_native_query_pc_word (by decide : limbBase < babyBearModulus) query0
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec entryPC at pcWord
  have rdQuery := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[4]) query0
  change w 7 = (rd.toNat : ZMod babyBearModulus) at rdQuery
  have history := facts.history
  have shape : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).ports =
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1], importedConstraintsMemoryPorts[2]] := by
    have same : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).ports = importedConstraintsMemoryPorts := rfl
    rw [same]
    rfl
  dsimp only [rowEvents] at history
  rw [shape] at history
  obtain ⟨_, _, _, _, cell, _, _, _, _, _, address, oldRead, _⟩ :=
    rv_three_ports trace.memoryEpoch (by simp [importedConstraintsMemoryPorts])
      (by simp [importedConstraintsMemoryPorts]) history
  have old : before.getReg rd = (Word.mk (w 31).val (w 32).val).toBitVec := by
    have target : cell.addressCode = (Cell.register rd).addressCode :=
      address.trans (register_address_code (by decide) rdQuery)
    simpa [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord] using
      rv_read_register target oldRead
  have readBound (k : Fin 3) := facts.readBounds importedConstraintsMemoryPorts[k]
    (by change importedConstraintsMemoryPorts[k] ∈ importedConstraintsMemoryPorts
        fin_cases k <;> simp [importedConstraintsMemoryPorts])
  have bounds : (Word.mk (w 25).val (w 26).val).Bounded ∧
      (Word.mk (w 29).val (w 30).val).Bounded ∧ (Word.mk (w 31).val (w 32).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using And.intro (readBound 0) (And.intro (readBound 1) (readBound 2))
  let input := modularInput opcode rs1 rs2 rd before
  let output : Circuit.Output := ⟨⟨(w 33).val, (w 34).val⟩, ⟨(w 19).val, (w 20).val⟩⟩
  have interfaces : AddSub.Modular.InterfaceAssumptions input output w := by
    refine ⟨facts.active, ?_, Word.ofBitVec_bound _⟩
    intro k lower upper
    let i : Fin 9 := ⟨k - 10, by omega⟩
    have flag := flags i
    have index : #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = k := by interval_cases k <;> rfl
    rw [index] at flag
    change w k = (if (modularData opcode rs1 rs2 rd).mask.testBit (k - 10) then 1 else 0) at flag
    rw [modular_mask_bit opcode rs1 rs2 rd k lower upper] at flag
    simpa only [input, modularInput, ite_eq_right nonzero, decide_eq_true_eq] using flag
  have mapping : AddSub.Modular.WordMapping input output w := by
    refine ⟨?_, ?_, ?_, rdQuery, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · intro _
      exact modular_word_residue bounds.1 left
    · intro _
      exact modular_word_residue bounds.2.1 right
    · intro _ _
      exact modular_word_residue bounds.2.2 old
    · change w 0 = ((Word.ofBitVec before.pc).lo : ZMod babyBearModulus)
      rw [facts.pc, ← pcWord, ZMod.natCast_zmod_val]
    · change w 1 = ((Word.ofBitVec before.pc).hi : ZMod babyBearModulus)
      rw [facts.pc, ← pcWord, ZMod.natCast_zmod_val]
  have result := AddSub.Proofs.modular_result core interfaces mapping nonzero
  have value : output.destination.toBitVec =
      RV.mopVal opcode.rvOp (before.getReg rs1) (before.getReg rs2) (before.getReg rd) := by
    change BitVec.ofNat 32 output.destination.value = _
    rw [result, AddSub.Modular.arithmeticResult_rv]
    rfl
  refine ⟨_, RV.exec_mop before opcode.rvOp rd rs1 rs2, ?_⟩
  rw [← value]
  exact rv_state_next written rfl finish

end Airbender.Trace.Machine.Proofs
