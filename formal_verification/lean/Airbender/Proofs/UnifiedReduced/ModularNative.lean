import Airbender.Proofs.UnifiedReduced.ModularArithmetic

namespace Airbender.UnifiedReduced.Modular.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem spec_from_history
    {initial : State} {cells : List Cell} {seed : List (MemoryToken babyBearModulus)}
    (image : initialImage initial cells = some seed) (registers : ∀ index, Cell.register index ∈ cells)
    {setup : Table (ZMod babyBearModulus) (fields 10)} {w : Nat → ZMod babyBearModulus}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1)
    (bounds : ∀ i : Fin 3, (readToken w importedConstraintsMemoryPorts[i]).word.Bounded)
    {entry : ProgramEntry} (fields : mopDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (opcode : AddSub.Modular.Opcode) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = AddSub.Modular.instruction opcode rs1 rs2 rd)
    (epoch : Nat) {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily)).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok (Control.initialPC w).toBitVec before) :
    AddSub.Modular.spec (AddSub.Modular.Proofs.nativeInput opcode rs1 rs2 rd (lift w) before)
      ⟨Control.destination w, Control.finalPC w⟩ := by
  let input := AddSub.Modular.Proofs.nativeInput opcode rs1 rs2 rd (lift w) before
  let output : Output := ⟨Control.destination w, Control.finalPC w⟩
  have data := mop_metadata opcode rs1 rs2 rd fields encoding
  have flags := UnifiedReduced.Proofs.decoder_selectors (p := babyBearModulus) (by decide)
    core (mop_bounds fields).2.1 query
  have disabled (i : Fin 12) : w importedConstraintsDecoderColumns.flags[(⟨7 + i.val, by omega⟩ : Fin 19)] = 0 := by
    have flag := flags ⟨7 + i.val, by omega⟩
    rw [data, mop_high_flags opcode rs1 rs2 rd i] at flag
    exact flag
  have interfaces : AddSub.Modular.InterfaceAssumptions input output (lift w) :=
    interfaces_from_history image registers core active fields query opcode rs1 rs2 rd
      encoding epoch past history pc
  have left : (Word.mk ((lift w) 25).val ((lift w) 26).val).Bounded := by
    simpa [lift, read_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using bounds 0
  have right : (Word.mk ((lift w) 29).val ((lift w) 30).val).Bounded := by
    simpa [lift, read_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using bounds 1
  have old : (Word.mk ((lift w) 31).val ((lift w) 32).val).Bounded := by
    simpa [lift, read_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using bounds 2
  have rdIndex := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[4]) query
  change w 7 = (entry.data.rd.toNat : ZMod babyBearModulus) at rdIndex
  have rdEqual : entry.data.rd = rd := data ▸ AddSub.Modular.Proofs.native_rd opcode rs1 rs2 rd
  rw [rdEqual] at rdIndex
  have mapping : AddSub.Modular.WordMapping input output (lift w) := by
    constructor
    · intro _; exact (AddSub.Modular.Proofs.word_residue (lift w) 25 26 left).symm
    · intro _; exact (AddSub.Modular.Proofs.word_residue (lift w) 29 30 right).symm
    · intro _ _; exact (AddSub.Modular.Proofs.word_residue (lift w) 31 32 old).symm
    · exact rdIndex
    · exact (ZMod.natCast_zmod_val _).symm
    · exact (ZMod.natCast_zmod_val _).symm
    · rfl
    · rfl
    · rfl
    · rfl
  have value : input.rd ≠ zeroRegister → output.destination.value =
      (AddSub.Modular.arithmeticResult input.opcode input.left input.right input.oldDestination).val := by
    intro nonzero
    have s10 := interfaces.selection 10 (by omega) (by omega)
    have s11 := interfaces.selection 11 (by omega) (by omega)
    have s12 := interfaces.selection 12 (by omega) (by omega)
    have s13 := interfaces.selection 13 (by omega) (by omega)
    have s14 := interfaces.selection 14 (by omega) (by omega)
    have s15 := interfaces.selection 15 (by omega) (by omega)
    have s16 := interfaces.selection 16 (by omega) (by omega)
    have nonstandard : (lift w) 10 = 0 ∧ (lift w) 11 = 0 ∧ (lift w) 12 = 0 := by
      cases hop : input.opcode <;>
        simp [hop, nonzero, AddSub.Modular.Opcode.selector] at s10 s11 s12
      all_goals exact ⟨s10, s11, s12⟩
    have selected : (lift w) 13 + (lift w) 14 + (lift w) 15 + (lift w) 16 = 1 := by
      cases hop : input.opcode <;>
        simp [hop, nonzero, AddSub.Modular.Opcode.selector] at s13 s14 s15 s16
      all_goals simp [s13, s14, s15, s16]
    have canonical : output.destination.value < babyBearModulus :=
      canonical_output core nonstandard.1 nonstandard.2.1 nonstandard.2.2 (disabled 2) selected
    apply AddSub.Proofs.modular_result_of_equations interfaces mapping nonzero canonical
    · have product := Verification.assertion_of_holds core ⟨1, by rw [constraint_count]; decide⟩
      simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] at product
      dsimp [lift]
      linear_combination product
    · have result := Verification.assertion_of_holds core ⟨2, by rw [constraint_count]; decide⟩
      simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] at result
      dsimp [lift]
      linear_combination result
  have next := UnifiedReduced.Proofs.pc_successor (p := babyBearModulus) (by decide)
    core active ⟨disabled 3, disabled 4, disabled 5, disabled 6⟩
    (initial := Control.initialPC w) (final := Control.finalPC w)
    ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩
    interfaces.initialPCBounds
  apply retire_of_destination interfaces.registers.pcRead next.2.2
  exact AddSub.Proofs.modular_destination
    (AddSub.Proofs.modular_contract_nextPC interfaces.registers output.pc.toBitVec) value

theorem execution_from_history
    {initial : State} {cells : List Cell} {seed : List (MemoryToken babyBearModulus)}
    (image : initialImage initial cells = some seed) (registers : ∀ index, Cell.register index ∈ cells)
    {setup : Table (ZMod babyBearModulus) (fields 10)} {w : Nat → ZMod babyBearModulus}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1)
    (bounds : ∀ i : Fin 3, (readToken w importedConstraintsMemoryPorts[i]).word.Bounded)
    {entry : ProgramEntry} (fields : mopDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (opcode : AddSub.Modular.Opcode) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = AddSub.Modular.instruction opcode rs1 rs2 rd)
    (epoch : Nat) {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily)).reverse before after) :
    run (normalStep (AddSub.Modular.clause opcode rs1 rs2 rd))
      (retiredState before (Control.initialPC w).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  have spec := spec_from_history (retired_state_image image (Control.initialPC w).toBitVec)
    registers core active bounds fields query opcode rs1 rs2 rd encoding epoch
    (retired_state_history past (Control.initialPC w).toBitVec)
    (retired_state_history history (Control.initialPC w).toBitVec) (retired_state_pc before _)
  have data := mop_metadata opcode rs1 rs2 rd fields encoding
  have flag := UnifiedReduced.Proofs.decoder_selectors (p := babyBearModulus) (by decide)
    core (mop_bounds fields).2.1 query 18
  rw [data] at flag
  have mask : (mopData opcode rs1 rs2 rd).mask.testBit 18 = false := by
    exact mop_high_flags opcode rs1 rs2 rd (11 : Fin 12)
  change w 29 = (if (mopData opcode rs1 rs2 rd).mask.testBit 18 then 1 else 0) at flag
  have noStore : w 29 = 0 := by
    rw [mask] at flag
    exact flag
  have rdEqual : entry.data.rd = rd := data ▸ AddSub.Modular.Proofs.native_rd opcode rs1 rs2 rd
  have index := (native_query_indices (p := babyBearModulus) (by decide) query).2.2
  rw [rdEqual] at index
  obtain ⟨final, normal, projected⟩ := spec
  have effects := UnifiedReduced.Proofs.register_effects core noStore index epoch
    ⟨Control.destination w, Control.finalPC w⟩ rfl history
  have same := (EStateM.Result.ok.inj (projected.symm.trans effects)).2
  rw [same] at normal
  exact normal

end Airbender.UnifiedReduced.Modular.Proofs
