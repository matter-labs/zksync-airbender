import Airbender.Proofs.Trace.PortReads
import Airbender.Proofs.Trace.ROM
import Airbender.Proofs.WordMemory.MemoryAccess
import Airbender.Proofs.Sail.Memory

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem

/-- Native memory consistency supplies the address bounds, operand bounds and
    RAM cell. The imported arithmetic equations then identify the effective
    address; neither an expected address nor a desired read is assumed. -/
theorem word_row_address [Fact p.Prime] (hp : ROM.limit < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p) ∈ trace.rows)
    (store : Bool) (selected : w 10 = if store then 1 else 0)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.wordMemory, w⟩ : Row p).decoderQuery = entry.query) :
    let address : Word := ⟨(w (if store then 25 else 19)).val,
      (w (if store then 26 else 20)).val⟩
    address.Bounded ∧
      address.toBitVec = (Word.mk (w 17).val (w 18).val).toBitVec +
        (Word.mk (w 8).val (w 9).val).toBitVec ∧
      Cell.ram address.toBitVec ∈ cells := by
  have clockSize : 2 * timestampBase + 4 < p := by
    dsimp [ROM.limit, timestampBase] at *; omega
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at *; omega
  have oneValue : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using
      (ZMod.val_natCast_of_lt (by dsimp [ROM.limit] at hp; omega : 1 < p))
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (WordMemory.importedConstraints trace.rom)
      WordMemory.importedConstraintsTimestampLookups)
  have source := read_bounds clockSize inverse accepted boundary
    (ROM.Proofs.value_boundary limbSize image setup) _ member
    WordMemory.importedConstraintsMemoryPorts[0]
    (by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts])
  rw [read_word] at source
  change (Word.mk (w 17).val (w 18).val).Bounded at source
  have immediate := query_immediate limbSize fields query
  change (Word.mk (w 8).val (w 9).val).Bounded at immediate
  have addressInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  cases store
  all_goals
    dsimp only [Bool.false_eq_true, if_false, if_true] at selected ⊢
  · have present : WordMemory.importedConstraintsMemoryPorts[1] ∈
        (⟨.wordMemory, w⟩ : Row p).ports := by
      simp [Row.ports, WordMemory.importedConstraintsMemoryPorts]
    have bound := address_bounds clockSize inverse accepted boundary image _ member _ present
    change (Word.mk (w 19).val (w 20).val).Bounded at bound
    have cell := row_ram_cell clockSize inverse accepted boundary image member present
      (by refine ⟨Nat.pair (w 19).val (w 20).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected,
            pairCode, oneValue])
    refine ⟨bound, ?_, cell.1⟩
    exact WordMemory.Proofs.effective_address (by dsimp [ROM.limit] at hp; omega)
      addressInverse false core selected
      ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm⟩ source immediate bound
  · have present : WordMemory.importedConstraintsMemoryPorts[2] ∈
        (⟨.wordMemory, w⟩ : Row p).ports := by
      simp [Row.ports, WordMemory.importedConstraintsMemoryPorts]
    have bound := address_bounds clockSize inverse accepted boundary image _ member _ present
    change (Word.mk (w 25).val (w 26).val).Bounded at bound
    have cell := row_ram_cell clockSize inverse accepted boundary image member present
      (by refine ⟨Nat.pair (w 25).val (w 26).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected,
            pairCode, oneValue])
    refine ⟨bound, ?_, cell.1⟩
    exact WordMemory.Proofs.effective_address (by dsimp [ROM.limit] at hp; omega)
      addressInverse true core selected
      ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm⟩ source immediate bound

set_option backward.isDefEq.respectTransparency false in
/-- Discharge Sail's virtual memory calls for a grouped native row. Alignment
    and ordinary-memory conditions belong to the public cell domain; the read
    values and final native state are derived from its accepted history. -/
theorem word_row_transport [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p) ∈ trace.rows)
    (store : Bool) (selected : w 10 = if store then 1 else 0)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.wordMemory, w⟩ : Row p).decoderQuery = entry.query)
    {before after : State} (configuration : FlatMemoryConfiguration before)
    (history : SailHistory cells
      (rowEvents trace.memoryEpoch (⟨.wordMemory, w⟩ : Row p)).reverse before after) :
    let immediate := (Word.mk (w 8).val (w 9).val).toBitVec
    let value := (Word.mk (w 23).val (w 24).val).toBitVec
    if store then
      run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before = .ok value before ∧
      run (SailRV32.Functions.vmem_write (.Regidx entry.data.rs1) immediate 4 value
        (.Store .Data) false false false) before = .ok (.Ok true) after
    else
      run (SailRV32.Functions.vmem_read (.Regidx entry.data.rs1) immediate 4
        (.Load .Data) false false false) before = .ok (.Ok value) before := by
  have clockSize : 2 * timestampBase + 4 < p := by
    dsimp [ROM.limit, timestampBase] at *; omega
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at *; omega
  have oneValue : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using
      (ZMod.val_natCast_of_lt (by dsimp [ROM.limit] at hp; omega : 1 < p))
  have address := word_row_address hp inverse accepted boundary image setup member
    store selected fields query
  have source := row_history_source_read limbSize trace.memoryEpoch history query
    (port := WordMemory.importedConstraintsMemoryPorts[0]) rfl
  simp [WordMemory.importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode,
    memoryWord] at source
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (WordMemory.importedConstraints trace.rom)
      WordMemory.importedConstraintsTimestampLookups)
  have values := ROM.Proofs.value_boundary limbSize image setup
  cases store
  · simp at address selected ⊢
    have alignment := aligned _ address.2.2
    have domain := ordinary _ address.2.2
    change (Word.mk (w 19).val (w 20).val).toBitVec.toNat % 4 = 0 at alignment
    rw [address.2.1] at alignment domain
    have present : WordMemory.importedConstraintsMemoryPorts[1] ∈
        (⟨.wordMemory, w⟩ : Row p).ports := by
      simp [Row.ports, WordMemory.importedConstraintsMemoryPorts]
    have bytes := row_history_ram_read clockSize inverse accepted boundary image
      member present (by
        refine ⟨Nat.pair (w 19).val (w 20).val, ?_⟩
        simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected,
          pairCode, oneValue]) history
    change (readBytes (ue := SailRV32.exception) 4
      (Word.mk (w 19).val (w 20).val).toBitVec.toNat).run before =
        .ok (memoryWord (Nat.pair (w 23).val (w 24).val)) before at bytes
    simp only [memoryWord, Nat.unpair_pair] at bytes
    rw [address.2.1] at bytes
    exact virtual_word_read configuration _ _ source alignment domain bytes
  · simp at address selected ⊢
    have alignment := aligned _ address.2.2
    have domain := ordinary _ address.2.2
    change (Word.mk (w 25).val (w 26).val).toBitVec.toNat % 4 = 0 at alignment
    rw [address.2.1] at alignment domain
    have register := word_history_register_read limbSize true core selected query
      trace.memoryEpoch history
    simp only [if_true] at register
    have classified := WordMemory.Proofs.rom_selection
      (by dsimp [ROM.limit] at hp; omega) true core selected
      (address := ⟨(w 25).val, (w 26).val⟩)
      (ZMod.natCast_zmod_val _).symm address.1
    have outside : ¬ (w 26).val < 64 := by
      have high := classified.2 rfl
      dsimp at high
      omega
    have ram : w 35 = 0 := by simpa [outside] using classified.1
    have copied := WordMemory.Proofs.ram_data values.disabledROM true core selected ram
    have written := row_history_ram_write clockSize inverse accepted boundary image member
      (port := WordMemory.importedConstraintsMemoryPorts[2])
      (by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts]) rfl
      (by
        refine ⟨Nat.pair (w 25).val (w 26).val, ?_⟩
        simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected,
          pairCode, oneValue]) history
    change run (writeMemory (size := 4) (Word.mk (w 25).val (w 26).val).toBitVec
      (memoryWord (Nat.pair (w 31).val (w 32).val))) before = .ok () after at written
    simp only [memoryWord, Nat.unpair_pair] at written
    change w 31 = w 23 ∧ w 32 = w 24 at copied
    rw [copied.1, copied.2, address.2.1] at written
    have native := write_word_state before
      ((Word.mk (w 17).val (w 18).val).toBitVec + (Word.mk (w 8).val (w 9).val).toBitVec)
      (Word.mk (w 23).val (w 24).val).toBitVec
    have same := (EStateM.Result.ok.inj (native.symm.trans written)).2
    exact ⟨register, by
      rw [virtual_word_write configuration _ _ source alignment domain, same]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The original decoded SW clause reaches the native row's actual after-state.
    Its source reads, immediate and store selector are derived, not assumed. -/
theorem word_row_store_execution [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.wordMemory, w⟩ : Row p).decoderQuery = entry.query)
    {imm : BitVec 12} {rs1 rs2 : BitVec 5}
    (instruction : entry.instruction = .STORE (imm, .Regidx rs2, .Regidx rs1, 4))
    {before after : State} (configuration : FlatMemoryConfiguration before)
    (history : SailHistory cells
      (rowEvents trace.memoryEpoch (⟨.wordMemory, w⟩ : Row p)).reverse before after) :
    run (SailRV32.Functions.execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at *; omega
  have data : entry.data = ⟨.wordMemory, rs1, rs2, 0,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 1⟩ := by
    rw [instruction] at fields
    exact (Option.some.inj fields).symm
  have selected := query_selectors limbSize accepted member fields query
    ⟨0, by change 0 < 1; decide⟩
  change w 10 = if entry.data.mask.testBit 0 then 1 else 0 at selected
  simp only [data] at selected
  have transport := word_row_transport hp inverse accepted boundary image setup aligned
    ordinary member true selected fields query configuration history
  simp only [if_true] at transport
  have immediate := query_immediate_value limbSize fields query
  change Word.mk (w 8).val (w 9).val = entry.data.immediate at immediate
  rw [data] at transport immediate
  have offset : (Word.mk (w 8).val (w 9).val).toBitVec =
      SailRV32.Functions.sign_extend (m := 32) imm :=
    (congrArg Word.toBitVec immediate).trans (Word.ofBitVec_roundtrip _)
  rw [offset] at transport
  exact store_word transport.1 transport.2

end Airbender.Trace.Proofs
