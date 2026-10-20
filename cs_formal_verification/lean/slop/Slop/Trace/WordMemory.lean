import Slop.Trace.PortReads
import Slop.Trace.ROM
import Slop.WordMemory.MemoryAccess
import Slop.Sail.Memory
import Slop.Trace.CodeHistory
import Slop.Trace.PC
import Slop.Trace.Retirement

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem

/-- The local address equation is independent of the family registry. Shared
    history supplies its operand/address bounds and initialized RAM cell. -/
theorem local_word_address {p : Nat} [Fact p.Prime] (hp : ROM.limit < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} {cells : List Cell}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (WordMemory.importedConstraints setup))
    (store : Bool) (selected : w 10 = if store then 1 else 0)
    (source : (Word.mk (w 17).val (w 18).val).Bounded)
    (immediate : (Word.mk (w 8).val (w 9).val).Bounded)
    (bound : (Word.mk (w (if store then 25 else 19)).val (w (if store then 26 else 20)).val).Bounded)
    (cell : Cell.ram (Word.mk (w (if store then 25 else 19)).val
      (w (if store then 26 else 20)).val).toBitVec ∈ cells) :
    let address : Word := ⟨(w (if store then 25 else 19)).val, (w (if store then 26 else 20)).val⟩
    address.Bounded ∧ address.toBitVec = (Word.mk (w 17).val (w 18).val).toBitVec +
      (Word.mk (w 8).val (w 9).val).toBitVec ∧ Cell.ram address.toBitVec ∈ cells := by
  have addressInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  cases store
  all_goals refine ⟨bound, ?_, cell⟩
  all_goals
    exact WordMemory.Proofs.effective_address (by dsimp [ROM.limit] at hp; omega)
      addressInverse _ h selected
      ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm⟩ source immediate bound

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
  cases store
  all_goals
    dsimp only [Bool.false_eq_true, ite_false, ite_true] at selected ⊢
  · have present : WordMemory.importedConstraintsMemoryPorts[1] ∈
        (⟨.wordMemory, w⟩ : Row p).ports := by
      simp [Row.ports, WordMemory.importedConstraintsMemoryPorts]
    have bound := address_bounds clockSize inverse accepted boundary image _ member _ present
    change (Word.mk (w 19).val (w 20).val).Bounded at bound
    have cell := row_ram_cell clockSize inverse accepted boundary image member present
      (by refine ⟨Nat.pair (w 19).val (w 20).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected,
            pairCode, oneValue])
    exact local_word_address hp inverse core false selected source immediate bound cell.1

  · have present : WordMemory.importedConstraintsMemoryPorts[2] ∈
        (⟨.wordMemory, w⟩ : Row p).ports := by
      simp [Row.ports, WordMemory.importedConstraintsMemoryPorts]
    have bound := address_bounds clockSize inverse accepted boundary image _ member _ present
    change (Word.mk (w 25).val (w 26).val).Bounded at bound
    have cell := row_ram_cell clockSize inverse accepted boundary image member present
      (by refine ⟨Nat.pair (w 25).val (w 26).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected,
            pairCode, oneValue])
    exact local_word_address hp inverse core true selected source immediate bound cell.1
set_option backward.isDefEq.respectTransparency false in
/-- Shared word transport interprets the actual native transfer using the
    imported equations, canonical address and public memory configuration. -/
theorem local_word_transport {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (WordMemory.importedConstraints setup))
    (disabled : ∀ query, setup.Contains #[] query → query[8] = 0 → query[1] = 0 ∧ query[2] = 0)
    {cells : List Cell} (epoch : Nat)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (store : Bool) (selected : w 10 = if store then 1 else 0)
    {entry : ProgramEntry} (query : (⟨.wordMemory, w⟩ : Row p).decoderQuery = entry.query)
    (address : (Word.mk (w (if store then 25 else 19)).val (w (if store then 26 else 20)).val).Bounded ∧
      (Word.mk (w (if store then 25 else 19)).val (w (if store then 26 else 20)).val).toBitVec =
        (Word.mk (w 17).val (w 18).val).toBitVec + (Word.mk (w 8).val (w 9).val).toBitVec ∧
      Cell.ram (Word.mk (w (if store then 25 else 19)).val (w (if store then 26 else 20)).val).toBitVec ∈ cells)
    {before after : State} (configuration : FlatMemoryConfiguration before)
    (history : SailHistory cells (rowEvents epoch (⟨.wordMemory, w⟩ : Row p)).reverse before after)
    (native : if store then
      run (writeMemory (size := 4) (Word.mk (w 25).val (w 26).val).toBitVec
        (Word.mk (w 31).val (w 32).val).toBitVec) before = .ok () after
      else (readBytes (ue := SailRV32.exception) 4
        (Word.mk (w 19).val (w 20).val).toBitVec.toNat).run before =
          .ok (Word.mk (w 23).val (w 24).val).toBitVec before) :
    let immediate := (Word.mk (w 8).val (w 9).val).toBitVec
    let value := (Word.mk (w 23).val (w 24).val).toBitVec
    if store then
      run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before = .ok value before ∧
      run (SailRV32.Functions.vmem_write (.Regidx entry.data.rs1) immediate 4 value
        (.Store .Data) false false false) before = .ok (.Ok true) after
    else run (SailRV32.Functions.vmem_read (.Regidx entry.data.rs1) immediate 4
      (.Load .Data) false false false) before = .ok (.Ok value) before := by
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at *; omega
  have source := row_history_source_read limbSize epoch history query
    (port := WordMemory.importedConstraintsMemoryPorts[0]) rfl
  simp [WordMemory.importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord] at source
  cases store
  · simp at address selected native ⊢
    have alignment := aligned _ address.2.2
    have domain := ordinary _ address.2.2
    change (Word.mk (w 19).val (w 20).val).toBitVec.toNat % 4 = 0 at alignment
    rw [address.2.1] at alignment domain native
    exact virtual_word_read configuration _ _ source alignment domain native
  · simp at address selected native ⊢
    have alignment := aligned _ address.2.2
    have domain := ordinary _ address.2.2
    change (Word.mk (w 25).val (w 26).val).toBitVec.toNat % 4 = 0 at alignment
    rw [address.2.1] at alignment domain
    have register := word_history_register_read limbSize true core selected query epoch history
    simp only [ite_true] at register
    have classified := WordMemory.Proofs.rom_selection
      (by dsimp [ROM.limit] at hp; omega) true core selected
      (address := ⟨(w 25).val, (w 26).val⟩) (ZMod.natCast_zmod_val _).symm address.1
    have outside : ¬ (w 26).val < 64 := by
      have high := classified.2 rfl
      dsimp at high
      omega
    have ram : w 35 = 0 := by simpa [outside] using classified.1
    have copied := WordMemory.Proofs.ram_data disabled true core selected ram
    change w 31 = w 23 ∧ w 32 = w 24 at copied
    rw [copied.1, copied.2, address.2.1] at native
    have written := write_word_state before
      ((Word.mk (w 17).val (w 18).val).toBitVec + (Word.mk (w 8).val (w 9).val).toBitVec)
      (Word.mk (w 23).val (w 24).val).toBitVec
    have same := (EStateM.Result.ok.inj (written.symm.trans native)).2
    exact ⟨register, by rw [virtual_word_write configuration _ _ source alignment domain, same]⟩

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
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [ROM.limit, timestampBase] at *; omega
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at *; omega
  have oneValue : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by dsimp [ROM.limit] at hp; omega : 1 < p)
  have address := word_row_address hp inverse accepted boundary image setup member store selected fields query
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (WordMemory.importedConstraints trace.rom) WordMemory.importedConstraintsTimestampLookups)
  apply local_word_transport hp core (ROM.Proofs.value_boundary limbSize image setup).disabledROM
    trace.memoryEpoch aligned ordinary store selected query address configuration history
  cases store
  · simp only [Bool.false_eq_true, ite_false] at selected ⊢
    have bytes := row_history_ram_read clockSize inverse accepted boundary image member
      (port := WordMemory.importedConstraintsMemoryPorts[1])
      (by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts]) (by
        refine ⟨Nat.pair (w 19).val (w 20).val, ?_⟩
        simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue]) history
    simpa [WordMemory.importedConstraintsMemoryPorts, MemoryPort.readCode, memoryWord, pairCode, MemoryAddress.word] using bytes
  · simp only [ite_true] at selected ⊢
    have written := row_history_ram_write clockSize inverse accepted boundary image member
      (port := WordMemory.importedConstraintsMemoryPorts[2])
      (by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts]) rfl (by
        refine ⟨Nat.pair (w 25).val (w 26).val, ?_⟩
        simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue]) history
    simpa [WordMemory.importedConstraintsMemoryPorts, MemoryPort.writeCode, memoryWord, pairCode, MemoryAddress.word] using written

set_option backward.isDefEq.respectTransparency false in
/-- Invoke the original SW clause after the shared native transport proof. -/
theorem local_word_store_execution {p : Nat} [MemoryPlatform SailRV32.exception]
    (hp : limbBase < p) {w : Nat → ZMod p} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.wordMemory, w⟩ : Row p).decoderQuery = entry.query)
    {imm : BitVec 12} {rs1 rs2 : BitVec 5}
    (instruction : entry.instruction = .STORE (imm, .Regidx rs2, .Regidx rs1, 4))
    {before after : State}
    (transport : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before =
        .ok (Word.mk (w 23).val (w 24).val).toBitVec before ∧
      run (SailRV32.Functions.vmem_write (.Regidx entry.data.rs1)
        (Word.mk (w 8).val (w 9).val).toBitVec 4 (Word.mk (w 23).val (w 24).val).toBitVec
        (.Store .Data) false false false) before = .ok (.Ok true) after) :
    run (SailRV32.Functions.execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  have data : entry.data = ⟨.wordMemory, rs1, rs2, 0,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 1, 0⟩ := by
    rw [instruction] at fields
    exact (Option.some.inj fields).symm
  have immediate := query_immediate_value hp fields query
  change Word.mk (w 8).val (w 9).val = entry.data.immediate at immediate
  rw [data] at transport immediate
  have offset : (Word.mk (w 8).val (w 9).val).toBitVec =
      SailRV32.Functions.sign_extend (m := 32) imm :=
    (congrArg Word.toBitVec immediate).trans (Word.ofBitVec_roundtrip _)
  rw [offset] at transport
  exact store_word transport.1 transport.2

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
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 1, 0⟩ := by
    rw [instruction] at fields
    exact (Option.some.inj fields).symm
  have selected := query_selectors limbSize accepted member fields query
    ⟨0, by change 0 < 1; decide⟩
  change w 10 = if entry.data.mask.testBit 0 then 1 else 0 at selected
  simp only [data] at selected
  have transport := word_row_transport hp inverse accepted boundary image setup aligned
    ordinary member true selected fields query configuration history
  simp only [ite_true] at transport
  exact local_word_store_execution limbSize fields query instruction transport

set_option backward.isDefEq.respectTransparency false in
/-- Original LW execution uses the same imported equations and port history
    in every family registry. ROM values are tied to actual public bytes. -/
theorem local_word_load_execution {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (WordMemory.importedConstraints setup))
    (disabled : ∀ query, setup.Contains #[] query → query[8] = 0 → query[1] = 0 ∧ query[2] = 0)
    (active : w 4 = 1) (selected : w 10 = 0)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (family : entry.data.family = .wordMemory)
    (query : (⟨.wordMemory, w⟩ : Row p).decoderQuery = entry.query)
    {imm : BitVec 12} {rs1 rd : BitVec 5}
    (instruction : entry.instruction = .LOAD (imm, .Regidx rs1, .Regidx rd, false, 4))
    {cells : List Cell} (epoch : Nat)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (address : (Word.mk (w 19).val (w 20).val).Bounded ∧
      (Word.mk (w 19).val (w 20).val).toBitVec = (Word.mk (w 17).val (w 18).val).toBitVec +
        (Word.mk (w 8).val (w 9).val).toBitVec ∧ Cell.ram (Word.mk (w 19).val (w 20).val).toBitVec ∈ cells)
    {before after : State} (configuration : FlatMemoryConfiguration before)
    (romReads : ROM.Reads before setup)
    (history : SailHistory cells (rowEvents epoch (⟨.wordMemory, w⟩ : Row p)).reverse before after)
    (native : (readBytes (ue := SailRV32.exception) 4
      (Word.mk (w 19).val (w 20).val).toBitVec.toNat).run before =
        .ok (Word.mk (w 23).val (w 24).val).toBitVec before) :
    run (SailRV32.Functions.execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 4) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at *; omega
  have data : entry.data = ⟨.wordMemory, rs1, 0, rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 0⟩ := by
    rw [instruction] at fields
    change (if rd = 0 then some (arithmeticFields 0 0 0 0 1) else some
      ⟨.wordMemory, rs1, 0, rd, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 0⟩) =
        some entry.data at fields
    split at fields
    · have equal := (Option.some.inj fields).symm
      rw [equal] at family
      cases family
    · exact (Option.some.inj fields).symm
  have classified := WordMemory.Proofs.rom_selection
    (by dsimp [ROM.limit] at hp; omega) false core selected
    (address := ⟨(w 19).val, (w 20).val⟩) (ZMod.natCast_zmod_val _).symm address.1
  have bytes : (readBytes (ue := SailRV32.exception) 4
      ((Word.mk (w 17).val (w 18).val).toBitVec +
        (Word.mk (w 8).val (w 9).val).toBitVec).toNat).run before =
      .ok (Word.mk (w 31).val (w 32).val).toBitVec before := by
    by_cases inROM : (w 20).val < 64
    · have flag : w 35 = 1 := by simpa [inROM] using classified.1
      have active : w 4 = 1 := active
      have lookup := WordMemory.Proofs.rom_data core selected active flag
      have rom := romReads ⟨(w 19).val, (w 20).val⟩ (w 31) (w 32) address.1 inROM
        (by simpa only [ZMod.natCast_zmod_val] using lookup)
      rw [address.2.1] at rom
      exact rom
    · have flag : w 35 = 0 := by simpa [inROM] using classified.1
      have copied := WordMemory.Proofs.ram_data
        disabled false core selected flag
      have nativeRead := native
      rw [address.2.1] at nativeRead
      change w 31 = w 23 ∧ w 32 = w 24 at copied
      simpa only [copied.1, copied.2] using nativeRead
  have source := row_history_source_read limbSize epoch history query
    (port := WordMemory.importedConstraintsMemoryPorts[0]) rfl
  simp [WordMemory.importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode,
    memoryWord] at source
  have memory := virtual_word_read configuration _ _ source
    (by rw [← address.2.1]; exact aligned _ address.2.2)
    (by rw [← address.2.1]; exact ordinary _ address.2.2) bytes
  have written := word_history_load_write limbSize core selected query epoch history
  have immediate := query_immediate_value limbSize fields query
  change Word.mk (w 8).val (w 9).val = entry.data.immediate at immediate
  rw [data] at immediate memory written
  have offset : (Word.mk (w 8).val (w 9).val).toBitVec =
      SailRV32.Functions.sign_extend (m := 32) imm :=
    (congrArg Word.toBitVec immediate).trans (Word.ofBitVec_roundtrip _)
  rw [offset] at memory
  have executed := load_word (rd := .Regidx rd) memory
  refine executed.trans ?_
  rw [run_bind_of_ok _ _ _ _ _ written]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Original LW execution agrees with the native destination update, including
    aliases and ROM loads. The public image and earlier native history supply
    both the current configuration and ROM byte binding. -/
theorem word_row_load_execution [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (family : entry.data.family = .wordMemory)
    (query : (⟨.wordMemory, w⟩ : Row p).decoderQuery = entry.query)
    {imm : BitVec 12} {rs1 rd : BitVec 5}
    (instruction : entry.instruction = .LOAD (imm, .Regidx rs1, .Regidx rd, false, 4))
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells
      (rowEvents trace.memoryEpoch (⟨.wordMemory, w⟩ : Row p)).reverse before after) :
    run (SailRV32.Functions.execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 4) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at *; omega
  have data : entry.data.mask = 0 := by
    rw [instruction] at fields
    change (if rd = 0 then some (arithmeticFields 0 0 0 0 1) else some
      ⟨.wordMemory, rs1, 0, rd, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 0⟩) =
        some entry.data at fields
    split at fields
    · have equal := (Option.some.inj fields).symm
      rw [equal] at family
      cases family
    · rw [← Option.some.inj fields]
  have selected := query_selectors limbSize accepted member fields query ⟨0, by change 0 < 1; decide⟩
  change w 10 = if entry.data.mask.testBit 0 then 1 else 0 at selected
  simp only [data] at selected
  have address := word_row_address hp inverse accepted boundary image setup member false selected fields query
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (WordMemory.importedConstraints trace.rom) WordMemory.importedConstraintsTimestampLookups)
  have nativeRead := row_history_ram_read
    (by dsimp [ROM.limit, timestampBase] at *; omega) inverse accepted boundary image member
    (port := WordMemory.importedConstraintsMemoryPorts[1])
    (by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts]) (by
      refine ⟨Nat.pair (w 19).val (w 20).val, ?_⟩
      have oneValue : (1 : ZMod p).val = 1 := by
        simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by dsimp [ROM.limit] at hp; omega : 1 < p)
      simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue]) history
  apply local_word_load_execution hp core (ROM.Proofs.value_boundary limbSize image setup).disabledROM
    (accepted.active _ member) selected fields family query instruction trace.memoryEpoch aligned ordinary address
    (history_configuration past configuration)
    (rom_reads_after_native_history hp inverse accepted boundary image setup aligned native past) history
  simpa [WordMemory.importedConstraintsMemoryPorts, MemoryPort.readCode, memoryWord, pairCode, MemoryAddress.word] using nativeRead

set_option backward.isDefEq.respectTransparency false in
/-- Compose the derived SW clause with original PC preparation/retirement.
    The current configuration follows from the initialized native history. -/
theorem word_row_store_step [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial) (initialPC : trace.initial.word.Bounded)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.wordMemory, w⟩ : Row p).decoderQuery = entry.query)
    {imm : BitVec 12} {rs1 rs2 : BitVec 5}
    (instruction : entry.instruction = .STORE (imm, .Regidx rs2, .Regidx rs1, 4))
    {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (history : SailHistory cells
      (rowEvents trace.memoryEpoch (⟨.wordMemory, w⟩ : Row p)).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before =
      .ok (Word.mk (w 0).val (w 1).val).toBitVec before) :
    let finalPC := (Word.mk (w 11).val (w 12).val).toBitVec
    run (normalStep (SailRV32.Functions.execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4)) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        { after with regs := after.regs.insert .nextPC finalPC |>.insert .PC finalPC } := by
  let currentPC := (Word.mk (w 0).val (w 1).val).toBitVec
  have prepared := sail_history_control history .nextPC (.inr rfl) (currentPC + 4)
  have executed := word_row_store_execution hp inverse accepted boundary image setup aligned ordinary
    member fields query instruction
    (configuration_next_pc_write (history_configuration past configuration) (currentPC + 4)) prepared
  have normal := normal_step_native (pc := currentPC) _ pc executed
  have successor := row_pc_successor (by dsimp [ROM.limit, timestampBase] at hp ⊢; omega)
    inverse accepted initialPC member
  change (Word.mk (w 11).val (w 12).val).toBitVec = currentPC + 4 at successor
  rw [← successor] at normal
  exact normal

set_option backward.isDefEq.respectTransparency false in
/-- The same complete native step for LW, including aliased source/destination
    registers and preserved public ROM bytes. Preparation preserves the initial
    image and both histories, so memory transport needs no new read premise. -/
theorem word_row_load_step [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial) (initialPC : trace.initial.word.Bounded)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (family : entry.data.family = .wordMemory)
    (query : (⟨.wordMemory, w⟩ : Row p).decoderQuery = entry.query)
    {imm : BitVec 12} {rs1 rd : BitVec 5}
    (instruction : entry.instruction = .LOAD (imm, .Regidx rs1, .Regidx rd, false, 4))
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells
      (rowEvents trace.memoryEpoch (⟨.wordMemory, w⟩ : Row p)).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before =
      .ok (Word.mk (w 0).val (w 1).val).toBitVec before) :
    let finalPC := (Word.mk (w 11).val (w 12).val).toBitVec
    run (normalStep (SailRV32.Functions.execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 4)) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        { after with regs := after.regs.insert .nextPC finalPC |>.insert .PC finalPC } := by
  let currentPC := (Word.mk (w 0).val (w 1).val).toBitVec
  have prepared := sail_history_control history .nextPC (.inr rfl) (currentPC + 4)
  have preparedPast := sail_history_control past .nextPC (.inr rfl) (currentPC + 4)
  have preparedImage := initial_image_control image .nextPC (.inr rfl) (currentPC + 4)
  have executed := word_row_load_execution hp inverse accepted boundary preparedImage setup aligned ordinary
    (configuration_next_pc_write configuration (currentPC + 4))
    member fields family query instruction native preparedPast prepared
  have normal := normal_step_native (pc := currentPC) _ pc executed
  have successor := row_pc_successor (by dsimp [ROM.limit, timestampBase] at hp ⊢; omega)
    inverse accepted initialPC member
  change (Word.mk (w 11).val (w 12).val).toBitVec = currentPC + 4 at successor
  rw [← successor] at normal
  exact normal

set_option backward.isDefEq.respectTransparency false in
/-- Native history transport supplies this row's Sail PC read. The complete
    native path then composes these actual instruction-boundary states. -/
theorem word_rebased_store_step [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial) (initialPC : trace.initial.word.Bounded)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.wordMemory, w⟩ : Row p).decoderQuery = entry.query)
    {imm : BitVec 12} {rs1 rs2 : BitVec 5}
    (instruction : entry.instruction = .STORE (imm, .Regidx rs2, .Regidx rs1, 4))
    {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (history : SailHistory cells
      (rowEvents trace.memoryEpoch (⟨.wordMemory, w⟩ : Row p)).reverse before after)
    :
    let currentPC := (Word.mk (w 0).val (w 1).val).toBitVec
    let finalPC := (Word.mk (w 11).val (w 12).val).toBitVec
    run (normalStep (SailRV32.Functions.execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4)) (retiredState before currentPC) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after finalPC) := by
  let currentPC := (Word.mk (w 0).val (w 1).val).toBitVec
  let finalPC := (Word.mk (w 11).val (w 12).val).toBitVec
  have checked := word_row_store_step hp inverse accepted boundary
    (retired_state_image image currentPC) setup aligned ordinary
    (retired_state_configuration configuration currentPC) initialPC
    member fields query instruction (retired_state_history past currentPC)
    (retired_state_history history currentPC) (retired_state_pc before currentPC)
  change run (normalStep (SailRV32.Functions.execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4)) (retiredState before currentPC) =
    .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (retiredState after currentPC) finalPC) at checked
  rw [retired_state_overwrite] at checked
  exact checked

set_option backward.isDefEq.respectTransparency false in
/-- Native history transport supplies this row's Sail PC read. The complete
    native path then composes these actual instruction-boundary states. -/
theorem word_rebased_load_step [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial) (initialPC : trace.initial.word.Bounded)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (family : entry.data.family = .wordMemory)
    (query : (⟨.wordMemory, w⟩ : Row p).decoderQuery = entry.query)
    {imm : BitVec 12} {rs1 rd : BitVec 5}
    (instruction : entry.instruction = .LOAD (imm, .Regidx rs1, .Regidx rd, false, 4))
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells
      (rowEvents trace.memoryEpoch (⟨.wordMemory, w⟩ : Row p)).reverse before after)
    :
    let currentPC := (Word.mk (w 0).val (w 1).val).toBitVec
    let finalPC := (Word.mk (w 11).val (w 12).val).toBitVec
    run (normalStep (SailRV32.Functions.execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 4)) (retiredState before currentPC) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after finalPC) := by
  let currentPC := (Word.mk (w 0).val (w 1).val).toBitVec
  let finalPC := (Word.mk (w 11).val (w 12).val).toBitVec
  have checked := word_row_load_step hp inverse accepted boundary
    (retired_state_image image currentPC) setup aligned ordinary
    (retired_state_configuration configuration currentPC) initialPC
    member fields family query instruction native (retired_state_history past currentPC)
    (retired_state_history history currentPC) (retired_state_pc before currentPC)
  change run (normalStep (SailRV32.Functions.execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 4)) (retiredState before currentPC) =
    .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (retiredState after currentPC) finalPC) at checked
  rw [retired_state_overwrite] at checked
  exact checked

end Airbender.Trace.Proofs
