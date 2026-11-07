import Slop.Bigint.RVOperation
import Slop.Bigint.Addresses
import Slop.Delegation.RVCallLink
import Slop.Delegation.RVCallHistory
import Slop.Delegation.RVNativeViews

/-! The delegate link of one bigint row: the row's RV call (its accesses run from `start` to `finish`) is the spec's
    bigint call `RV.Delegation.bigint` from `start`, up to the spec's PC advance. Every guard of the spec call comes
    from the circuit: x10/x11 32-aligned (`pointer_alignment`), canonical (their indirect ports address tracked cells),
    distinct (`seed_row_addresses_distinct`), the x12 control byte (`row_operation`). RAM is RAM at any address, the
    shadow RAM below `ROM_END` included. -/

namespace Airbender.Bigint.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Native
set_option warningAsError true
set_option maxRecDepth 16384

theorem port_shapes :
    importedConstraintsMemoryPorts[0].address = .constantRegister 10 ∧ importedConstraintsMemoryPorts[9].address = .constantRegister 11 ∧
      importedConstraintsMemoryPorts[18].address = .constantRegister 12 ∧
      (∀ i : Fin 8, (importedConstraintsMemoryPorts[1 + i.val]'(by change 1 + i.val < 19; omega)).address = .indirect (importedConstraintsIndirectPorts[i.val]'(by omega)) ∧
        (importedConstraintsMemoryPorts[10 + i.val]'(by change 10 + i.val < 19; omega)).address = .indirect (importedConstraintsIndirectPorts[8 + i.val]'(by omega))) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i
  fin_cases i <;> exact ⟨rfl, rfl⟩

/-- x10, x11 and the x11 block are read-only ports: they write back what they read. -/
theorem readonly_ports {p : Nat} (w : Nat → ZMod p) :
    importedConstraintsMemoryPorts[0].writeCode w = importedConstraintsMemoryPorts[0].readCode w ∧ importedConstraintsMemoryPorts[9].writeCode w = importedConstraintsMemoryPorts[9].readCode w ∧
      ∀ i : Fin 8, (importedConstraintsMemoryPorts[10 + i.val]'(by change 10 + i.val < 19; omega)).writeCode w =
        (importedConstraintsMemoryPorts[10 + i.val]'(by change 10 + i.val < 19; omega)).readCode w := by
  refine ⟨rfl, rfl, ?_⟩
  intro i
  fin_cases i <;> rfl

theorem port_values {p : Nat} (w : Nat → ZMod p) :
    memoryWord (importedConstraintsMemoryPorts[0].readCode w) = (⟨(w 3).val, (w 4).val⟩ : Word).toBitVec ∧
      memoryWord (importedConstraintsMemoryPorts[9].readCode w) = (⟨(w 37).val, (w 38).val⟩ : Word).toBitVec ∧
      memoryWord (importedConstraintsMemoryPorts[18].readCode w) = (⟨(w 55).val, (w 56).val⟩ : Word).toBitVec ∧
      memoryWord (importedConstraintsMemoryPorts[18].writeCode w) = (⟨(w 57).val, (w 58).val⟩ : Word).toBitVec := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [memoryWord, MemoryPort.readCode, MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate,
      importedConstraintsMemoryPorts]

theorem expected_left (input : Addresses.Input) (i : Fin 8) :
    (Addresses.expected input)[i.val] = input.left.toBitVec + BitVec.ofNat 32 (4 * i.val) := by
  simp [Addresses.expected, Vector.append]

theorem expected_right (input : Addresses.Input) (i : Fin 8) :
    (Addresses.expected input)[8 + i.val] = input.right.toBitVec + BitVec.ofNat 32 (4 * i.val) := by
  simp [Addresses.expected, Vector.append]

/-- A cell named by an indirect port has canonical address limbs. -/
theorem indirect_bounded {p : Nat} {w : Nat → ZMod p} {port : Verification.IndirectPort} {cell : Cell}
    (code : cell.addressCode = (MemoryAddress.indirect port).code w) :
    (⟨(port.rawAddress w).1.val, (port.rawAddress w).2.val⟩ : Word).Bounded := by
  have word := address_word code.symm
  have same := indirect_cell code
  subst same
  simp only [MemoryAddress.word, Cell.addressWord] at word
  rw [word]
  exact Word.ofBitVec_bound _

/-- Every native port of a bigint row names x10, x11, x12, or a word of the x10 or x11 block. -/
theorem port_cell {p : Nat} {w : Nat → ZMod p} {x10 x11 : BitVec 32}
    (left : ∀ i : Fin 8, (importedConstraintsIndirectPorts[i.val]'(by omega)).address w = x10 + BitVec.ofNat 32 (4 * i.val))
    (right : ∀ i : Fin 8, (importedConstraintsIndirectPorts[8 + i.val]'(by omega)).address w = x11 + BitVec.ofNat 32 (4 * i.val))
    {cell : Cell} (k : Fin 19) (code : cell.addressCode = (importedConstraintsMemoryPorts[k.val]'(by change k.val < 19; omega)).address.code w) :
    cell = .register 10 ∨ cell = .register 11 ∨ cell = .register 12 ∨
      ∃ j : Fin 8, cell = .ram (x10 + BitVec.ofNat 32 (4 * j.val)) ∨
        cell = .ram (x11 + BitVec.ofNat 32 (4 * j.val)) := by
  have block (j : Fin 8) (code : cell.addressCode = (MemoryAddress.indirect (importedConstraintsIndirectPorts[j.val]'(by omega))).code w) :
      ∃ j : Fin 8, cell = .ram (x10 + BitVec.ofNat 32 (4 * j.val)) ∨
        cell = .ram (x11 + BitVec.ofNat 32 (4 * j.val)) :=
    ⟨j, Or.inl ((indirect_cell code).trans (congrArg Cell.ram (left j)))⟩
  have block' (j : Fin 8) (code : cell.addressCode = (MemoryAddress.indirect (importedConstraintsIndirectPorts[8 + j.val]'(by omega))).code w) :
      ∃ j : Fin 8, cell = .ram (x10 + BitVec.ofNat 32 (4 * j.val)) ∨
        cell = .ram (x11 + BitVec.ofNat 32 (4 * j.val)) :=
    ⟨j, Or.inr ((indirect_cell code).trans (congrArg Cell.ram (right j)))⟩
  fin_cases k
  · exact Or.inl (cell_address_injective code)
  · exact Or.inr (Or.inr (Or.inr (block 0 code)))
  · exact Or.inr (Or.inr (Or.inr (block 1 code)))
  · exact Or.inr (Or.inr (Or.inr (block 2 code)))
  · exact Or.inr (Or.inr (Or.inr (block 3 code)))
  · exact Or.inr (Or.inr (Or.inr (block 4 code)))
  · exact Or.inr (Or.inr (Or.inr (block 5 code)))
  · exact Or.inr (Or.inr (Or.inr (block 6 code)))
  · exact Or.inr (Or.inr (Or.inr (block 7 code)))
  · exact Or.inr (Or.inl (cell_address_injective code))
  · exact Or.inr (Or.inr (Or.inr (block' 0 code)))
  · exact Or.inr (Or.inr (Or.inr (block' 1 code)))
  · exact Or.inr (Or.inr (Or.inr (block' 2 code)))
  · exact Or.inr (Or.inr (Or.inr (block' 3 code)))
  · exact Or.inr (Or.inr (Or.inr (block' 4 code)))
  · exact Or.inr (Or.inr (Or.inr (block' 5 code)))
  · exact Or.inr (Or.inr (Or.inr (block' 6 code)))
  · exact Or.inr (Or.inr (Or.inr (block' 7 code)))
  · exact Or.inr (Or.inr (Or.inl (cell_address_injective code)))

/-- A bigint call's RV history leaves every register but x10/x11/x12 and every RAM word outside both blocks. -/
theorem rv_row_frame {p : Nat} {w : Nat → ZMod p} {x10 x11 : BitVec 32}
    (left : ∀ i : Fin 8, (importedConstraintsIndirectPorts[i.val]'(by omega)).address w = x10 + BitVec.ofNat 32 (4 * i.val))
    (right : ∀ i : Fin 8, (importedConstraintsIndirectPorts[8 + i.val]'(by omega)).address w = x11 + BitVec.ofNat 32 (4 * i.val))
    {before after : RV.State} {cells : List Cell} {events : List MemoryAccess}
    (history : RVHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .bigint w).memorySteps.map transferEvent))
    (observed : ∀ port ∈ importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    (∀ r : BitVec 5, r ≠ 10 → r ≠ 11 → r ≠ 12 → after.getReg r = before.getReg r) ∧
    (∀ a : BitVec 32, a.toNat % 4 = 0 → (∀ j : Fin 8, a ≠ x10 + BitVec.ofNat 32 (4 * j.val)) →
      (∀ j : Fin 8, a ≠ x11 + BitVec.ofNat 32 (4 * j.val)) → RV.read after.mem a 4 = RV.read before.mem a 4) := by
  have touched : ∀ event ∈ events, ∃ cell : Cell, cell.addressCode = event.2.1 ∧
      (cell = .register 10 ∨ cell = .register 11 ∨ cell = .register 12 ∨
        ∃ j : Fin 8, cell = .ram (x10 + BitVec.ofNat 32 (4 * j.val)) ∨
          cell = .ram (x11 + BitVec.ofNat 32 (4 * j.val))) := by
    intro event present
    obtain ⟨edge, included, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp present)
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp included
    have member : port ∈ importedConstraintsMemoryPorts := by
      simpa only [Delegation.Row.ports, Array.mem_toList_iff] using portMember
    obtain ⟨i, bound, equal⟩ := Array.mem_iff_getElem.mp member
    obtain ⟨cell, code⟩ := observed port member
    refine ⟨cell, code, ?_⟩
    subst equal
    exact port_cell left right ⟨i, bound⟩ code
  constructor
  · intro r r10 r11 r12
    have untouched : ∀ event ∈ events, event.2.1 ≠ (Cell.register r).addressCode := by
      intro event present same
      obtain ⟨cell, code, kind⟩ := touched event present
      have equal : cell = .register r := cell_address_injective (code.trans same)
      subst equal
      rcases kind with h | h | h | ⟨j, h | h⟩
      · exact r10 (Cell.register.inj h)
      · exact r11 (Cell.register.inj h)
      · exact r12 (Cell.register.inj h)
      · cases h
      · cases h
    have frame := rv_history_cell_frame history aligned (.register r) trivial untouched (readRV_register r before)
    rw [readRV_register] at frame
    exact Option.some.inj frame
  · intro a alignedA outside10 outside11
    have untouched : ∀ event ∈ events, event.2.1 ≠ (Cell.ram a).addressCode := by
      intro event present same
      obtain ⟨cell, code, kind⟩ := touched event present
      have equal : cell = .ram a := cell_address_injective (code.trans same)
      subst equal
      rcases kind with h | h | h | ⟨j, h | h⟩
      · cases h
      · cases h
      · cases h
      · exact outside10 j (Cell.ram.inj h)
      · exact outside11 j (Cell.ram.inj h)
    have readable := readable_of_aligned (address := a) alignedA
    have frame := rv_history_cell_frame history aligned (.ram a) alignedA untouched (readRV_ram before readable)
    rw [readRV_ram after readable] at frame
    exact Option.some.inj frame

private theorem register_value {p : Nat} {w : Nat → ZMod p} {cells : List Cell} {before after : RV.State}
    {index : BitVec 5} (k : Nat) (hk : k < 19)
    (address : (importedConstraintsMemoryPorts[k]'hk).address.code w = (Cell.register index).addressCode)
    (ports : ∀ port ∈ importedConstraintsMemoryPorts, ∃ cell ∈ cells,
      cell.addressCode = port.address.code w ∧
      cell.readRV before = some (memoryWord (port.readCode w)) ∧
      cell.readRV after = some (memoryWord (port.writeCode w))) :
    before.getReg index = memoryWord ((importedConstraintsMemoryPorts[k]'hk).readCode w) ∧
      after.getReg index = memoryWord ((importedConstraintsMemoryPorts[k]'hk).writeCode w) := by
  obtain ⟨cell, _, code, readBefore, readAfter⟩ :=
    ports (importedConstraintsMemoryPorts[k]'hk) (Array.getElem_mem hk)
  have same : cell = .register index := cell_address_injective (code.trans address)
  subst same
  rw [readRV_register] at readBefore readAfter
  exact ⟨Option.some.inj readBefore, Option.some.inj readAfter⟩

private theorem ram_value {p : Nat} {w : Nat → ZMod p} {cells : List Cell} {before after : RV.State}
    {indirect : Verification.IndirectPort} (k : Nat) (hk : k < 19)
    (shape : (importedConstraintsMemoryPorts[k]'hk).address = .indirect indirect)
    (ports : ∀ port ∈ importedConstraintsMemoryPorts, ∃ cell ∈ cells,
      cell.addressCode = port.address.code w ∧
      cell.readRV before = some (memoryWord (port.readCode w)) ∧
      cell.readRV after = some (memoryWord (port.writeCode w))) :
    (⟨(indirect.rawAddress w).1.val, (indirect.rawAddress w).2.val⟩ : Word).Bounded ∧
      RV.read before.mem (indirect.address w) 4 = memoryWord ((importedConstraintsMemoryPorts[k]'hk).readCode w) ∧
      RV.read after.mem (indirect.address w) 4 = memoryWord ((importedConstraintsMemoryPorts[k]'hk).writeCode w) := by
  obtain ⟨cell, _, code, readBefore, readAfter⟩ :=
    ports (importedConstraintsMemoryPorts[k]'hk) (Array.getElem_mem hk)
  rw [shape] at code
  have bounded := indirect_bounded code
  have same := indirect_cell code
  subst same
  exact ⟨bounded, rv_ram_read readBefore, rv_ram_read readAfter⟩

theorem row_address_codes {p : Nat} (w : Nat → ZMod p) (k : Nat) (hk : k < 19) :
    ∃ bound, ((⟨.bigint, w⟩ : Delegation.Row p).memorySteps.map fun edge => edge.1.address)[k]'bound =
      (importedConstraintsMemoryPorts[k]'hk).address.code w := by
  have length : ((⟨.bigint, w⟩ : Delegation.Row p).memorySteps.map fun edge => edge.1.address).length = 19 := by
    simp only [Delegation.Row.memorySteps, Delegation.Row.ports, List.length_map, Array.length_toList]
    rfl
  refine ⟨by omega, ?_⟩
  simp only [Delegation.Row.memorySteps, Delegation.Row.ports, List.getElem_map, Array.getElem_toList, readToken]
  rfl

/-- The delegate link of one bigint row: from the call's pre-state `start`, the spec's bigint call
    (`RV.Delegation.effect .bigint`) has an effect, and applying it gives the call's post-state `finish` up to the
    spec's PC advance. -/
theorem rv_bigint_call {data : Delegation.MemoryData babyBearModulus} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.SeedProofs.SeedInputs data cells)
    (table : data.setup.bigint = setupTable) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {w : Nat → ZMod babyBearModulus} (member : (⟨.bigint, w⟩ : Delegation.Row babyBearModulus) ∈ data.rows)
    {events : List MemoryAccess} {start finish : RV.State} (history : RVHistory cells events start finish)
    (permutation : events.Perm ((Delegation.Row.mk .bigint w).memorySteps.map transferEvent)) :
    ∃ s', (RV.Delegation.effect .bigint (start.getReg 10) (start.getReg 11) (start.getReg 12)
        start.delegationRAM).bind start.applyEffect = some s' ∧ RV.Same s' (finish.setPC (start.pc + 4)) := by
  have hp : 2 * timestampBase + 4 < babyBearModulus := by norm_num [timestampBase, babyBearModulus]
  have ports : ∀ port ∈ importedConstraintsMemoryPorts, ∃ cell ∈ cells,
      cell.addressCode = port.address.code w ∧ cell.readRV start = some (memoryWord (port.readCode w)) ∧
      cell.readRV finish = some (memoryWord (port.writeCode w)) :=
    rv_row_atomic_observations hp accepted inputs member history permutation aligned
  have holds := accepted.constraints _ member
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints data.setup.bigint) at holds
  rw [table] at holds
  have core := Verification.holds_of_sublist holds
    (List.sublist_append_left (importedConstraints setupTable) importedConstraintsTimestampLookups)
  obtain ⟨_, _, _, shapes⟩ := port_shapes
  obtain ⟨readonly0, readonly9, readonlyBlock⟩ := readonly_ports w
  obtain ⟨value0, value9, value18, written18⟩ := port_values w
  -- registers
  obtain ⟨x10Start, x10Finish⟩ := register_value (index := 10) 0 (by decide) rfl ports
  obtain ⟨x11Start, x11Finish⟩ := register_value (index := 11) 9 (by decide) rfl ports
  obtain ⟨x12Start, x12Finish⟩ := register_value (index := 12) 18 (by decide) rfl ports
  have x10Same : finish.getReg 10 = start.getReg 10 :=
    x10Finish.trans ((congrArg memoryWord readonly0).trans x10Start.symm)
  have x11Same : finish.getReg 11 = start.getReg 11 :=
    x11Finish.trans ((congrArg memoryWord readonly9).trans x11Start.symm)
  have x10Value : start.getReg 10 = (⟨(w 3).val, (w 4).val⟩ : Word).toBitVec := x10Start.trans value0
  have x11Value : start.getReg 11 = (⟨(w 37).val, (w 38).val⟩ : Word).toBitVec := x11Start.trans value9
  have x12Value : start.getReg 12 = (⟨(w 55).val, (w 56).val⟩ : Word).toBitVec := x12Start.trans value18
  have x12Written : finish.getReg 12 = (⟨(w 57).val, (w 58).val⟩ : Word).toBitVec := x12Finish.trans written18
  -- canonical pointers
  have leftBounded : (⟨(w 3).val, (w 4).val⟩ : Word).Bounded := by
    have bound := (ram_value 1 (by decide) (shapes 0).1 ports).1
    have first : (importedConstraintsIndirectPorts[0]'(by decide)) =
        ⟨10, 0, #v[3, 4], 0, none, 0, #v[5, 6], some #v[7, 8]⟩ := rfl
    simp only [Fin.val_zero, first, Verification.IndirectPort.rawAddress, Option.elim, mul_zero, add_zero,
      Nat.cast_zero] at bound
    exact bound
  have rightBounded : (⟨(w 37).val, (w 38).val⟩ : Word).Bounded := by
    have bound := (ram_value 10 (by decide) (shapes 0).2 ports).1
    have first : (importedConstraintsIndirectPorts[8]'(by decide)) =
        ⟨11, 0, #v[37, 38], 0, none, 0, #v[39, 40], none⟩ := rfl
    simp only [Fin.val_zero, first, Verification.IndirectPort.rawAddress, Option.elim, mul_zero,
      add_zero, Nat.cast_zero] at bound
    exact bound
  have addresses := Addresses.Proofs.soundness (p := babyBearModulus) (by norm_num [babyBearModulus]) (by decide)
    ⟨⟨(w 3).val, (w 4).val⟩, ⟨(w 37).val, (w 38).val⟩⟩ (importedConstraintsIndirectPorts.map fun port => port.address w) w
    ⟨⟨leftBounded, rightBounded⟩, core, rfl, rfl, rfl⟩
  obtain ⟨leftAligned, rightAligned, blocks⟩ := addresses
  have left (i : Fin 8) : (importedConstraintsIndirectPorts[i.val]'(by omega)).address w =
      (⟨(w 3).val, (w 4).val⟩ : Word).toBitVec + BitVec.ofNat 32 (4 * i.val) := by
    have entry := congrArg (fun v : Vector (BitVec 32) 16 => v[i.val]'(by omega)) blocks
    simp only [Vector.getElem_map] at entry
    rw [entry, expected_left]
  have right (i : Fin 8) : (importedConstraintsIndirectPorts[8 + i.val]'(by omega)).address w =
      (⟨(w 37).val, (w 38).val⟩ : Word).toBitVec + BitVec.ofNat 32 (4 * i.val) := by
    have entry := congrArg (fun v : Vector (BitVec 32) 16 => v[8 + i.val]'(by omega)) blocks
    simp only [Vector.getElem_map] at entry
    rw [entry, expected_right]
  have x10Nat : (⟨(w 3).val, (w 4).val⟩ : Word).toBitVec.toNat = (w 3).val + 65536 * (w 4).val :=
    Word.toBitVec_toNat leftBounded
  have x11Nat : (⟨(w 37).val, (w 38).val⟩ : Word).toBitVec.toNat = (w 37).val + 65536 * (w 38).val :=
    Word.toBitVec_toNat rightBounded
  generalize (⟨(w 3).val, (w 4).val⟩ : Word).toBitVec = x10 at x10Value left x10Nat
  generalize (⟨(w 37).val, (w 38).val⟩ : Word).toBitVec = x11 at x11Value right x11Nat
  generalize x12Def : (⟨(w 55).val, (w 56).val⟩ : Word).toBitVec = x12 at x12Value
  change (w 3).val % 32 = 0 at leftAligned
  change (w 37).val % 32 = 0 at rightAligned
  have x10Mod : x10.toNat % 32 = 0 := by omega
  have x11Mod : x11.toNat % 32 = 0 := by omega
  have x10Fits : x10.toNat + 4 * 8 ≤ 2 ^ 32 := by have := x10.isLt; omega
  have x11Fits : x11.toNat + 32 ≤ RV.RAM_END := by have := x11.isLt; simp only [RV.RAM_END]; omega
  -- distinct pointers: the first words of the two blocks are different native addresses of one row
  have distinct : x10 ≠ x11 := by
    intro same
    have codes := seed_row_addresses_distinct hp accepted inputs member
    obtain ⟨cell1, _, code1, _⟩ := ports _ (Array.getElem_mem (by decide) : importedConstraintsMemoryPorts[1] ∈ _)
    obtain ⟨cell10, _, code10, _⟩ := ports _ (Array.getElem_mem (by decide) : importedConstraintsMemoryPorts[10] ∈ _)
    have code1' : cell1.addressCode = (MemoryAddress.indirect (importedConstraintsIndirectPorts[0]'(by decide))).code w :=
      code1
    have code10' : cell10.addressCode =
        (MemoryAddress.indirect (importedConstraintsIndirectPorts[8]'(by decide))).code w := code10
    have equal : cell1 = cell10 := by
      rw [indirect_cell code1', indirect_cell code10']
      exact congrArg Cell.ram ((left 0).trans ((congrArg (· + BitVec.ofNat 32 (4 * 0)) same).trans (right 0).symm))
    obtain ⟨b1, at1⟩ := row_address_codes w 1 (by decide)
    obtain ⟨b10, at10⟩ := row_address_codes w 10 (by decide)
    have index := (List.Nodup.getElem_inj_iff codes).mp
      (at1.trans (code1.symm.trans ((congrArg Cell.addressCode equal).trans (code10.trans at10.symm))))
    omega
  -- the control word and the operation
  have small := (mask_columns core).2
  have x12Low : x12.toNat % 65536 = (w 55).val := by
    rw [← x12Def]
    simp only [Word.toBitVec, Word.value, limbBase, BitVec.toNat_ofNat]
    omega
  obtain ⟨guard, r, f, operation, resultValue, flag57, flag58⟩ := row_operation core x12Low
  -- the operand words
  have ranges := source_ranges (by decide) core
  have operandWords (i : Fin 8) :
      (RV.readWords start.mem x10 8)[i].toNat =
          (limbs w Variables.leftLimbs)[2 * i.val] + 65536 * (limbs w Variables.leftLimbs)[2 * i.val + 1] ∧
      (RV.readWords start.mem x11 8)[i].toNat =
          (limbs w Variables.rightLimbs)[2 * i.val] + 65536 * (limbs w Variables.rightLimbs)[2 * i.val + 1] := by
    have roles := Native.Proofs.native_word_roles w i
    have lo := ranges ⟨2 * i.val, by omega⟩
    have hi := ranges ⟨2 * i.val + 1, by omega⟩
    have leftWord : RV.read start.mem (x10 + BitVec.ofNat 32 (4 * i.val)) 4 =
        (⟨(limbs w Variables.leftLimbs)[2 * i.val], (limbs w Variables.leftLimbs)[2 * i.val + 1]⟩ : Word).toBitVec := by
      have read := (ram_value (1 + i.val) (by omega) (shapes i).1 ports).2.1
      rw [left i] at read
      exact read.trans (congrArg Word.toBitVec roles.1)
    have rightWord : RV.read start.mem (x11 + BitVec.ofNat 32 (4 * i.val)) 4 =
        (⟨(limbs w Variables.rightLimbs)[2 * i.val], (limbs w Variables.rightLimbs)[2 * i.val + 1]⟩ : Word).toBitVec := by
      have read := (ram_value (10 + i.val) (by omega) (shapes i).2 ports).2.1
      rw [right i] at read
      exact read.trans (congrArg Word.toBitVec roles.2.2)
    simp only [RV.readWords, Vector.getElem_ofFn, Fin.getElem_fin]
    constructor
    · rw [leftWord, Word.toBitVec_toNat ⟨by simpa [limbs, limbBase] using lo.1, by simpa [limbs, limbBase] using hi.1⟩]
      simp [Word.value, limbBase]
    · rw [rightWord, Word.toBitVec_toNat ⟨by simpa [limbs, limbBase] using lo.2, by simpa [limbs, limbBase] using hi.2⟩]
      simp [Word.value, limbBase]
  have leftValue := toU256_of_limbs _ _ (fun i => (operandWords i).1)
  have rightValue := toU256_of_limbs _ _ (fun i => (operandWords i).2)
  -- the spec's effect
  have effect : RV.Delegation.effect .bigint (start.getReg 10) (start.getReg 11) (start.getReg 12) start.mem =
      some { writes := RV.writesAt x10 (RV.Delegation.ofU256 r), reg := 12, val := if f then 1 else 0 } := by
    rw [x10Value, x11Value, x12Value]
    simp only [RV.Delegation.effect, RV.Delegation.bigint]
    simp only [x10Mod, x11Fits, x11Mod, ne_eq, distinct, not_false_eq_true, guard, and_self, ↓reduceIte]
    rw [leftValue, rightValue, operation]
    rfl
  have resultBound : ∀ i : Fin 16, (output w).result[i] < 65536 := by
    intro i; simpa [output, limbs, limbBase] using written_limb_bounds (by decide) core i
  obtain ⟨frameRegs, frameWords⟩ := rv_row_frame left right history permutation
    (fun port present => by obtain ⟨cell, _, code, _⟩ := ports port present; exact ⟨cell, code⟩) aligned
  have fields := rv_history_fields history
  obtain ⟨U, call, same⟩ := call_same (S := start) (T := finish) effect
    (by
      intro aw present
      obtain ⟨j, bound, address⟩ := RV.writesAt_addr x10 _ x10Fits aw present
      omega)
    fields.2.1 fields.2.2
    (by
      intro reg
      by_cases r12 : reg = 12
      · subst r12
        simp only [and_self, ne_eq, show (12 : BitVec 5) ≠ 0 by decide, not_false_eq_true, ↓reduceIte]
        rw [x12Written]
        cases f
        · simp only [Bool.false_eq_true, ↓reduceIte] at flag57 ⊢
          simp [Word.toBitVec, Word.value, flag57, flag58]
        · simp only [↓reduceIte] at flag57 ⊢
          simp [Word.toBitVec, Word.value, flag57, flag58]
      · have notTwelve : ¬(reg = 12 ∧ reg ≠ 0) := fun h => r12 h.1
        simp only [notTwelve, ↓reduceIte]
        by_cases r10 : reg = 10
        · subst r10
          exact x10Same
        by_cases r11 : reg = 11
        · subst r11
          exact x11Same
        exact frameRegs reg r10 r11 r12)
    (by
      intro a alignedA
      by_cases inLeft : ∃ j : Fin 8, a = x10 + BitVec.ofNat 32 (4 * j.val)
      · obtain ⟨j, rfl⟩ := inLeft
        have written := (ram_value (1 + j.val) (by omega) (shapes j).1 ports).2.2
        rw [left j] at written
        have stored := read_writesAt_at start [] [] x10 (RV.Delegation.ofU256 r) x10Fits (by simp) j
        simp only [List.nil_append, List.append_nil] at stored
        rw [stored, ofU256_of_limbs r _ resultBound resultValue j]
        refine written.trans ((congrArg Word.toBitVec (Native.Proofs.native_word_roles w j).2.1).trans ?_)
        simp [Word.toBitVec, Word.value, limbBase]
      · have outside : ∀ j : Fin 8, a ≠ x10 + BitVec.ofNat 32 (4 * j.val) := fun j h => inLeft ⟨j, h⟩
        rw [RV.read_storeAll_other start _ a (by have := a.isLt; omega)
          (writesAt_disjoint x10 a _ (by omega) x10Fits alignedA outside)]
        by_cases inRight : ∃ j : Fin 8, a = x11 + BitVec.ofNat 32 (4 * j.val)
        · obtain ⟨j, rfl⟩ := inRight
          have observed := ram_value (10 + j.val) (by omega) (shapes j).2 ports
          rw [right j] at observed
          exact observed.2.2.trans ((congrArg memoryWord (readonlyBlock j)).trans observed.2.1.symm)
        · exact frameWords a alignedA outside (fun j h => inRight ⟨j, h⟩))
  have bindSome : ∀ o : Option RV.State, (o.bind fun x => some x) = o := fun o => by cases o <;> rfl
  simp only [RV.calls, RV.State.delegationRAM, bindSome] at call
  exact ⟨U, call, same⟩

end Airbender.Bigint.Proofs
