import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.SubwordMemory.PortReads
import Airbender.Proofs.Trace.Addresses
import Airbender.Proofs.SubwordMemory.MemoryAccess

namespace Airbender.SubwordMemory.Proofs
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
open Arithmetic Trace Reference.RiscV.Sail

omit [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] in
/-- A native aligned cell and its offset recover Sail's containing word. -/
theorem aligned_cell_index {cell : Word} (bound : cell.Bounded)
    (aligned : cell.value % 4 = 0) {offset : Nat} (small : offset < 4) :
    (cell.toBitVec + BitVec.ofNat 32 offset).toNat / 4 * 4 = cell.toBitVec.toNat := by
  have wordBound := Word.value_lt bound
  have noWrap : cell.value + offset < 4294967296 := by
    dsimp [wordModulus] at wordBound
    omega
  rw [BitVec.toNat_add, Word.toBitVec_toNat bound, BitVec.toNat_ofNat]
  norm_num only [Nat.reducePow]
  have offsetBound : offset < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt offsetBound, Nat.mod_eq_of_lt noWrap]
  omega

/-- The public ordinary-cell domain also covers its byte/halfword offsets. -/
theorem ordinary_cell_offset {address : BitVec 32} (aligned : address.toNat % 4 = 0)
    (ordinary : PlatformWordAddress address) {offset : Nat} (small : offset < 4) :
    PlatformWordAddress (address + BitVec.ofNat 32 offset) := by
  have wordBound := address.isLt
  norm_num only [Nat.reducePow] at wordBound
  have noWrap : address.toNat + offset < 4294967296 := by omega
  change ((_root_.Sail.ArchSem.MemoryPlatform.devices (ue := SailRV32.exception)).haveClint = false ∨ address.toNat < 33554432 ∨ 33603584 ≤ address.toNat) ∧
    ((_root_.Sail.ArchSem.MemoryPlatform.devices (ue := SailRV32.exception)).haveSig = false ∨ address.toNat < 201326592 ∨ 201326624 ≤ address.toNat) at ordinary
  change ((_root_.Sail.ArchSem.MemoryPlatform.devices (ue := SailRV32.exception)).haveClint = false ∨ (address + BitVec.ofNat 32 offset).toNat < 33554432 ∨
      33603584 ≤ (address + BitVec.ofNat 32 offset).toNat) ∧
    ((_root_.Sail.ArchSem.MemoryPlatform.devices (ue := SailRV32.exception)).haveSig = false ∨ (address + BitVec.ofNat 32 offset).toNat < 201326592 ∨
      201326624 ≤ (address + BitVec.ofNat 32 offset).toNat)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  norm_num only [Nat.reducePow]
  have offsetBound : offset < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt offsetBound, Nat.mod_eq_of_lt noWrap]
  constructor
  · rcases ordinary.1 with disabled | outside
    · exact Or.inl disabled
    · exact Or.inr (by omega)
  · rcases ordinary.2 with disabled | outside
    · exact Or.inl disabled
    · exact Or.inr (by omega)

omit [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] in
/-- Registry-independent address equations. Initialized history supplies the
    three canonical words and cell membership; this lemma supplies alignment. -/
theorem local_address {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 33554432)
    (inverse : SerializedInverse.Clock p)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} {cells : List Cell}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (store : Bool) (selected : w 10 = if store then 1 else 0)
    (source : (Word.mk (w 19).val (w 20).val).Bounded)
    (immediate : (Word.mk (w 8).val (w 9).val).Bounded)
    (cellBound : (Word.mk (if store then w 27 else w 21).val (if store then w 28 else w 22).val).Bounded)
    (present : Cell.ram (Word.mk (if store then w 27 else w 21).val
      (if store then w 28 else w 22).val).toBitVec ∈ cells) :
    let cell : Word := ⟨(if store then w 27 else w 21).val, (if store then w 28 else w 22).val⟩
    let offset := (w 35).val + 2 * (w 36).val
    cell.Bounded ∧ cell.value % 4 = 0 ∧ offset < 4 ∧
      cell.toBitVec + BitVec.ofNat 32 offset =
        (Word.mk (w 19).val (w 20).val).toBitVec + (Word.mk (w 8).val (w 9).val).toBitVec ∧
      ((Word.mk (w 19).val (w 20).val).toBitVec +
        (Word.mk (w 8).val (w 9).val).toBitVec).toNat % 4 = offset ∧
      Cell.ram cell.toBitVec ∈ cells := by
  have addressInverse : SerializedInverse.Limb16 p := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  have effect := effective_address (by omega) addressInverse store h selected
    ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
      (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl,
      (ZMod.natCast_zmod_val _).symm⟩ source immediate cellBound.2
  refine ⟨effect.1, effect.2.1, effect.2.2.1, effect.2.2.2.1, effect.2.2.2.2, ?_⟩
  exact present

omit [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] in
/-- Public initialization and latest-write history supply operand/address bounds.
    Imported address equations then identify the aligned cell and byte offset. -/
theorem native_address {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 33554432)
    (inverse : SerializedInverse.Clock p) {trace : NativeTrace p}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {program : Nat → BitVec 32} (setup : trace.rom = Verification.subwordTable program)
    {w : Nat → ZMod p} (member : (⟨.subwordMemory, w⟩ : Row p TraceKind) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (store : Bool) (selected : w 10 = if store then 1 else 0) :
    let cell : Word := ⟨(if store then w 27 else w 21).val, (if store then w 28 else w 22).val⟩
    let offset := (w 35).val + 2 * (w 36).val
    cell.Bounded ∧ cell.value % 4 = 0 ∧ offset < 4 ∧
      cell.toBitVec + BitVec.ofNat 32 offset =
        (Word.mk (w 19).val (w 20).val).toBitVec + (Word.mk (w 8).val (w 9).val).toBitVec ∧
      ((Word.mk (w 19).val (w 20).val).toBitVec +
        (Word.mk (w 8).val (w 9).val).toBitVec).toNat % 4 = offset ∧
      Cell.ram cell.toBitVec ∈ cells := by
  have clockField : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  have h := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have bounds := (native_value_bounds hp inverse accepted clocks (Trace.Proofs.image_bounds image) setup).1 _ member
  have source := bounds importedConstraintsMemoryPorts[0]
    (by simp [Row.ports, importedConstraintsMemoryPorts])
  rw [Trace.Proofs.read_word] at source
  change (Word.mk (w 19).val (w 20).val).Bounded at source
  have immediate : (Word.mk (w 8).val (w 9).val).Bounded := by
    have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query
    have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query
    change w 8 = (entry.data.immediate.lo : ZMod p) at low
    change w 9 = (entry.data.immediate.hi : ZMod p) at high
    have bound := (decoder_field_bounds fields).1
    rw [Word.Bounded, low, high, ZMod.val_natCast_of_lt (lt_trans bound.1 limbField),
      ZMod.val_natCast_of_lt (lt_trans bound.2 limbField)]
    exact bound
  have address := Trace.Proofs.address_bounds clockField inverse accepted clocks image _ member
    (if store then importedConstraintsMemoryPorts[2] else importedConstraintsMemoryPorts[1])
    (by cases store <;> simp [Row.ports, importedConstraintsMemoryPorts])
  have cellBound : (Word.mk (if store then w 27 else w 21).val
      (if store then w 28 else w 22).val).Bounded := by
    cases store <;> simpa [importedConstraintsMemoryPorts, MemoryAddress.word] using address
  have present := (ram_cell clockField inverse accepted clocks image member store selected).1
  apply local_address hp inverse h store selected source immediate cellBound
  cases store <;> simpa [importedConstraintsMemoryPorts, MemoryAddress.word] using present

end Airbender.SubwordMemory.Proofs
