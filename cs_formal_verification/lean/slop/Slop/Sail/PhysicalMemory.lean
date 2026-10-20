import Slop.Sail.WordMemoryState
import Slop.Sail.MMIO

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

private theorem projected_byte {size : Nat} (value : BitVec (8 * size)) (i : Int) (bound : i.toNat < size) :
    (_root_.Sail.bitvec_to_vecbytes (n := size) value)[i]'bound =
      value.extractLsb' (8 * i.toNat) 8 := by
  change (_root_.Sail.bitvec_to_vecbytes (n := size) value)[i.toNat] = _
  simp [_root_.Sail.bitvec_to_vecbytes, _root_.Sail.BitVec.slice]

set_option backward.isDefEq.respectTransparency false in
/-- The generated Sail little-endian decoder inverts the pinned runtime's
    byte projection. Both functions here are upstream definitions. -/
theorem decode_memory_bytes {size : Nat} (width : size = 1 ∨ size = 2 ∨ size = 4)
    (value : BitVec (8 * size)) :
    SailRV32.Functions.from_bytes_le (_root_.Sail.bitvec_to_vecbytes (n := size) value) = value := by
  rcases width with rfl | rfl | rfl
  all_goals
    simp [SailRV32.Functions.from_bytes_le, forIn_eq_forIn', ForIn'.forIn',
      IntRange.forIn', IntRange.forIn'.loop, Membership.mem, projected_byte,
      _root_.Sail.BitVec.updateSubrange, _root_.Sail.BitVec.updateSubrange']
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro i bound
    interval_cases i <;> simp only [BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_extractLsb'] <;> simp

theorem decode_word_bytes (value : BitVec 32) :
    SailRV32.Functions.from_bytes_le (_root_.Sail.bitvec_to_vecbytes (n := 4) value) = value :=
  decode_memory_bytes (Or.inr (Or.inr rfl)) value

set_option backward.isDefEq.respectTransparency false in
/-- The generated encoder and native write interpreter use the same byte order. -/
theorem encode_memory_bytes {size : Nat} (width : size = 1 ∨ size = 2 ∨ size = 4)
    (value : BitVec (8 * size)) :
    _root_.Sail.vecbytes_to_bitvec (SailRV32.Functions.to_bytes_le (n := size) value) = value := by
  have bytes : SailRV32.Functions.to_bytes_le (n := size) value =
      Vector.ofFn (fun i : Fin size => value.extractLsb' (8 * i.val) 8) := by
    rcases width with rfl | rfl | rfl
    all_goals
      simp [SailRV32.Functions.to_bytes_le, forIn_eq_forIn', ForIn'.forIn',
        IntRange.forIn', IntRange.forIn'.loop, Membership.mem,
        _root_.Sail.vectorInit, _root_.Sail.vectorUpdate, _root_.Sail.BitVec.extractLsb,
        BitVec.extractLsb, Vector.ofFn]
      rfl
  rw [bytes]
  rcases width with rfl | rfl | rfl
  all_goals
    unfold _root_.Sail.vecbytes_to_bitvec
    simp only [Vector.ofFn]
    rw [Vector.foldl_mk, ← Array.foldl_toList]
    simp only [Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero,
      List.foldl_cons, List.foldl_nil, BitVec.zero]
    apply BitVec.eq_of_getLsbD_eq
    intro i bound
    interval_cases i <;> simp [BitVec.zeroExtend]

theorem encode_word_bytes (value : BitVec 32) :
    _root_.Sail.vecbytes_to_bitvec (SailRV32.Functions.to_bytes_le (n := 4) value) = value :=
  encode_memory_bytes (Or.inr (Or.inr rfl)) value

set_option backward.isDefEq.respectTransparency false in
theorem read_ram_sized {size : Nat} {before : State} {address : BitVec 32} {value : BitVec (8 * size)}
    (width : size = 1 ∨ size = 2 ∨ size = 4)
    (read : (readBytes (ue := SailRV32.exception) size address.toNat).run before =
      .ok value before) :
    run (SailRV32.Functions.read_ram .Read_plain (.Load .Data)
      (.Physaddr (address.setWidth 34)) size false) before = .ok (value, ()) before := by
  let request : Mem_request size 0 SailRV32.physaddrbits_len.toNat Unit SailRV32.access_kind := {
    access_kind := .AK_Read (.Read_plain, .Load .Data)
    address := address.setWidth 34
    address_space := ()
    size := size
    num_tag := 0 }
  have native : run (PreSail.sail_mem_read request : SailRV32.SailM _) before =
      .ok (.Ok (_root_.Sail.bitvec_to_vecbytes (n := size) value, #v[])) before := by
    change readBytes (ue := SailRV32.exception) size address.toNat before = _ at read
    simp [PreSail.sail_mem_read, run, interpretSailEffects, FreeM.liftM,
      Mem_request.toArchSem, request, interpretInstructionEffect, EStateM.run,
      bind, EStateM.bind,
      _root_.Sail.bitvec_to_vecbool, Function.comp_def]
    rw [physical_address_value]
    simp [pure, EStateM.pure, read]
    rfl
  simp only [SailRV32.Functions.read_ram, SailRV32.ArchSem.sail_mem_read, freeM_pure_bind]
  rw [run_bind_of_ok _ _ _ _ _ native]
  simp only [decode_memory_bytes width]
  rfl

theorem read_ram_word {before : State} {address : BitVec 32} {value : BitVec 32}
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .ok value before) :
    run (SailRV32.Functions.read_ram .Read_plain (.Load .Data)
      (.Physaddr (address.setWidth 34)) 4 false) before = .ok (value, ()) before :=
  read_ram_sized (Or.inr (Or.inr rfl)) read

set_option backward.isDefEq.respectTransparency false in
theorem read_ram_sized_error {size : Nat} {before after : State} {address : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (read : (readBytes (ue := SailRV32.exception) size address.toNat).run before =
      .error error after) :
    run (SailRV32.Functions.read_ram .Read_plain (.Load .Data)
      (.Physaddr (address.setWidth 34)) size false) before = .error error after := by
  let request : Mem_request size 0 SailRV32.physaddrbits_len.toNat Unit SailRV32.access_kind := {
    access_kind := .AK_Read (.Read_plain, .Load .Data)
    address := address.setWidth 34
    address_space := ()
    size := size
    num_tag := 0 }
  have native : run (PreSail.sail_mem_read request : SailRV32.SailM _) before =
      .error error after := by
    change readBytes (ue := SailRV32.exception) size address.toNat before = _ at read
    simp [PreSail.sail_mem_read, run, interpretSailEffects, FreeM.liftM,
      Mem_request.toArchSem, request, interpretInstructionEffect, EStateM.run,
      bind, EStateM.bind, Function.comp_def]
    rw [physical_address_value]
    simp [pure, EStateM.pure, read]
  simp only [SailRV32.Functions.read_ram, SailRV32.ArchSem.sail_mem_read, freeM_pure_bind]
  exact run_bind_of_error _ _ _ _ _ native

theorem read_ram_word_error {before after : State} {address : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .error error after) :
    run (SailRV32.Functions.read_ram .Read_plain (.Load .Data)
      (.Physaddr (address.setWidth 34)) 4 false) before = .error error after :=
  read_ram_sized_error read

set_option backward.isDefEq.respectTransparency false in
theorem write_ram_sized {size : Nat} {before after : State} (address : BitVec 32)
    (width : size = 1 ∨ size = 2 ∨ size = 4) (value : BitVec (8 * size))
    (write : run (writeMemory (size := size) address value) before = .ok () after) :
    run (SailRV32.Functions.write_ram .Write_plain (.Store .Data)
      (.Physaddr (address.setWidth 34)) size value ()) before = .ok true after := by
  let request : Mem_request size 0 SailRV32.physaddrbits_len.toNat Unit SailRV32.access_kind := {
    access_kind := .AK_Write (.Write_plain, .Store .Data)
    address := address.setWidth 34
    address_space := ()
    size := size
    num_tag := 0 }
  have native : run (PreSail.sail_mem_write request
      (SailRV32.Functions.to_bytes_le (n := size) value) #v[] : SailRV32.SailM _) before =
      run (do writeMemory (size := size) address value; pure (.Ok none)) before := by
    simp [PreSail.sail_mem_write, encode_memory_bytes width, run, interpretSailEffects,
      FreeM.liftM, FreeM.bind, Mem_request.toArchSem, request, interpretInstructionEffect, writeMemory,
      EStateM.run, EStateM.bind, EStateM.pure, bind, pure]
    rw [physical_address_value]
    cases outcome : writeBytes (ue := SailRV32.exception) (n := size) address.toNat value before with
    | ok result state => cases result; rfl
    | error error state => rfl
  rw [run_bind_of_ok _ _ _ _ _ write] at native
  change run (PreSail.sail_mem_write request
    (SailRV32.Functions.to_bytes_le (n := size) value) #v[] >>= fun result =>
    match result with
    | .Ok _ => pure true
    | .Err () => pure false) before = _
  rw [run_bind_of_ok _ _ _ _ _ native]
  rfl

theorem write_ram_word (before : State) (address value : BitVec 32) :
    run (SailRV32.Functions.write_ram .Write_plain (.Store .Data)
      (.Physaddr (address.setWidth 34)) 4 value ()) before =
        .ok true (wordWriteState before address.toNat value) :=
  write_ram_sized address (Or.inr (Or.inr rfl)) value (write_word_state before address value)

end Airbender.Reference.RiscV.Sail
