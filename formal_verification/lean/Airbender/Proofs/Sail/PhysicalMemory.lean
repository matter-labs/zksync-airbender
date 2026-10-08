import Airbender.Proofs.Sail.WordMemoryState
import Airbender.Proofs.Sail.MMIO

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

private theorem projected_byte (value : BitVec 32) (i : Int) (bound : i.toNat < 4) :
    (_root_.Sail.bitvec_to_vecbytes (n := 4) value)[i]'bound =
      value.extractLsb' (8 * i.toNat) 8 := by
  change (_root_.Sail.bitvec_to_vecbytes (n := 4) value)[i.toNat] = _
  simp [_root_.Sail.bitvec_to_vecbytes, _root_.Sail.BitVec.slice]

set_option backward.isDefEq.respectTransparency false in
/-- The generated Sail little-endian decoder inverts the pinned runtime's
    byte projection. Both functions here are upstream definitions. -/
theorem decode_word_bytes (value : BitVec 32) :
    SailRV32.Functions.from_bytes_le (_root_.Sail.bitvec_to_vecbytes (n := 4) value) = value := by
  simp [SailRV32.Functions.from_bytes_le, forIn_eq_forIn', ForIn'.forIn',
    IntRange.forIn', IntRange.forIn'.loop, Membership.mem,
    projected_byte,
    _root_.Sail.BitVec.updateSubrange, _root_.Sail.BitVec.updateSubrange']
  apply BitVec.eq_of_getLsbD_eq
  intro i bound
  interval_cases i <;> simp only [BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb'] <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- The generated encoder and native write interpreter use the same byte order. -/
theorem encode_word_bytes (value : BitVec 32) :
    _root_.Sail.vecbytes_to_bitvec (SailRV32.Functions.to_bytes_le (n := 4) value) = value := by
  have bytes : SailRV32.Functions.to_bytes_le (n := 4) value =
      ⟨#[value.extractLsb' 0 8, value.extractLsb' 8 8,
        value.extractLsb' 16 8, value.extractLsb' 24 8], rfl⟩ := by
    simp [SailRV32.Functions.to_bytes_le, forIn_eq_forIn', ForIn'.forIn',
      IntRange.forIn', IntRange.forIn'.loop, Membership.mem,
      _root_.Sail.vectorInit, _root_.Sail.vectorUpdate, _root_.Sail.BitVec.extractLsb,
      BitVec.extractLsb]
    rfl
  rw [bytes]
  unfold _root_.Sail.vecbytes_to_bitvec
  rw [Vector.foldl_mk, ← Array.foldl_toList]
  simp only [List.foldl_cons, List.foldl_nil, BitVec.zero]
  change (((((0 : BitVec 32) ||| ((value.extractLsb' 0 8).zeroExtend 32 <<< 0)) |||
    ((value.extractLsb' 8 8).zeroExtend 32 <<< 8)) |||
    ((value.extractLsb' 16 8).zeroExtend 32 <<< 16)) |||
    ((value.extractLsb' 24 8).zeroExtend 32 <<< 24)) = value
  apply BitVec.eq_of_getLsbD_eq
  intro i bound
  interval_cases i <;> simp only [BitVec.zeroExtend, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb'] <;> simp

set_option backward.isDefEq.respectTransparency false in
theorem read_ram_word {before : State} {address : BitVec 32} {value : BitVec 32}
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before =
      .ok value before) :
    run (SailRV32.Functions.read_ram .Read_plain (.Load .Data)
      (.Physaddr (address.setWidth 34)) 4 false) before = .ok (value, ()) before := by
  let request : Mem_request 4 0 SailRV32.physaddrbits_len.toNat Unit SailRV32.access_kind := {
    access_kind := .AK_Read (.Read_plain, .Load .Data)
    address := address.setWidth 34
    address_space := ()
    size := 4
    num_tag := 0 }
  have native : run (PreSail.sail_mem_read request : SailRV32.SailM _) before =
      .ok (.Ok (_root_.Sail.bitvec_to_vecbytes (n := 4) value, #v[])) before := by
    change readBytes (ue := SailRV32.exception) 4 address.toNat before = _ at read
    simp [PreSail.sail_mem_read, run, interpretSailEffects, FreeM.liftM,
      Mem_request.toArchSem, request, interpretInstructionEffect, EStateM.run,
      bind, EStateM.bind,
      _root_.Sail.bitvec_to_vecbool, Function.comp_def]
    rw [physical_address_value]
    simp [pure, EStateM.pure, read]
    rfl
  simp only [SailRV32.Functions.read_ram, SailRV32.ArchSem.sail_mem_read, freeM_pure_bind]
  rw [run_bind_of_ok _ _ _ _ _ native]
  simp only [decode_word_bytes]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem read_ram_word_error {before after : State} {address : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before =
      .error error after) :
    run (SailRV32.Functions.read_ram .Read_plain (.Load .Data)
      (.Physaddr (address.setWidth 34)) 4 false) before = .error error after := by
  let request : Mem_request 4 0 SailRV32.physaddrbits_len.toNat Unit SailRV32.access_kind := {
    access_kind := .AK_Read (.Read_plain, .Load .Data)
    address := address.setWidth 34
    address_space := ()
    size := 4
    num_tag := 0 }
  have native : run (PreSail.sail_mem_read request : SailRV32.SailM _) before =
      .error error after := by
    change readBytes (ue := SailRV32.exception) 4 address.toNat before = _ at read
    simp [PreSail.sail_mem_read, run, interpretSailEffects, FreeM.liftM,
      Mem_request.toArchSem, request, interpretInstructionEffect, EStateM.run,
      bind, EStateM.bind, Function.comp_def]
    rw [physical_address_value]
    simp [pure, EStateM.pure, read]
  simp only [SailRV32.Functions.read_ram, SailRV32.ArchSem.sail_mem_read, freeM_pure_bind]
  exact run_bind_of_error _ _ _ _ _ native

set_option backward.isDefEq.respectTransparency false in
theorem write_ram_word (before : State) (address value : BitVec 32) :
    run (SailRV32.Functions.write_ram .Write_plain (.Store .Data)
      (.Physaddr (address.setWidth 34)) 4 value ()) before =
        .ok true (wordWriteState before address.toNat value) := by
  let request : Mem_request 4 0 SailRV32.physaddrbits_len.toNat Unit SailRV32.access_kind := {
    access_kind := .AK_Write (.Write_plain, .Store .Data)
    address := address.setWidth 34
    address_space := ()
    size := 4
    num_tag := 0 }
  have native : run (PreSail.sail_mem_write request
      (SailRV32.Functions.to_bytes_le (n := 4) value) #v[] : SailRV32.SailM _) before =
        .ok (.Ok none) (wordWriteState before address.toNat value) := by
    simp [PreSail.sail_mem_write, encode_word_bytes, run, interpretSailEffects,
      FreeM.liftM, Mem_request.toArchSem, request, interpretInstructionEffect,
      wordWriteState, writeBytes, List.ofFn_succ,
      List.forM_cons, writeByte, modify, modifyGet, MonadStateOf.modifyGet,
      EStateM.run, EStateM.bind, EStateM.modifyGet, EStateM.pure, bind, pure]
    rw [physical_address_value]
  change run (PreSail.sail_mem_write request
    (SailRV32.Functions.to_bytes_le (n := 4) value) #v[] >>= fun result =>
    match result with
    | .Ok _ => pure true
    | .Err () => pure false) before = _
  rw [run_bind_of_ok _ _ _ _ _ native]
  rfl

end Airbender.Reference.RiscV.Sail
