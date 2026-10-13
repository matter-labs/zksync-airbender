import Slop.Equiv.Bytes

/-! `mem_read` on Airbender: an aligned load of 1, 2 or 4 bytes from ROM or RAM returns the bytes in Sail's memory
(`readBytes`), state unchanged. One lemma per (region, width). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem phys_addr_toNat (a : BitVec 32) :
    (BitVec.addInt (bits_of_physaddr (physaddr.Physaddr (zero_extend a))) 0).toNat = a.toNat := by
  simp only [BitVec.addInt, bits_of_physaddr]
  rw [show (BitVec.ofInt _ 0) = 0#_ from by simp, BitVec.add_zero]
  exact zero_extend_toNat a (by decide)

theorem update_full8 (y : BitVec 8) : BitVec.updateSubrange (zeros : BitVec 8) 7 0 y = y := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', zeros]
  interval_cases j <;> simp

theorem update_full16 (y : BitVec 16) : BitVec.updateSubrange (zeros : BitVec 16) 15 0 y = y := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', zeros]
  interval_cases j <;> simp

theorem update_full32 (y : BitVec 32) : BitVec.updateSubrange (zeros : BitVec 32) 31 0 y = y := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', zeros]
  interval_cases j <;> simp

theorem mem_read_ram1 (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (ha : a.toNat % 1 = 0)
    (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 1 ≤ Airbender.RAM_END) :
    runF (mem_read (.Load .Data) .PBMT_PMA .Machine (.Physaddr (zero_extend a)) 1 false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 1)) σ := by
  have hw : (1 = 1 ∨ 1 = 2 ∨ 1 = 4) := by decide
  sail_run hs using mem_side with [pma_ram_load]
  dsimp only [MemoryOpResult_drop_meta]
  simp only [EStateM.Result.ok.injEq, and_true, Result.Ok.injEq]
  simp
  show BitVec.updateSubrange (zeros : BitVec 8) 7 0 (from_bytes_le (n := 1) (bitvec_to_vecbytes (n := 1)
    (readBytes σ.mem (BitVec.addInt (bits_of_physaddr (physaddr.Physaddr (zero_extend a))) 0).toNat 1))) =
    readBytes σ.mem a.toNat 1
  rw [roundtrip1, update_full8, phys_addr_toNat]

theorem mem_read_ram2 (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (ha : a.toNat % 2 = 0)
    (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 2 ≤ Airbender.RAM_END) :
    runF (mem_read (.Load .Data) .PBMT_PMA .Machine (.Physaddr (zero_extend a)) 2 false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 2)) σ := by
  have hw : (2 = 1 ∨ 2 = 2 ∨ 2 = 4) := by decide
  sail_run hs using mem_side with [pma_ram_load]
  dsimp only [MemoryOpResult_drop_meta]
  simp only [EStateM.Result.ok.injEq, and_true, Result.Ok.injEq]
  simp
  show BitVec.updateSubrange (zeros : BitVec 16) 15 0 (from_bytes_le (n := 2) (bitvec_to_vecbytes (n := 2)
    (readBytes σ.mem (BitVec.addInt (bits_of_physaddr (physaddr.Physaddr (zero_extend a))) 0).toNat 2))) =
    readBytes σ.mem a.toNat 2
  rw [roundtrip2, update_full16, phys_addr_toNat]

theorem mem_read_ram4 (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (ha : a.toNat % 4 = 0)
    (h1 : Airbender.RAM_START ≤ a.toNat) (h2 : a.toNat + 4 ≤ Airbender.RAM_END) :
    runF (mem_read (.Load .Data) .PBMT_PMA .Machine (.Physaddr (zero_extend a)) 4 false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 4)) σ := by
  have hw : (4 = 1 ∨ 4 = 2 ∨ 4 = 4) := by decide
  sail_run hs using mem_side with [pma_ram_load]
  dsimp only [MemoryOpResult_drop_meta]
  simp only [EStateM.Result.ok.injEq, and_true, Result.Ok.injEq]
  simp
  show BitVec.updateSubrange (zeros : BitVec 32) 31 0 (from_bytes_le (n := 4) (bitvec_to_vecbytes (n := 4)
    (readBytes σ.mem (BitVec.addInt (bits_of_physaddr (physaddr.Physaddr (zero_extend a))) 0).toNat 4))) =
    readBytes σ.mem a.toNat 4
  rw [roundtrip4, update_full32, phys_addr_toNat]

theorem mem_read_rom1 (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (ha : a.toNat % 1 = 0)
    (h2 : a.toNat + 1 ≤ Airbender.RAM_START) :
    runF (mem_read (.Load .Data) .PBMT_PMA .Machine (.Physaddr (zero_extend a)) 1 false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 1)) σ := by
  have hw : (1 = 1 ∨ 1 = 2 ∨ 1 = 4) := by decide
  sail_run hs using mem_side with [pma_rom_load]
  dsimp only [MemoryOpResult_drop_meta]
  simp only [EStateM.Result.ok.injEq, and_true, Result.Ok.injEq]
  simp
  show BitVec.updateSubrange (zeros : BitVec 8) 7 0 (from_bytes_le (n := 1) (bitvec_to_vecbytes (n := 1)
    (readBytes σ.mem (BitVec.addInt (bits_of_physaddr (physaddr.Physaddr (zero_extend a))) 0).toNat 1))) =
    readBytes σ.mem a.toNat 1
  rw [roundtrip1, update_full8, phys_addr_toNat]

theorem mem_read_rom2 (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (ha : a.toNat % 2 = 0)
    (h2 : a.toNat + 2 ≤ Airbender.RAM_START) :
    runF (mem_read (.Load .Data) .PBMT_PMA .Machine (.Physaddr (zero_extend a)) 2 false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 2)) σ := by
  have hw : (2 = 1 ∨ 2 = 2 ∨ 2 = 4) := by decide
  sail_run hs using mem_side with [pma_rom_load]
  dsimp only [MemoryOpResult_drop_meta]
  simp only [EStateM.Result.ok.injEq, and_true, Result.Ok.injEq]
  simp
  show BitVec.updateSubrange (zeros : BitVec 16) 15 0 (from_bytes_le (n := 2) (bitvec_to_vecbytes (n := 2)
    (readBytes σ.mem (BitVec.addInt (bits_of_physaddr (physaddr.Physaddr (zero_extend a))) 0).toNat 2))) =
    readBytes σ.mem a.toNat 2
  rw [roundtrip2, update_full16, phys_addr_toNat]

theorem mem_read_rom4 (σ : FState) (hs : Airbender.Sys σ) (a : BitVec 32) (ha : a.toNat % 4 = 0)
    (h2 : a.toNat + 4 ≤ Airbender.RAM_START) :
    runF (mem_read (.Load .Data) .PBMT_PMA .Machine (.Physaddr (zero_extend a)) 4 false false false) σ =
      .ok (.Ok (readBytes σ.mem a.toNat 4)) σ := by
  have hw : (4 = 1 ∨ 4 = 2 ∨ 4 = 4) := by decide
  sail_run hs using mem_side with [pma_rom_load]
  dsimp only [MemoryOpResult_drop_meta]
  simp only [EStateM.Result.ok.injEq, and_true, Result.Ok.injEq]
  simp
  show BitVec.updateSubrange (zeros : BitVec 32) 31 0 (from_bytes_le (n := 4) (bitvec_to_vecbytes (n := 4)
    (readBytes σ.mem (BitVec.addInt (bits_of_physaddr (physaddr.Physaddr (zero_extend a))) 0).toNat 4))) =
    readBytes σ.mem a.toNat 4
  rw [roundtrip4, update_full32, phys_addr_toNat]

end Slop.Equiv
