import Slop.Sail.PMA

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

private theorem clint_base : SailRV32.Functions.plat_clint_base = (33554432 : BitVec 34) := rfl
private theorem clint_size : SailRV32.Functions.plat_clint_size = (49152 : BitVec 34) := rfl
private theorem signature_base : SailRV32.Functions.plat_sig_base = (201326592 : BitVec 34) := rfl
private theorem signature_size : SailRV32.Functions.plat_sig_size = (32 : BitVec 34) := rfl

-- The Airbender configuration has no CLINT (`plat_have_clint = false`): `within_clint` is
-- `pure false` without reading any register, so the exclusion holds for every address.
theorem clint_excluded_sized {size : Nat} {before : State} {hart : BitVec 32} {address : BitVec 32}
    (positive : 0 < size)
    (initialized : before.regs.get? .mhartid = some hart)
    (outside : address.toNat < 33554432 ∨ 33603584 ≤ address.toNat) :
    run (SailRV32.Functions.within_clint (.Physaddr (address.setWidth 34)) size) before =
      .ok false before := by
  simp only [SailRV32.Functions.within_clint, SailRV32.Functions.plat_have_clint, SailRV32.not]
  rfl

theorem clint_excluded {before : State} {hart : BitVec 32} {address : BitVec 32}
    (initialized : before.regs.get? .mhartid = some hart)
    (outside : address.toNat < 33554432 ∨ 33603584 ≤ address.toNat) :
    run (SailRV32.Functions.within_clint (.Physaddr (address.setWidth 34)) 4) before =
      .ok false before :=
  clint_excluded_sized (by decide) initialized outside

theorem signature_excluded_sized {size : Nat} {address : BitVec 32}
    (positive : 0 < size)
    (outside : address.toNat < 201326592 ∨ 201326624 ≤ address.toNat) :
    SailRV32.Functions.within_sig (.Physaddr (address.setWidth 34)) size = pure false := by
  have excluded : ((201326592 ≤b address.toNat) &&
      ((address.toNat : Int) + size ≤b 201326624)) = false := by
    by_cases low : 201326592 ≤ address.toNat
    · have high : ¬ ((address.toNat : Int) + size ≤ 201326624) := by omega
      simp [low, high]
    · simp [low]
  have reduced : (address.toNat : Int) % 17179869184 = address.toNat :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have bound := address.isLt; omega)
  simp [SailRV32.Functions.within_sig, SailRV32.Functions.plat_have_sig, SailRV32.not,
    signature_base, signature_size, _root_.Sail.BitVec.toNatInt, reduced, excluded]

theorem signature_excluded {address : BitVec 32}
    (outside : address.toNat < 201326592 ∨ 201326624 ≤ address.toNat) :
    SailRV32.Functions.within_sig (.Physaddr (address.setWidth 34)) 4 = pure false :=
  signature_excluded_sized (by decide) outside

theorem htif_disabled {before : State}
    (disabled : before.regs.get? .htif_tohost_base = some none)
    (address : SailRV32.physaddr) (width : Nat) :
    run (SailRV32.Functions.within_htif_writable address width) before = .ok false before := by
  cases address
  simp only [SailRV32.Functions.within_htif_writable]
  rw [run_bind_of_ok _ _ _ _ _ (read_register disabled)]
  rfl

private theorem ordinary_windows {address : BitVec 32} (outside : OrdinaryWordAddress address) :
    (address.toNat < 33554432 ∨ 33603584 ≤ address.toNat) ∧
      (address.toNat < 201326592 ∨ 201326624 ≤ address.toNat) := by
  simpa [OrdinaryWordAddress, clint_base, clint_size, signature_base, signature_size] using outside

theorem mmio_read_excluded_sized {size : Nat} {before : State} {hart : BitVec 32} {address : BitVec 32}
    (positive : 0 < size) (initialized : before.regs.get? .mhartid = some hart)
    (disabled : before.regs.get? .htif_tohost_base = some none)
    (outside : OrdinaryWordAddress address) :
    run (SailRV32.Functions.within_mmio_readable (.Physaddr (address.setWidth 34)) size)
      before = .ok false before := by
  obtain ⟨clint, signature⟩ := ordinary_windows outside
  simp only [SailRV32.Functions.within_mmio_readable, SailRV32.Functions.get_config_rvfi,
    Bool.false_eq_true, ite_false]
  rw [run_bind_of_ok _ _ _ _ _ (clint_excluded_sized positive initialized clint)]
  simp only [signature_excluded_sized positive signature, freeM_pure_bind,
    SailRV32.Functions.within_htif_readable]
  rw [run_bind_of_ok _ _ _ _ _ (htif_disabled disabled _ size)]
  rfl

theorem mmio_read_excluded {before : State} {hart : BitVec 32} {address : BitVec 32}
    (initialized : before.regs.get? .mhartid = some hart)
    (disabled : before.regs.get? .htif_tohost_base = some none)
    (outside : OrdinaryWordAddress address) :
    run (SailRV32.Functions.within_mmio_readable (.Physaddr (address.setWidth 34)) 4)
      before = .ok false before :=
  mmio_read_excluded_sized (by decide) initialized disabled outside

theorem mmio_write_excluded_sized {size : Nat} {before : State} {hart : BitVec 32} {address : BitVec 32}
    (positive : 0 < size) (initialized : before.regs.get? .mhartid = some hart)
    (disabled : before.regs.get? .htif_tohost_base = some none)
    (outside : OrdinaryWordAddress address) :
    run (SailRV32.Functions.within_mmio_writable (.Physaddr (address.setWidth 34)) size)
      before = .ok false before := by
  obtain ⟨clint, signature⟩ := ordinary_windows outside
  simp only [SailRV32.Functions.within_mmio_writable, SailRV32.Functions.get_config_rvfi,
    Bool.false_eq_true, ite_false]
  rw [run_bind_of_ok _ _ _ _ _ (clint_excluded_sized positive initialized clint)]
  simp only [signature_excluded_sized positive signature, freeM_pure_bind]
  rw [run_bind_of_ok _ _ _ _ _ (htif_disabled disabled _ size)]
  rfl

theorem mmio_write_excluded {before : State} {hart : BitVec 32} {address : BitVec 32}
    (initialized : before.regs.get? .mhartid = some hart)
    (disabled : before.regs.get? .htif_tohost_base = some none)
    (outside : OrdinaryWordAddress address) :
    run (SailRV32.Functions.within_mmio_writable (.Physaddr (address.setWidth 34)) 4)
      before = .ok false before :=
  mmio_write_excluded_sized (by decide) initialized disabled outside

end Airbender.Reference.RiscV.Sail
