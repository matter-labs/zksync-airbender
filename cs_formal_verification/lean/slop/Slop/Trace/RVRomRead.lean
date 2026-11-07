import Slop.Trace.RVValues

/-! RV twin of `ROM.Proofs.read_source`: an active word-ROM query reads the ROM image at its address
    (`RV.read initial.rom`), not a separately supplied value (from `rv_rom_member`, RVValues.lean). -/

namespace Airbender.Trace.RVValues
open Arithmetic Trace.Proofs

/-- An active ROM query at a canonical address below `ROM.limit` reads the ROM image's word there. -/
theorem rv_rom_read {p : Nat} [Fact p.Prime] (hp : ROM.limit < p)
    {before : RV.State} {cells : List Cell} (address : Word) (lo hi : ZMod p)
    (bounded : address.Bounded) (low : address.hi < 64)
    (contains : (ROM.table cells (romImageRV (p := p) before cells)).Contains #[]
      #v[(address.lo : ZMod p) + 65536 * address.hi, lo, hi, 0, 0, 0, 0, 0, 34]) :
    Cell.ram address.toBitVec ∈ cells ∧
      RV.read before.rom address.toBitVec 4 = (Word.mk lo.val hi.val).toBitVec := by
  have small : address.value < ROM.limit := by
    dsimp [Word.value, Word.Bounded, limbBase, ROM.limit] at *
    omega
  have modulus : limbBase < p := by dsimp [limbBase, ROM.limit] at *; omega
  rcases rv_rom_member contains with zero | ⟨source, sourceMember, sourceLow, equal⟩
  · have tag := congrArg (fun query : Vector (ZMod p) 9 => query[8]) zero
    change (34 : ZMod p) = 0 at tag
    have values := congrArg ZMod.val tag
    have cast : ((34 : Nat) : ZMod p).val = 34 :=
      ZMod.val_natCast_of_lt (by dsimp [ROM.limit] at hp; omega)
    norm_num only [Nat.cast_ofNat] at cast
    rw [cast, ZMod.val_zero] at values
    contradiction
  · have encoded := congrArg (fun query : Vector (ZMod p) 9 => query[0]) equal
    change (address.lo : ZMod p) + 65536 * address.hi = (source.toNat : ZMod p) at encoded
    have castAddress : (address.lo : ZMod p) + 65536 * address.hi = (address.value : ZMod p) := by
      simp [Word.value, limbBase]
    rw [castAddress] at encoded
    have natural := congrArg ZMod.val encoded
    rw [ZMod.val_natCast_of_lt (lt_trans small hp),
      ZMod.val_natCast_of_lt (lt_trans sourceLow hp)] at natural
    have sameAddress : address.toBitVec = source := by
      apply BitVec.eq_of_toNat_eq
      change address.value % 2 ^ 32 = source.toNat
      rw [Nat.mod_eq_of_lt (by dsimp [ROM.limit] at small; omega)]
      exact natural
    have lowWord := congrArg (fun query : Vector (ZMod p) 9 => query[1]) equal
    have highWord := congrArg (fun query : Vector (ZMod p) 9 => query[2]) equal
    change lo = ((Word.ofBitVec (RV.read before.rom source 4)).lo : ZMod p) at lowWord
    change hi = ((Word.ofBitVec (RV.read before.rom source 4)).hi : ZMod p) at highWord
    have bound := Word.ofBitVec_bound (RV.read before.rom source 4)
    have word : Word.mk lo.val hi.val = Word.ofBitVec (RV.read before.rom source 4) := by
      rw [lowWord, highWord, ZMod.val_natCast_of_lt (lt_trans bound.1 modulus),
        ZMod.val_natCast_of_lt (lt_trans bound.2 modulus)]
    rw [word, Word.ofBitVec_roundtrip, sameAddress]
    exact ⟨sourceMember, rfl⟩

end Airbender.Trace.RVValues
