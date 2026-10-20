import Airbender.Proofs.ShiftBinop.ShiftEquations
import Airbender.Proofs.Mersenne31

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Verification Trace
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Three bounded native contribution limbs add without Mersenne31 wrap. This
    does not assume that their sum is already a canonical 16-bit limb. -/
theorem shift_sum_value (a b c r : ZMod mersenne31Modulus)
    (ha : a.val < 65536) (hb : b.val < 65536) (hc : c.val < 65536)
    (equation : a + b + c = r) : r.val = a.val + b.val + c.val := by
  have small : a.val + b.val + c.val < mersenne31Modulus := by
    change _ < 2147483647
    omega
  have field : ((a.val + b.val + c.val : Nat) : ZMod mersenne31Modulus) = r := by
    simp only [Nat.cast_add,ZMod.natCast_zmod_val]
    exact equation
  have natural := congrArg ZMod.val field
  rw [ZMod.val_natCast_of_lt small] at natural
  exact natural.symm

/-- Native decoding and accepted tables force truncation, exact RV32 lookup
    contributions and actual selected-word assembly, with no source-bound premise. -/
theorem selected_shift_contributions {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (kind : ShiftKind) (immediate : Bool)
    (mask : w 12 = ((kind.operation.mask + if immediate then 32 else 0 : Nat) : ZMod mersenne31Modulus))
    (tag : w 11 = (kind.operation.funct3 : ZMod mersenne31Modulus)) :
    ShiftContributions w kind := by
  have equations := shift_equations holds kind immediate mask
  obtain ⟨operandBound,amount,padding⟩ := shift_truncation holds kind immediate mask tag
  have parts (slot : Fin 3) : (w (43 + 4 * slot.val)).val < 2097152 ∧
      (partWord w slot).Bounded ∧ (partWord w slot).toBitVec =
        (kind.parts[slot.val]).result (w (43 + 4 * slot.val)).val :=
    native_part_result _ _ (shift_part_members holds kind immediate mask tag slot)
  have low := shift_sum_value (w 44) (w 48) (w 52) (w 55)
    (parts 0).2.1.1 (parts 1).2.1.1 (parts 2).2.1.1 equations.low
  have high := shift_sum_value (w 45) (w 49) (w 53) (w 56)
    (parts 0).2.1.2 (parts 1).2.1.2 (parts 2).2.1.2 equations.high
  refine ⟨operandBound,amount,padding,equations.keys,parts,low,high,?_⟩
  have packed : (selectedWord w).value =
      (partWord w 0).value + (partWord w 1).value + (partWord w 2).value := by
    dsimp [selectedWord,partWord,Word.value,limbBase]
    rw [low,high]
    ring
  simp only [Word.toBitVec,packed,BitVec.ofNat_add]

/-- Original public metadata supplies the operation mask and funct3; the native
    constraints and actual tagged lookup rows supply every contribution. -/
theorem entry_shift_contributions {w : Nat → ZMod mersenne31Modulus} {entry : ProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (kind : ShiftKind)
    (family : entry.data.family = kind.operation) : ShiftContributions w kind := by
  obtain ⟨_,immediate,mask,tag⟩ := decoder_field_bounds fields
  have maskQuery := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
  change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at maskQuery
  have tagQuery := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[8]) query
  change w 11 = (entry.data.funct3 : ZMod mersenne31Modulus) at tagQuery
  exact selected_shift_contributions holds kind immediate
    (by rw [maskQuery,mask,family]) (by rw [tagQuery,tag,family])

theorem fetched_shift_contributions {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧
      decoderQuery w = entry.query ∧ Routing w entry ∧
      ∀ kind, entry.data.family = kind.operation → ShiftContributions w kind := by
  obtain ⟨entry,present,source,query,routing⟩ := fetched_routing image holds member
  exact ⟨entry,present,source,query,routing,fun kind family =>
    entry_shift_contributions holds source.fields query kind family⟩

end Airbender.ShiftBinop.Proofs
