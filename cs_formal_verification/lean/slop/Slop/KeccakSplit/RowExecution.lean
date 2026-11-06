import Slop.KeccakSplit.RowCommon
import Slop.KeccakSplit.Trace.AtomicWrites
import Slop.Arithmetic.Word

/- Sail-level steps shared by the three split-worker `executes` proofs (ported from
   PR #585's *_call_control_binding, *_call_pointer_binding, *_lane_port_half and
   *_call_executes). -/

namespace Airbender.Keccak.Split.RowProofs
open Airbender.Trace Airbender.Trace.Proofs Airbender.Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- A control word read through x10 identifies the call whose arguments hold. -/
theorem control_index {actual index : Fin 361} {before : State}
    (arguments : Call.ArgumentsAt index.val before)
    (read : (Cell.register 10).read before = .ok (Word.mk (controlAt actual.val) 0).toBitVec before) :
    actual = index := by
  obtain ⟨control, _, controlRead, _, controlWord, _⟩ := arguments
  rw [controlWord] at controlRead
  have bits := (EStateM.Result.ok.inj (read.symm.trans controlRead)).1
  have numeric := congrArg BitVec.toNat bits
  have a := SetupProofs.controlAt_lt actual.isLt
  have b := SetupProofs.controlAt_lt index.isLt
  simp only [Word.toBitVec, Word.value, limbBase, mul_zero, add_zero, BitVec.toNat_ofNat] at numeric
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at numeric
  exact Fin.ext (SetupProofs.controlAt_inj actual.isLt index.isLt numeric)

/-- Two bounded words split a lane into its halves. -/
theorem half_words {lo hi : Word} (bl : lo.Bounded) (bh : hi.Bounded) (high : Bool) :
    Call.half (lo.value + 2 ^ 32 * hi.value) high = (if high then hi else lo).toBitVec := by
  have l := Word.value_lt bl
  have h := Word.value_lt bh
  simp only [wordModulus] at l h
  cases high <;> simp only [Call.half, Bool.false_eq_true, ↓reduceIte, Word.toBitVec]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [show (lo.value + 2 ^ 32 * hi.value) / 2 ^ 32 = hi.value by omega]

theorem lane_words_bound {lo hi : Word} (bl : lo.Bounded) (bh : hi.Bounded) :
    lo.value + 2 ^ 32 * hi.value < 2 ^ 64 := by
  have l := Word.value_lt bl
  have h := Word.value_lt bh
  simp only [wordModulus] at l h
  omega

/-- A cell observed at a port's address is the cell with that address code. -/
theorem observed_read {port : MemoryPort} {w : Nat → ZMod babyBearModulus} {before : State}
    {target : Cell} (address : port.address.code w = target.addressCode)
    (observed : ∃ cell : Cell, cell.addressCode = port.address.code w ∧
      cell.read before = .ok (readToken w port).word.toBitVec before) :
    target.read before = .ok (readToken w port).word.toBitVec before := by
  obtain ⟨cell, code, read⟩ := observed
  rwa [cell_address_injective (code.trans address)] at read

/-- The Sail step of a row whose port values project onto the call's writes. -/
theorem executes_of_projection (row : Native.Row babyBearModulus) (index : Fin 361)
    {before after : State} {cells : List Cell} {events : List MemoryAccess}
    (arguments : Call.ArgumentsAt index.val before) (pointer : BitVec 32)
    (pointerRead : (Cell.register 11).read before = .ok pointer before) (input : Vector Nat 7)
    (lanes : ∀ lane : Fin 7, lane.val < Call.slotCount (kindAt index.val) →
      input[lane] < 2 ^ 64 ∧
      (Call.laneCell pointer (Call.slots index)[lane] false).read before =
        .ok (Call.half input[lane] false) before ∧
      (Call.laneCell pointer (Call.slots index)[lane] true).read before =
        .ok (Call.half input[lane] true) before)
    (history : SailHistory cells events before after)
    (permutation : events.Perm (row.memorySteps.map transferEvent))
    (projection : (row.memorySteps.map transferEvent).map
        (fun event => (event.2.1, memoryWord event.2.2.2)) =
      (Call.writes index pointer (Call.result index input)).map
        (fun entry => (entry.1.addressCode, entry.2))) :
    Call.ExecutesAt index before after := by
  refine ⟨pointer, input, arguments, pointerRead, lanes, ?_⟩
  apply atomic_writes_of_history history
  exact (permutation.map _).trans (List.Perm.of_eq projection)

end Airbender.Keccak.Split.RowProofs
