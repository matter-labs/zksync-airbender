import Airbender.Proofs.Keccak.SplitChiWriteProjection
import Airbender.Proofs.Trace.AtomicWrites
import Airbender.Proofs.Trace.TransferHistory

namespace Airbender.Keccak.Split.Native.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
variable [Fact babyBearModulus.Prime]

/-- Each register and lane port used by the call proof occurs in the actual native array. -/
theorem chi5_call_ports_present (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    chi5ControlPort cached ∈ (⟨.chi5, w⟩ : Row babyBearModulus).ports cached ∧
      chi5PointerPort cached ∈ (⟨.chi5, w⟩ : Row babyBearModulus).ports cached ∧
      ∀ (lane : Fin 5) (high : Bool), chi5LanePort cached lane high ∈
        (⟨.chi5, w⟩ : Row babyBearModulus).ports cached := by
  simp only [← Array.mem_toList_iff, chi5_ports_enumeration]
  refine ⟨List.mem_append_left _ (List.mem_cons_self),
    List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
  intro lane high
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨lane, by simp, ?_⟩
  cases high
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The actual initialized native chi5 history executes the original complete split call. -/
theorem chi5_call_executes (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (active : w 0 = 1) (index : Fin 361) {before after : State}
    (arguments : ArgumentsAt index.val before)
    (pointerBound : (readToken w (chi5PointerPort cached)).word.Bounded)
    {cells : List Cell} {events : List MemoryAccess}
    (history : SailHistory cells events before after)
    (permutation : events.Perm
      (((⟨.chi5, w⟩ : Row babyBearModulus).memorySteps cached).map transferEvent))
    (observed : ∀ port ∈ (⟨.chi5, w⟩ : Row babyBearModulus).ports cached, ∃ cell : Cell,
      cell.addressCode = port.address.code w ∧
        cell.read before = .ok (readToken w port).word.toBitVec before) :
    Call.Executes .chi5 before after := by
  have present := chi5_call_ports_present cached w
  have controls := chi5_call_control_binding cached w holds active index before arguments
    (observed _ present.1)
  obtain ⟨pointer, pointerRead, _, aligned, pointerWord⟩ :=
    chi5_call_pointer_binding cached w index before arguments pointerBound (observed _ present.2.1)
  refine ⟨index, pointer, chi5ReferenceLanes cached false w, controls.1, arguments, pointerRead, ?_, ?_⟩
  · intro lane live
    change lane.val < 5 at live
    let native : Fin 5 := ⟨lane.val, live⟩
    have read (high : Bool) :
        (Call.laneCell pointer (Call.slots index)[lane] high).read before =
          .ok (Call.half (chi5ReferenceLanes cached false w)[lane] high) before := by
      obtain ⟨cell, code, found⟩ := observed _ (present.2.2 native high)
      have address := chi5_call_lane_address cached high w pointer aligned pointerWord index native
        (controls.2.2.2 native)
      have same := cell_address_injective (code.trans address)
      rw [same] at found
      have half := chi5_lane_port_half cached false high w holds native
      change Call.half (chi5LaneValue cached false w native) high =
        (readToken w (chi5LanePort cached native high)).word.toBitVec at half
      rw [← half] at found
      simpa only [chi5ReferenceLanes, Fin.getElem_fin, Vector.getElem_ofFn, dif_pos live] using found
    refine ⟨?_, read false, read true⟩
    simpa only [chi5ReferenceLanes, Fin.getElem_fin, Vector.getElem_ofFn, dif_pos live] using
      chi5_lane_bound cached false w holds native
  · apply atomic_writes_of_history history
    have projection := chi5_call_write_projection cached w holds index controls.1 pointer aligned
      pointerWord controls.2.2.1 controls.2.2.2
    have mapped := permutation.map (fun event => (event.2.1, memoryWord event.2.2.2))
    apply mapped.trans
    apply List.Perm.of_eq
    simpa only [List.map_map, Function.comp_def, transferEvent, memoryWord, MemoryToken.word] using projection

end Airbender.Keccak.Split.Native.Proofs
