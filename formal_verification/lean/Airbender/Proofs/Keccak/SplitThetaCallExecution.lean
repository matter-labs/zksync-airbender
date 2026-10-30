import Airbender.Proofs.Keccak.SplitThetaWriteProjection
import Airbender.Proofs.Trace.AtomicWrites
import Airbender.Proofs.Trace.TransferHistory

namespace Airbender.Keccak.Split.Native.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Each register and lane port used by the call proof occurs in the actual native array. -/
theorem theta_call_ports_present (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    thetaControlPort cached ∈ (⟨.thetaRho, w⟩ : Row babyBearModulus).ports cached ∧
      thetaPointerPort cached ∈ (⟨.thetaRho, w⟩ : Row babyBearModulus).ports cached ∧
      ∀ (lane : Fin 7) (high : Bool), thetaLanePort cached lane high ∈
        (⟨.thetaRho, w⟩ : Row babyBearModulus).ports cached := by
  simp only [← Array.mem_toList_iff, theta_ports_enumeration]
  refine ⟨List.mem_append_left _ (List.mem_cons_self),
    List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
  intro lane high
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨lane, by simp, ?_⟩
  cases high
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The actual initialized native theta history executes the original complete split call. -/
theorem theta_call_executes (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable else ThetaRho.clockConstraints thetaRhoFixedTable))
    (active : w 0 = 1) (index : Fin 361) {before after : State}
    (arguments : ArgumentsAt index.val before)
    (boundedReads : ∀ port ∈ (⟨.thetaRho, w⟩ : Row babyBearModulus).ports cached,
      (readToken w port).word.Bounded)
    {cells : List Cell} {events : List MemoryAccess}
    (history : SailHistory cells events before after)
    (permutation : events.Perm
      (((⟨.thetaRho, w⟩ : Row babyBearModulus).memorySteps cached).map transferEvent))
    (observed : ∀ port ∈ (⟨.thetaRho, w⟩ : Row babyBearModulus).ports cached, ∃ cell : Cell,
      cell.addressCode = port.address.code w ∧
        cell.read before = .ok (readToken w port).word.toBitVec before) :
    Call.Executes .thetaRho before after := by
  have present := theta_call_ports_present cached w
  have boundedLane (lane : Fin 7) (high : Bool) := boundedReads _ (present.2.2 lane high)
  have controls := theta_call_control_binding cached w holds active index before arguments
    (observed _ present.1)
  obtain ⟨pointer, pointerRead, _, aligned, pointerWord⟩ :=
    theta_call_pointer_binding cached w index before arguments (boundedReads _ present.2.1) (observed _ present.2.1)
  refine ⟨index, pointer, thetaReferenceLanes cached false w, controls.1, arguments, pointerRead, ?_, ?_⟩
  · intro lane live
    change lane.val < 7 at live
    let native : Fin 7 := ⟨lane.val, live⟩
    have limbBounds := theta_read_limb_bounds cached w native (boundedLane native)
    have read (high : Bool) :
        (Call.laneCell pointer (Call.slots index)[lane] high).read before =
          .ok (Call.half (thetaReferenceLanes cached false w)[lane] high) before := by
      obtain ⟨cell, code, found⟩ := observed _ (present.2.2 native high)
      have address := theta_call_lane_address cached high w pointer aligned pointerWord index native
        (controls.2.2.2.1 native)
      have same := cell_address_injective (code.trans address)
      rw [same] at found
      have half := theta_lane_port_half cached false high w native (limbBounds 0) (limbBounds 1)
      change Call.half (thetaLaneValue cached false w native) high =
        (readToken w (thetaLanePort cached native high)).word.toBitVec at half
      rw [← half] at found
      simpa only [thetaReferenceLanes, Fin.getElem_fin, Vector.getElem_ofFn] using found
    refine ⟨?_, read false, read true⟩
    simpa only [thetaReferenceLanes, Fin.getElem_fin, Vector.getElem_ofFn] using
      theta_read_lane_bound cached w native (boundedLane native)
  · apply atomic_writes_of_history history
    have projection := theta_call_write_projection cached w holds index controls.1 controls.2.2.2.2 boundedLane pointer aligned
      pointerWord controls.2.2.1 controls.2.2.2.1
    have mapped := permutation.map (fun event => (event.2.1, memoryWord event.2.2.2))
    apply mapped.trans
    apply List.Perm.of_eq
    simpa only [List.map_map, Function.comp_def, transferEvent, memoryWord, MemoryToken.word] using projection

end Airbender.Keccak.Split.Native.Proofs
