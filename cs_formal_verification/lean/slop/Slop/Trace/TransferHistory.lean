module
public import Slop.Trace.HistorySplit
public import Slop.Trace.OfflineMemory

@[expose] public section

namespace Airbender.Trace.Proofs.Transfer
set_option warningAsError true
set_option maxRecDepth 16384

structure Data (p : Nat) where
  initial : List (MemoryToken p)
  terminal : List (MemoryToken p)
  steps : List (MemoryToken p × MemoryToken p)

structure Facts (data : Data p) : Prop where
  matching : (data.initial ++ data.steps.map Prod.snd).Perm
    (data.terminal ++ data.steps.map Prod.fst)
  addresses : ∀ edge ∈ data.steps, edge.1.address = edge.2.address
  order : ∀ edge ∈ data.steps,
    (timeOfPair edge.1.time).value < (timeOfPair edge.2.time).value

def rawEvents (data : Data p) : List MemoryAccess :=
  List.append (α := MemoryAccess)
    (data.initial.map fun token => (0, token.address, 0, token.value))
    (data.steps.map transferEvent)

def memoryEpoch (data : Data p) : Nat :=
  (data.initial.map MemoryToken.address).foldr max 0 + 1

def eventClock (data : Data p) (event : MemoryAccess) : Nat :=
  if event.1 = 0 then event.2.1 else
    memoryEpoch data + (rawEvents data).length.succ * event.1 + (rawEvents data).idxOf event

def labeledEvents (data : Data p) : List MemoryAccess :=
  (rawEvents data).map (Trace.Proofs.relabelMemoryEvent (eventClock data))

theorem seed_below_epoch {data : Data p} {source : MemoryToken p}
    (member : source ∈ data.initial) : source.address < memoryEpoch data := by
  have maxBound : ∀ n ∈ data.initial.map MemoryToken.address,
      n ≤ (data.initial.map MemoryToken.address).foldr max 0 := by
    generalize data.initial.map MemoryToken.address = values
    induction values with
    | nil => simp
    | cons first rest ih =>
      intro n member
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact (ih n member).trans (Nat.le_max_right _ _)
  have bound := maxBound source.address (List.mem_map.mpr ⟨source, member, rfl⟩)
  exact Nat.lt_succ_of_le bound

theorem event_clock_order (data : Data p) {first last : MemoryAccess}
    (lastBound : last.1 = 0 → last.2.1 < memoryEpoch data)
    (earlier : last.1 < first.1) : eventClock data last < eventClock data first := by
  have firstPositive : first.1 ≠ 0 := by omega
  have lastIndex := List.idxOf_le_length (l := rawEvents data) (a := last)
  have firstIndex := List.idxOf_le_length (l := rawEvents data) (a := first)
  simp only [eventClock, ite_eq_right firstPositive]
  by_cases zero : last.1 = 0
  · rw [ite_eq_left zero]
    have bound := lastBound zero
    omega
  · rw [ite_eq_right zero]
    have multiplied := Nat.mul_le_mul_left (rawEvents data).length.succ
      (Nat.succ_le_of_lt earlier)
    simp only [Nat.mul_succ] at multiplied
    omega

theorem zero_event_seed {data : Data p} {event : MemoryAccess}
    (member : event ∈ rawEvents data) (zero : event.1 = 0) :
    ∃ source ∈ data.initial, event = (0, source.address, 0, source.value) := by
  rcases List.mem_append.mp member with initial | native
  · obtain ⟨source, present, rfl⟩ := List.mem_map.mp initial
    exact ⟨source, present, rfl⟩
  · obtain ⟨edge, _, rfl⟩ := List.mem_map.mp native
    simp [transferEvent] at zero

theorem raw_seed_bound {data : Data p} {event : MemoryAccess}
    (member : event ∈ rawEvents data) : event.1 = 0 → event.2.1 < memoryEpoch data := by
  intro zero
  obtain ⟨source, present, rfl⟩ := zero_event_seed member zero
  exact seed_below_epoch present

def nativeEventClock (data : Data p) (event : MemoryAccess) : Nat :=
  (event.1 - memoryEpoch data) / (rawEvents data).length.succ

theorem native_clock_roundtrip {data : Data p} {event : MemoryAccess}
    (positive : event.1 ≠ 0) :
    relabelMemoryEvent (nativeEventClock data)
      (relabelMemoryEvent (eventClock data) event) = event := by
  have index := List.idxOf_le_length (l := rawEvents data) (a := event)
  have clock : nativeEventClock data (relabelMemoryEvent (eventClock data) event) = event.1 := by
    simp only [nativeEventClock, relabelMemoryEvent, eventClock, ite_eq_right positive]
    have subtraction : memoryEpoch data + (rawEvents data).length.succ * event.1 +
        (rawEvents data).idxOf event - memoryEpoch data =
        (rawEvents data).length.succ * event.1 + (rawEvents data).idxOf event := by omega
    rw [subtraction, Nat.mul_add_div (Nat.succ_pos _) event.1 _,
      Nat.div_eq_of_lt (by omega), Nat.add_zero]
  apply Prod.ext
  · exact clock
  · rfl

theorem labeled_events_split (data : Data p) : labeledEvents data =
    List.append (α := MemoryAccess)
      (data.initial.map fun token => ((token.address, token.address, 0, token.value) : MemoryAccess))
      ((data.steps.map transferEvent).map (relabelMemoryEvent (eventClock data))) := by
  unfold labeledEvents rawEvents
  simp only [List.append_eq, List.map_append, List.map_map]
  congr 1

end Airbender.Trace.Proofs.Transfer
