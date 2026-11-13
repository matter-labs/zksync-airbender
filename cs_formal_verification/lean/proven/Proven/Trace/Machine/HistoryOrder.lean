module
public import Proven.Trace.RVHistory

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
set_option warningAsError true

/-- A strict native event order fixes the order of any sorted permutation. -/
theorem events_eq_of_sorted {events canonical : List MemoryAccess}
    (permutation : events.Perm canonical)
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (strict : canonical.Pairwise (fun a b => b.1 < a.1)) : events = canonical := by
  have distinct : (canonical.map Prod.fst).Nodup :=
    (List.pairwise_map.mpr strict).imp (by intro a b less; exact Ne.symm (Nat.ne_of_lt less))
  apply List.Perm.eq_of_pairwise ?_ ordered (strict.imp (by intro a b less; exact Nat.le_of_lt less)) permutation
  intro first last included present one two
  exact List.inj_on_of_nodup_map distinct (permutation.mem_iff.mp included) present (Nat.le_antisymm two one)

/-- RV memory histories depend on addresses and values, not timestamp labels. -/
theorem history_of_payloads {cells : List Cell} {events target : List MemoryAccess} {before after : RV.State}
    (history : RVHistory cells events before after) (payloads : events.map Prod.snd = target.map Prod.snd) :
    RVHistory cells target before after := by
  induction history generalizing target with
  | nil state =>
    have empty : target = [] := by simpa using payloads.symm
    subst target
    exact .nil _
  | @cons event rest before middle after past cell member address read write ih =>
    cases target with
    | nil => simp at payloads
    | cons head tail =>
      have same : event.2 = head.2 ∧ rest.map Prod.snd = tail.map Prod.snd := by simpa using payloads
      exact .cons (ih same.2) cell member (same.1 ▸ address) (same.1 ▸ read) (same.1 ▸ write)

end Airbender.Trace.Machine.Proofs
