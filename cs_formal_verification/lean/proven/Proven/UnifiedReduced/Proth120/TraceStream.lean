module
public import Human.Trace.UnifiedReduced.Proth120Trace
public import Proven.Trace.RVHistory

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace

/-- The memory argument touches registers and RAM. The independent stream can be replaced at
    either side by the same unread suffix while preserving all native read/write checks. -/
theorem history_with_input {cells events} {s t : RV.State} (h : RVHistory cells events s t)
    (stream : List RV.Word) : RVHistory cells events {s with input := stream} {t with input := stream} := by
  induction h with
  | nil => exact .nil _
  | @cons e es s mid t _ c mem addr read write ih =>
    have same (c' : Cell) : c'.readRV {mid with input := stream} = c'.readRV mid := by cases c' <;> rfl
    apply RVHistory.cons ih c mem addr ((same c).trans read)
    unfold Cell.applyRV at write ⊢
    rw [same]
    split at write
    · cases Option.some.inj write; simp_all
    · cases c <;> simp_all [Cell.writeRV] <;> subst t <;> rfl

theorem read_position {row : Row proth120Modulus Kind} {rest} (sorted : (row :: rest).Pairwise (fun a b => b.clock < a.clock)) :
    ExternalStream.index Row.clock isRead (row :: rest) row = ExternalStream.count isRead rest := by
  simp only [ExternalStream.index, ExternalStream.count, List.filter_cons, lt_self_iff_false, decide_false,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  congr 1
  apply List.filter_congr
  exact fun r hr => by simp [(List.pairwise_cons.mp sorted).1 r hr]

theorem tail_position {row : Row proth120Modulus Kind} {rest} (sorted : (row :: rest).Pairwise (fun a b => b.clock < a.clock))
    {r} (hr : r ∈ rest) : ExternalStream.index Row.clock isRead (row :: rest) r =
      ExternalStream.index Row.clock isRead rest r := by
  simp [ExternalStream.index, Nat.not_lt.mpr ((List.pairwise_cons.mp sorted).1 r hr).le]

end Airbender.UnifiedReduced.Proth120
