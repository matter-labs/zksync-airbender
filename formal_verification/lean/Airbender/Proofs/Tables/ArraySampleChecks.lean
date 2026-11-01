import Mathlib.Init

namespace Airbender.Verification.ArraySampleChecks
set_option warningAsError true

structure Request where
  count : Nat
  values : Array Nat
  expected : Fin count → Nat

def check (requests : List Request) : Bool :=
  requests.all fun request => request.values.size == request.count &&
    (List.finRange request.count).all fun index =>
      request.values[index.val]?.getD 0 == request.expected index

def Fact (request : Request) : Prop :=
  request.values.size = request.count ∧
    ∀ index : Fin request.count, request.values[index.val]?.getD 0 = request.expected index

theorem check_sound (requests : List Request) (checked : check requests = true)
    (request : Request) (member : request ∈ requests) : Fact request := by
  have row := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked request member)
  exact ⟨beq_iff_eq.mp row.1, fun index =>
    beq_iff_eq.mp (List.all_eq_true.mp row.2 index (List.mem_finRange index))⟩

theorem check_sound_at (requests : List Request) (checked : check requests = true)
    (index : Fin requests.length) : Fact (requests.get index) :=
  check_sound requests checked _ (List.get_mem requests index)

theorem size_sound (request : Request) (fact : Fact request) :
    request.values.size = request.count := fact.1

theorem sample_sound (request : Request) (fact : Fact request) (index : Fin request.count) :
    request.values[index.val]'(by rw [size_sound request fact]; exact index.isLt) =
      request.expected index := by
  have sample := fact.2 index
  simpa only [Array.getElem?_eq_getElem (by rw [fact.1]; exact index.isLt),
    Option.getD_some] using sample

theorem size_sound_bound (request : Request) (fact : Fact request)
    (values : Array Nat) (binding : values = request.values) : values.size = request.count :=
  (congrArg Array.size binding).trans (size_sound request fact)

theorem sample_sound_bound (request : Request) (fact : Fact request)
    (values : Array Nat) (binding : values = request.values) (index : Fin request.count) :
    values[index.val]'(by rw [size_sound_bound request fact values binding]; exact index.isLt) =
      request.expected index := by
  subst values
  exact sample_sound request fact index

end Airbender.Verification.ArraySampleChecks
