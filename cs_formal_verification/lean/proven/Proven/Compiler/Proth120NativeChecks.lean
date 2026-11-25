module
public import Human.Import.Exec.Proth120Native
public import Human.Helpers.Properties
public import Proven.GKRProtocol.CleanArithmetic

@[expose] public section
namespace Airbender.Compiler.Proth120Native

variable {F : Type} [Field F]

/-- Assign a finite polynomial variable to each physical address. Both directions are
    checked on the actual wires of each gate; unused addresses need no representation. -/
structure Coordinates (n : Nat) where
  wire : GKRAddress → Fin n
  address : Fin n → GKRAddress
  slot : Nat → Fin n

def Gate.polynomial (c : Coordinates n) (decode : Nat → F) (g : Gate) : Polynomial n F :=
  let input := g.2.map fun (v, wires) => (decode v, wires.map c.wire)
  match g.1 with
  | none => input
  | some out => add (atom (c.wire out)) (negate input)

def Gate.addresses (g : Gate) := g.1.toList ++ g.2.flatMap Prod.snd

theorem terms_value {c : Coordinates n} {terms : Terms} {decode : Nat → F} {physical : GKRAddress → F}
    (back : ∀ a ∈ terms.flatMap Prod.snd, c.address (c.wire a) = a) :
    evaluate (physical ∘ c.address) (terms.map fun (v, wires) => (decode v, wires.map c.wire)) =
      value decode physical terms := by
    unfold value
    simp only [evaluate, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    dsimp [monomialValue, List.map_map]
    congr 2
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    simp [Function.comp_def, back a (List.mem_flatMap.mpr ⟨t, ht, ha⟩)]
theorem Gate.zero {c : Coordinates n} {g : Gate} {decode : Nat → F} {physical : GKRAddress → F}
    (back : ∀ a ∈ g.addresses, c.address (c.wire a) = a) (satisfies : g.Holds decode physical) :
    evaluate (physical ∘ c.address) (g.polynomial c decode) = 0 := by
  have eqInput := terms_value (c := c) (decode := decode) (physical := physical) (terms := g.2)
    (fun a ha => back a (List.mem_append_right _ ha))
  cases hout : g.1 with
  | none => simpa [Gate.polynomial, hout, eqInput] using
      (show _ from satisfies.symm.trans (by simp [hout]))
  | some a =>
    have ha := back a (List.mem_append_left _ (by simp [hout]))
    simp only [Gate.polynomial, hout, evaluate_add, evaluate_atom, evaluate_negate, eqInput]
    rw [Function.comp_apply, ha, show physical a = _ from by simpa [Gate.Holds, hout] using satisfies]
    exact add_neg_cancel _

variable [DecidableEq F]

instance (decode : Nat → F) (physical : GKRAddress → F) (g : Gate) : Decidable (g.Holds decode physical) := by
  unfold Gate.Holds
  infer_instance

def checks (coords : Coordinates n) (decode : Nat → F) (places : List (Nat × GKRAddress))
    (e : Airbender.Expression F) (gate : Gate) : Bool :=
  gate.addresses.all (fun a => decide (coords.address (coords.wire a) = a)) &&
  (CleanExpression.inputs e).all (fun i => decide ((i, coords.address (coords.slot i)) ∈ places)) &&
  equal (CleanExpression.polynomial coords.slot e) (gate.polynomial coords decode)

theorem checked_assertion {coords : Coordinates n} {decode : Nat → F} {places : List (Nat × GKRAddress)}
    {e : Airbender.Expression F} {g : Gate} (checked : checks coords decode places e g = true)
    {physical : GKRAddress → F} {logical : Nat → F} (accepted : g.Holds decode physical)
    (agreement : ∀ kv ∈ places, logical kv.1 = physical kv.2) :
    e.eval (Verification.environment logical) = 0 := by
  obtain ⟨⟨ga, la⟩, eq⟩ := Bool.and_eq_true_iff.mp checked |>.imp_left Bool.and_eq_true_iff.mp
  rw [← CleanExpression.polynomial_value e coords.slot (physical ∘ coords.address) _ (by
    intro i hi
    exact (agreement _ (of_decide_eq_true (List.all_eq_true.mp la i hi))).symm)]
  exact (equal_sound eq _).trans (g.zero (fun a ha => of_decide_eq_true (List.all_eq_true.mp ga a ha)) accepted)

theorem checked_field {coords : Coordinates n} {decode : Nat → F} {places : List (Nat × GKRAddress)}
    {e : Airbender.Expression F} {ts : Terms} (checked : checks coords decode places e (none, ts) = true)
    {physical : GKRAddress → F} {logical : Nat → F}
    (agreement : ∀ kv ∈ places, logical kv.1 = physical kv.2) :
    e.eval (Verification.environment logical) = value decode physical ts := by
  obtain ⟨⟨ga, la⟩, eq⟩ := Bool.and_eq_true_iff.mp checked |>.imp_left Bool.and_eq_true_iff.mp
  rw [← CleanExpression.polynomial_value e coords.slot (physical ∘ coords.address) _ (by
    intro i hi; exact (agreement _ (of_decide_eq_true (List.all_eq_true.mp la i hi))).symm)]
  exact (equal_sound eq _).trans (terms_value (fun a ha =>
    of_decide_eq_true (List.all_eq_true.mp ga a (List.mem_append_right _ ha))))

def fieldsCheck (c : Coordinates n) (decode : Nat → F) (places : List (Nat × GKRAddress)) :
    List (Airbender.Expression F) → List Terms → Bool
  | [], [] => true
  | x::xs, t::ts => checks c decode places x (none, t) && fieldsCheck c decode places xs ts
  | _, _ => false

theorem fields_value {c : Coordinates n} {decode : Nat → F} {places : List (Nat × GKRAddress)}
    {es : List (Airbender.Expression F)} {ts : List Terms}
    (h : fieldsCheck c decode places es ts = true) {physical : GKRAddress → F} {logical : Nat → F}
    (agreement : ∀ kv ∈ places, logical kv.1 = physical kv.2) :
    es.map (fun e => e.eval (Verification.environment logical)) = ts.map (value decode physical) := by
  induction es generalizing ts with
  | nil => cases ts <;> first | rfl | cases h
  | cons e es ih =>
    cases ts with
    | nil => cases h
    | cons t ts =>
      obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp h
      exact congrArg₂ List.cons (checked_field first agreement) (ih rest)

/-- Consume exactly one checked native gate index for every logical assertion. A short
    selector list, a surplus selector, and an out-of-range gate all fail the certificate. -/
def checkRows (c : Coordinates n) (decode : Nat → F) (places : List (Nat × GKRAddress))
    (gates : List Gate) : List (Airbender.Expression F) → List Nat → Bool
  | [], [] => true
  | e :: es, i :: is => (gates[i]?.any (checks c decode places e)) && checkRows c decode places gates es is
  | _, _ => false

theorem rows_sound {c : Coordinates n} {decode : Nat → F} {places : List (Nat × GKRAddress)}
    {gates : List Gate} {es : List (Airbender.Expression F)} {is : List Nat}
    (checked : checkRows c decode places gates es is = true)
    {physical : GKRAddress → F} {logical : Nat → F}
    (accepted : ∀ g ∈ gates, g.Holds decode physical)
    (agreement : ∀ kv ∈ places, logical kv.1 = physical kv.2) :
    ∀ e ∈ es, e.eval (Verification.environment logical) = 0 := by
  induction es generalizing is with
  | nil => simp
  | cons e rest ih =>
    cases is with
    | nil => cases checked
    | cons i tail =>
      obtain ⟨first, others⟩ := Bool.and_eq_true_iff.mp checked
      cases h : gates[i]? with
      | none => simp [h] at first
      | some g =>
        have hg := List.mem_of_getElem? h
        have he := checked_assertion (by simpa [h] using first) (accepted g hg) agreement
        exact List.forall_mem_cons.mpr ⟨he, ih others⟩

end Airbender.Compiler.Proth120Native
