namespace Airbender.Verification.FiniteGridChecks
set_option warningAsError true

def check (first second third : Nat) (left right : Fin first → Fin second → Fin third → Nat) : Bool :=
  (List.finRange first).all fun a => (List.finRange second).all fun b =>
    (List.finRange third).all fun c => left a b c == right a b c

theorem check_sound (first second third : Nat) (left right : Fin first → Fin second → Fin third → Nat)
    (checked : check first second third left right = true) (a : Fin first) (b : Fin second) (c : Fin third) :
    left a b c = right a b c := by
  have row := List.all_eq_true.mp checked a (List.mem_finRange a)
  have lane := List.all_eq_true.mp row b (List.mem_finRange b)
  exact beq_iff_eq.mp (List.all_eq_true.mp lane c (List.mem_finRange c))

end Airbender.Verification.FiniteGridChecks
