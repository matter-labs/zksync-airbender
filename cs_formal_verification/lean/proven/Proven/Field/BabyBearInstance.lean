module
public import Proven.CircuitField

@[expose] public section

/-- Specialize a circuit theorem to its host. Common size and two-adic inverse premises come
    from the field instance. Closed identities involving a coefficient embedded in a particular
    layout are checked in that host: e.g. `(-30720) * 65536 = 1` belongs to a BabyBear artifact. -/
macro "circuit_field_instance " h:term " at " host:term : tactic => `(tactic| (
  let _ : Airbender.CircuitField $host := inferInstance
  apply $h (p := $host) <;> first
    | exact lt_of_le_of_lt (by decide) (Airbender.CircuitField.limbCapacity (p := $host))
    | exact le_trans (by decide) (Airbender.CircuitField.limbCapacity (p := $host)).le
    | apply Airbender.CircuitField.invPow_mul <;> decide
    | rw [mul_comm]; apply Airbender.CircuitField.invPow_mul <;> decide
    | decide))

/-- The unrolled CPU and worker captures serialize BabyBear coefficients. -/
macro "babybear_instance " h:term : tactic => `(tactic| circuit_field_instance $h at Airbender.babyBearModulus)
