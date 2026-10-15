import Airbender.Review.Helpers.Context.Model

namespace Airbender.PaddingBoundary
open Trace

/-- The enforced GKR contribution gate: `(input - 1) * execute + 1`.
    This definition records its algebra; Rust/artifact enforcement is external. -/
def mask [Ring R] (execute input : R) : R := 1 + execute * (input - 1)

/-- A symbolic global factor. `none` denotes multiplicative identity and
    `some value` retains the entire native tuple, including zero-valued tuples.
    Selector Booleanity below prevents other field values from being discarded. -/
def contribution [One R] [DecidableEq R] (execute : R) (value : α) : Option α :=
  if execute = 1 then some value else none

/-- Interpret a symbolic factor under any tuple encoding. -/
def evaluate [One R] (encode : α → R) : Option α → R
  | none => 1
  | some value => encode value

/-- All row occurrences remain present in the external argument. Inactive rows
    contribute identities; native tuple values and multiplicities are retained. -/
def contributions [One R] [DecidableEq R] (rows : List ρ) (execute : ρ → R)
    (values : ρ → List α) : List (Option α) :=
  rows.flatMap fun row => (values row).map (contribution (execute row))

/-- Select participation solely by the imported execute column. This preserves
    occurrence order and multiplicity; it imposes no clock or output condition. -/
def active {Kind : Type} [CircuitLayout Kind] [Fact p.Prime] (trace : Data p Kind) : Data p Kind :=
  { trace with rows := trace.rows.filter fun row => decide (row.assignment row.columns.execute = 1) }

/-- External logical binding for the actual masked PC and memory contributions.
    The same native execute column masks reads and writes. Identity factors stay
    explicit in these permutations; they are erased by the projection proof.

    This is the analogue of `VerifierBoundary.Binding`, not an assertion that
    sampled product equality deterministically implies multiset equality.
    GKR/cryptographic enforcement, address-space separation, selector-copy and
    Rust/artifact correspondence remain external. No row stuttering, desired
    read, final result or architectural execution is supplied. -/
structure Binding {Kind : Type} [CircuitLayout Kind] [Fact p.Prime] (trace : Data p Kind) : Prop where
  /-- The selector is the imported native execute flag and is Boolean. -/
  selectors : ∀ row ∈ trace.rows,
    row.assignment row.columns.execute = 0 ∨ row.assignment row.columns.execute = 1
  /-- Full raw PC/clock tuples and public endpoints, before identity erasure. -/
  states : (some trace.initial :: contributions trace.rows
    (fun row => row.assignment row.columns.execute) (fun row => [row.finish])).Perm
      (some trace.terminal :: contributions trace.rows
        (fun row => row.assignment row.columns.execute) (fun row => [row.start]))
  /-- All native port tuples and public memory boundaries, before identity erasure. -/
  memory : (trace.initialMemory.map some ++ contributions trace.rows
    (fun row => row.assignment row.columns.execute) Row.writes).Perm
      (trace.terminalMemory.map some ++ contributions trace.rows
        (fun row => row.assignment row.columns.execute) Row.reads)

/-- Full-layout imported constraints plus the external global-contribution
    boundary. Ungated auxiliary/range/timestamp lookups remain checked for every
    row, including padding. Decoder membership is required only after projection. -/
structure AcceptedLayout {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    (trace : Data p Kind) : Prop where
  constraints : ∀ row ∈ trace.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom)
  binding : Binding trace

end Airbender.PaddingBoundary
