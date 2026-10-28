import Airbender.Review.Helpers.Decoder.PooledProgram

namespace Airbender.ExternalBoundary.Decoder
open Trace

/-- Committed setup rows are kept separately for each actual native family.
    Extraction, commitment authentication and cached preprocessing must bind
    these full nine-column rows; a table name or digest alone is insufficient. -/
abbrev Rows (p : Nat) (Kind : Type) := Kind → List (Vector (ZMod p) 9)

/-- External interpretation of the committed decoder setup. The current
    untagged native filler is field-minus-one in every column; tagged setups
    use their discriminator. Each real row comes from the public
    Sail-decoded program; filler has field-minus-one in a guarded column. The
    active query's guarded limb is typed independently of decoder membership.
    PC-low is one possible guarded column, not the only corrected column. The
    active-limb encoding and every full query/family connection remain external
    obligations, including committed/cached/scalar/vectorized agreement. -/
structure Binding {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    (trace : Data p Kind) (program : List (ProgramEntry Kind)) (rows : Rows p Kind)
    (column : Fin 9) : Prop where
  contents : ∀ family, ∀ value ∈ rows family,
    (∃ entry ∈ program, entry.data.family = family ∧ value = entry.query) ∨ value[column] = -1
  lookups : ∀ row ∈ trace.rows, row.decoderQuery ∈ rows row.family
  /-- Binding to a typed native limb, rather than assuming a decoded instruction. -/
  typed : ∀ row ∈ trace.rows, ∃ limb : Fin 65536,
    row.decoderQuery[column] = (limb.val : ZMod p)

end Airbender.ExternalBoundary.Decoder
