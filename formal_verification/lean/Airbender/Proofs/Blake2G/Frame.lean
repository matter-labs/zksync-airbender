import Airbender.Proofs.Blake2G.FrameDefinitions
import Airbender.Proofs.Arithmetic.FieldSlices
import Airbender.Proofs.Blake2G.Assembly

namespace Airbender.Blake2G.Proofs
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- A projection certificate contains only obligations discharged from the
    source constraints; it is an internal proof object, not a public premise. -/
structure Frame.Certificate {p : Nat} [Fact p.Prime] (frame : Frame p)
    (table : Table (ZMod p) (fields 9)) : Prop where
  flags : ∀ k : Fin 12, frame.base Variables.booleanColumns[1 + k.val] = 0 ∨
    frame.base Variables.booleanColumns[1 + k.val] = 1
  queries : QueryHolds table frame.assignment

theorem Frame.Certificate.holds {p : Nat} [Fact p.Prime] {frame : Frame p}
    {table : Table (ZMod p) (fields 9)} (certificate : frame.Certificate table) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment frame.assignment)
      (mixingConstraints table) :=
  assembled_holds frame.base table certificate.flags certificate.queries

end Airbender.Blake2G.Proofs
