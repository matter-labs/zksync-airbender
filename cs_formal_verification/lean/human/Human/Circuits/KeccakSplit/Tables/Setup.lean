import Human.Circuits.KeccakSplit.ColumnParity.SetupArtifact
import Human.Circuits.KeccakSplit.ThetaRho.SetupArtifact
import Human.Circuits.KeccakSplit.Chi5.SetupArtifact
import Clean.Circuit.Operations
import Mathlib.Algebra.Field.ZMod

/- Native fixed tables of the three split Keccak workers, as exported from the Rust
   setup (`artifacts/setup/README.md`), not hand-written models. Each table keeps every
   exported row up to the trace length (2^22), padding included; every imported query
   fixes its tag column to one of the worker's table IDs (`Circuit.splitKeccakQueries`). -/

namespace Airbender.Keccak.Split

open Airbender.Import.Setup

/-- Row `i` of a decoded setup: each column decoded from its blocks. -/
noncomputable def setupRow (data : SetupData) (width : Nat) (i : Nat) : Vector Int width :=
  Vector.ofFn fun c => decode (data.columns.getD c.val []) i

/-- The fixed table of a decoded setup: exactly its exported rows. -/
noncomputable def setupTable {p : Nat} [Fact p.Prime] (data : SetupData) (width : Nat) (name : String) :
    Table (ZMod p) (fields width) := .fromStatic {
  name := name
  length := data.traceLen
  row i := (setupRow data width i.val).map (fun (v : Int) => (v : ZMod p))
  index _ := 0
  Spec x := ∃ i : Fin data.traceLen, x = (setupRow data width i.val).map (fun (v : Int) => (v : ZMod p))
  contains_iff _ := Iff.rfl
}

/-- Column parity: iota (tag 38), slots (62), control (63), five-input XOR (64). -/
noncomputable def ColumnParity.setup {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 8) :=
  setupTable ColumnParity.columnParitySetup 8 "Airbender.KeccakColumnParity"

/-- Theta+rho: byte XOR (4), XOR-and-split (58), control (59), slots (60). -/
noncomputable def ThetaRho.setup {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 9) :=
  setupTable ThetaRho.thetaRhoSetup 9 "Airbender.KeccakThetaRho"

/-- Chi: the chi table (65) and control (66). -/
noncomputable def Chi5.setup {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 11) :=
  setupTable Chi5.chi5Setup 11 "Airbender.KeccakChi5"

end Airbender.Keccak.Split
