module
public import Human.Circuits.Blake2G.Tables.Setup
public import Human.Circuits.Blake2Round.SetupArtifact

@[expose] public section

namespace Airbender.Blake2Round

/- Native fixed tables of the extended-control round, as exported from the Rust
   setup (`artifacts/setup/blake-round.json`, provenance in its README), not a
   hand-written model. Rows 0..606207 hold the six regions in table-offset order:
   XOR-8 (tag 4), XOR-7 (19), XOR-9 (20), XOR-8 with carry (55), XOR-7 with carry (56)
   and the split XOR (4+3)x(4+3) (57). The table keeps every exported row up to the
   trace length, padding included; each imported query fixes its tag column to one
   of the six tags (`Circuit.blakeRoundQueries`). -/

/-- Row `i` of the exported setup: each of the six columns decoded from its blocks
    (kernel data, no compiled code). -/
noncomputable def setupRow (i : Nat) : Vector Int 6 :=
  Vector.ofFn fun c => Import.Setup.decode (blake2RoundSetup.columns.getD c.val []) i

noncomputable def setupTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 6) := .fromStatic {
  name := "Airbender.Blake2Round"
  length := blake2RoundSetup.traceLen
  row i := (setupRow i.val).map (fun (v : Int) => (v : ZMod p))
  index x := match x[5].val with
    | 4 => x[0].val * 256 + x[1].val
    | 19 => 65536 + x[0].val * 128 + x[1].val
    | 20 => 81920 + x[0].val * 512 + x[1].val
    | 55 => 344064 + x[2].val * 65536 + x[0].val * 256 + x[1].val
    | 56 => 540672 + x[2].val * 16384 + x[0].val * 128 + x[1].val
    | 57 => 589824 + x[0].val * 1024 + x[1].val * 128 + x[2].val * 8 + x[3].val
    | _ => 0
  Spec x := ∃ i : Fin blake2RoundSetup.traceLen,
    x = (setupRow i.val).map (fun (v : Int) => (v : ZMod p))
  contains_iff _ := Iff.rfl
}

end Airbender.Blake2Round
