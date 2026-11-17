module
public import Human.Helpers.Tables.Lookups
public import Human.Circuits.JumpBranchSlt.Tables.Control

public import Human.Compiler.NativeSetups.Bigint

@[expose] public section

namespace Airbender.Bigint

/-- Native fixed rows: the six tagged regions. `SetupImportClaim` makes them equal to the imported native rows. -/
def setupRow (index : Fin 1390592) : Nat × Nat × Nat :=
  let n := index.val
  if n < 262144 then (n / 512, n % 512, 22)
  else if n < 1310720 then ((n - 262144) / 1024, (n - 262144) % 1024, 23)
  else if n < 1312768 then (n - 1310720, 0, 24)
  else if n < 1316864 then (n - 1312768, 0, 25)
  else if n < 1325056 then (n - 1316864, 0, 26)
  else (n - 1325056, (n - 1325056) % 256, 41)

def setupTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.Bigint"
  length := 1390592
  row i := #v[((setupRow i).1 : ZMod p), ((setupRow i).2.1 : ZMod p), ((setupRow i).2.2 : ZMod p)]
  index x := match x[2].val with
    | 22 => x[0].val * 512 + x[1].val
    | 23 => 262144 + x[0].val * 1024 + x[1].val
    | 24 => 1310720 + x[0].val
    | 25 => 1312768 + x[0].val
    | 26 => 1316864 + x[0].val
    | 41 => 1325056 + x[0].val
    | _ => 0
  Spec x := ∃ i : Fin 1390592, x = #v[((setupRow i).1 : ZMod p), ((setupRow i).2.1 : ZMod p), ((setupRow i).2.2 : ZMod p)]
  contains_iff _ := Iff.rfl
}

/-- The fixed rows, then zero padding, are the imported native rows on the complete trace domain. -/
def SetupImportClaim : Prop :=
  Compiler.NativeSetups.bigintSetup.traceLen = 4194304 ∧
  Compiler.NativeSetups.bigintSetup.Rows fun index =>
    if bound : index < 1390592 then
      let row := setupRow ⟨index, bound⟩
      #v[(row.1 : Int), (row.2.1 : Int), (row.2.2 : Int)]
    else #v[0, 0, 0]

end Airbender.Bigint
