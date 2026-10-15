import Slop.RV.MulAdd.Block

/-! Prints the value DAG of a block's symbolic run (`sym_block`), for `gen/clusters.py`:
`<id> var i | const w | op o a b | mop o a b x | load n sg b off`, then `write base off n src`. -/

open RV RV.Sym

def opName : Op → String
  | .add => "add" | .sub => "sub" | .sll => "sll" | .slt => "slt" | .sltu => "sltu" | .xor => "xor"
  | .srl => "srl" | .sra => "sra" | .or => "or" | .and => "and" | .mul => "mul" | .mulhu => "mulhu"
  | .divu => "divu" | .remu => "remu"

def fopName : FieldOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .fma => "fma" | .triAdd => "triadd"

def dumpDag (σ : SState) : IO Unit := do
  for i in [0:σ.pool.len] do
    IO.println <| s!"{i} " ++ match nodeAt σ.pool i with
      | .var j => s!"var {j}"
      | .const w => s!"const {w.toNat}"
      | .op o a b => s!"op {opName o} {a} {b}"
      | .mop o a b x => s!"mop {fopName o} {a} {b} {x}"
      | .load n sg b k => s!"load {n} {sg} {b} {k.toNat}"
  for w in σ.writes do
    IO.println s!"write {w.base} {w.off.toNat} {w.n} {w.src.val}"

def main (args : List String) : IO Unit :=
  match args with
  | ["MulAdd"] => dumpDag MulAdd.σ
  | _ => throw (IO.userError "usage: Dag <block>")


