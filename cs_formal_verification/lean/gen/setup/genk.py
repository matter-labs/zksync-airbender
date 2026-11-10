import sys,re
import os
P=os.path.dirname(os.path.abspath(__file__))+"/"
L=os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../slop/Slop/KeccakSplit/Setup/")
fams={
 "theta":dict(dir="ThetaRho",ns="ThetaRho",setup="thetaRhoSetup",ncol=9,
   helpers="callAt, ctl, slt, flag, splitA, splitB, splitS, callIndex"),
 "parity":dict(dir="ColumnParity",ns="ColumnParity",setup="columnParitySetup",ncol=8,
   helpers="nib, callAt, callIndex, Nat.reducePow, pow_zero, Nat.div_one"),
 "chi":dict(dir="Chi5",ns="Chi5",setup="chi5Setup",ncol=11,
   helpers="nib, chiOut, callAt, ctl, callIndex, Nat.reducePow, pow_zero, Nat.div_one"),
}
fam=sys.argv[1]; F=fams[fam]
cols={}; table=None
for line in open(P+"struct.txt"):
    f=line.split(None,4)
    if f[0]!=fam: continue
    c=int(f[1]); s=int(f[2]); rest=f[3]+" "+f[4].strip()
    m=re.search(r"TABLE\[([^\]]*)\]",rest)
    if m: table=m.group(1); rest=rest.replace(m.group(0),"iotaTable")
    cols.setdefault(c,[]).append((s,rest))
ns=f"Airbender.Keccak.Split.{F['ns']}.SetupProofs"
# Shapes
sh=[f"import Slop.KeccakSplit.Setup.{F['dir']}.Spec\n\n/- Long blocks of each column, matched by shape (generated from the imported columns:\n   the import's grid blocks and the affine runs longer than 200 rows). -/\n\nnamespace {ns}\n\nopen Airbender.Import.Setup Airbender.Import.Setup.Proofs\n\nset_option warningAsError true\n"]
if table:
    sh.append(f"\n/-- The iota table's per-byte constants, as the import emitted them. -/\ndef iotaTable : Array Nat :=\n  #[{table}]\n")
nlong={}
for c in range(F['ncol']):
    items=[]
    for s,rest in cols[c]:
        k=rest.split()
        if k[0]=="G":
            items.append(f"({s}, .grid {k[1]} {rest.split(None,2)[2]})")
        elif k[0]=="A" and int(k[1])>200:
            items.append(f"({s}, .affine {k[1]} {k[2]} {k[3]})")
    nlong[c]=len(items)
    sh.append(f"\nabbrev col{c}Spec (n : Nat) : Int := Int.ofNat (spec{c} n)\n\ndef col{c}Longs : List (Nat × Shape) :=\n  [" + ",\n    ".join(items)+"]\n")
sh.append(f"\nend {ns}\n")
open(L+F['dir']+"/Shapes.lean","w").write("".join(sh))
# ShapesOk
ok=[f"import Slop.KeccakSplit.Setup.{F['dir']}.Shapes\n\n/- Agreement of every listed long block with its row formula, by formula: grid blocks by\n   their digits (`digits_eq`), affine runs by `omega`. -/\n\nnamespace {ns}\n\nopen Airbender.Import.Setup Airbender.Import.Setup.Proofs Airbender.Keccak.Split.SetupProofs\n\nset_option warningAsError true\n-- generated (gen/setup/genk.py): every block gets the same simp set, which a block need not use in full\nset_option linter.unusedSimpArgs false\n"]
if table:
    ok.append("\ntheorem iotaTable_eq : ∀ b < 256, iotaTable.getD b 0 = rcByte b := by decide +kernel\n")
for c in range(F['ncol']):
    pats=" | ".join(["rfl"]*nlong[c])
    extra = "\n    try rw [iotaTable_eq _ (by omega)]" if (table and c==2) else ""
    ok.append(f'''
theorem col{c}_longs : ∀ p ∈ col{c}Longs, p.2.Ok col{c}Spec p.1 := by
  intro p hp
  simp only [col{c}Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with {pats}
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col{c}Spec, spec{c}, {F['helpers']}, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]{extra}
    split_ifs <;> digits_eq
''')
ok.append(f"\nend {ns}\n")
open(L+F['dir']+"/ShapesOk.lean","w").write("".join(ok))
# Rows
rows=[f"""import Slop.KeccakSplit.Setup.{F['dir']}.ShapesOk
import Slop.KeccakSplit.Setup.{F['dir']}.Formula
import Human.Circuits.KeccakSplit.Tables.Setup
import Mathlib.Tactic.IntervalCases

/- Row meaning of the imported setup: every column decodes to its row formula on all 2^22
   exported rows. Each column is a few blocks: grid blocks and long affine runs matched by
   shape (`Shapes`, proved in `ShapesOk`), the controller rows checked row by row (`scan`). -/

namespace {ns}
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option warningAsError true
"""]
for c in range(F['ncol']):
    rows.append(f"""
theorem col{c}_rows : ∀ n < 4194304, decode {F['setup']}_col{c} n = col{c}Spec n :=
  rows_of_scan _ col{c}_longs (by decide +kernel) (by decide +kernel)
""")
rows.append(f"""
theorem traceLen_eq : {F['setup']}.traceLen = 4194304 := rfl

/-- Every exported row is the formula row. -/
theorem setupRow_eq (n : Nat) (hn : n < 4194304) :
    Airbender.Keccak.Split.setupRow {F['setup']} {F['ncol']} n = (formulaRow n).map Int.ofNat := by
  ext c hc
  simp only [Airbender.Keccak.Split.setupRow, Vector.getElem_ofFn, Vector.getElem_map, formulaRow]
  interval_cases c
""")
for c in range(F['ncol']):
    rows.append(f"  · exact col{c}_rows n hn\n")
rows.append(f"\nend {ns}\n")
open(L+F['dir']+"/Rows.lean","w").write("".join(rows))
