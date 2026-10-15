#!/usr/bin/env python3
"""Cut a block's value DAG at the results of its field operations and write the proof files.

Input: the DAG printed by `gen/Dag.lean` (stdin). The model below (the op sequence of `rust/src/bb.rs`) is evaluated
next to the DAG on random inputs; a DAG node whose value always equals a model value is a cut point ("canonical"
node), and so is each raw Montgomery product `T` (structural: `add` with a `sltu`-of-`mul` operand). Nothing here is
trusted: the files only state lemmas, which Lean then proves (`mm_cluster`, `lin_cluster`) or rejects.

usage: clusters.py MulAdd OUTDIR < dag.txt
"""
import random
import sys

P = 0x78000001
M32 = (1 << 32) - 1
RINV = pow(1 << 32, P - 2, P)
NR = 939524073  # new_ct(11): 11 in Montgomery form


def mm(a, b):
    return a * b * RINV % P


# ---------------------------------------------------------------- the DAG

def parse(lines):
    nodes, writes = [], []
    for ln in lines:
        t = ln.split()
        if not t:
            continue
        if t[0] == "write":
            writes.append(tuple(int(x) for x in t[1:]))
        else:
            assert int(t[0]) == len(nodes)
            nodes.append(t[1:])
    return nodes, writes


def alu(o, a, b):
    if o == "add": return (a + b) & M32
    if o == "sub": return (a - b) & M32
    if o == "sltu": return int(a < b)
    if o == "and": return a & b
    if o == "or": return a | b
    if o == "xor": return a ^ b
    if o == "mul": return (a * b) & M32
    if o == "mulhu": return (a * b) >> 32
    if o == "sll": return (a << (b & 31)) & M32
    if o == "srl": return a >> (b & 31)
    raise ValueError(o)


def evaluate(nodes, regs, mem):
    vs = []
    for n in nodes:
        k = n[0]
        if k == "var": v = regs.get(int(n[1]), 0)
        elif k == "const": v = int(n[1])
        elif k == "op": v = alu(n[1], vs[int(n[2])], vs[int(n[3])])
        elif k == "load":
            assert n[1] == "4"
            v = mem.get((vs[int(n[3])] + int(n[4])) & M32, 0)
        else: raise ValueError(n)
        vs.append(v)
    return vs


# ---------------------------------------------------------------- the model

class Model:
    def __init__(self):
        self.steps = []  # (name, op, args, extra)

    def _s(self, name, op, args, extra=None):
        self.steps.append((name, op, args, extra))
        return len(self.steps) - 1

    def ld(self, name, k): return self._s(name, "ld", [], k)
    def const(self, name, w): return self._s(name, "const", [], w)
    def add(self, name, a, b): return self._s(name, "add", [a, b])
    def sub(self, name, a, b): return self._s(name, "sub", [a, b])
    def mul(self, name, a, b): return self._s(name, "mul", [a, b])

    def run(self, inputs):
        v = []
        for (_, op, args, extra) in self.steps:
            if op == "ld": v.append(inputs[extra])
            elif op == "const": v.append(extra)
            elif op == "add": v.append((v[args[0]] + v[args[1]]) % P)
            elif op == "sub": v.append((v[args[0]] + P - v[args[1]]) % P)
            elif op == "mul": v.append(mm(v[args[0]], v[args[1]]))
        return v


def model_mul_add():
    """`ext4_mul_add(acc, x, c)`: acc ← acc·x + c, Ext4 tower Karatsuba (bb.rs, plain)."""
    m = Model()
    a = [m.ld(f"a{i}", i) for i in range(4)]
    b = [m.ld(f"b{i}", 4 + i) for i in range(4)]
    c = [m.ld(f"c{i}", 8 + i) for i in range(4)]
    nr = m.const("NR", NR)

    def e2mul(tag, x0, x1, y0, y1):
        v0 = m.mul(tag + ".v0", x0, y0)
        v1 = m.mul(tag + ".v1", x1, y1)
        sx = m.add(tag + ".sx", x1, x0)
        sy = m.add(tag + ".sy", y0, y1)
        p = m.mul(tag + ".p", sx, sy)
        q = m.sub(tag + ".q", p, v0)
        c1 = m.sub(tag + ".c1", q, v1)
        v1n = m.mul(tag + ".v1n", v1, nr)
        c0 = m.add(tag + ".c0", v0, v1n)
        return c0, c1

    v00, v01 = e2mul("V0", a[0], a[1], b[0], b[1])
    v10, v11 = e2mul("V1", a[2], a[3], b[2], b[3])
    s0 = m.add("s0", a[2], a[0]); s1 = m.add("s1", a[3], a[1])
    t0 = m.add("t0", b[0], b[2]); t1 = m.add("t1", b[1], b[3])
    m0, m1 = e2mul("M", s0, s1, t0, t1)
    d0 = m.sub("d0", m0, v00); d1 = m.sub("d1", m1, v01)
    f0 = m.sub("f0", d0, v10); f1 = m.sub("f1", d1, v11)
    nrv = m.mul("nr", v11, nr)
    g0 = m.add("g0", v00, nrv); g1 = m.add("g1", v01, v10)
    outs = [m.add("R0", g0, c[0]), m.add("R1", g1, c[1]), m.add("R2", f0, c[2]), m.add("R3", f1, c[3])]
    # registers: a0 = acc, a1 = x, a2 = c; inputs in that order
    return m, outs, {10: 0, 11: 4, 12: 8}


MODELS = {"MulAdd": model_mul_add}


# ---------------------------------------------------------------- matching

def analyse(nodes, model, bases, samples=40):
    rnd = random.Random(1)
    base_addr = {r: 0x1200000 + 0x100 * i for i, r in enumerate(sorted(bases))}
    runs = []
    for s in range(samples):
        # edge values too: 0, 1, p - 1
        pool = [0, 1, P - 1, P - 2] if s < 4 else None
        inputs = [rnd.choice(pool) if pool and rnd.random() < 0.5 else rnd.randrange(P) for _ in range(12)]
        regs = {i: rnd.randrange(1 << 32) for i in range(32)}
        regs[0] = 0
        regs[2] = 0x1100000
        mem = {}
        for r, first in bases.items():
            regs[r] = base_addr[r]
            for j in range(4):
                mem[base_addr[r] + 4 * j] = inputs[first + j]
        runs.append((evaluate(nodes, regs, mem), model.run(inputs)))
    n = len(nodes)

    def is_sltu_of_mul(j):
        x = nodes[j]
        return x[0] == "op" and x[1] == "sltu" and nodes[int(x[3])][0] == "op" and nodes[int(x[3])][1] == "mul"

    tnodes = [i for i in range(n) if nodes[i][0] == "op" and nodes[i][1] == "add"
              and (is_sltu_of_mul(int(nodes[i][2])) or is_sltu_of_mul(int(nodes[i][3])))]
    canon, traw = {}, {}
    for k, (name, op, _, _) in enumerate(model.steps):
        if op == "const":
            continue
        for i in range(n):
            if i in tnodes:
                continue
            if all(dv[i] == mv[k] for dv, mv in runs):
                if op != "ld" or nodes[i][0] == "load":
                    canon[k] = i
                    break
        if op == "mul" and k not in canon or op == "mul":
            for t in tnodes:
                if all(dv[t] % P == mv[k] and dv[t] < 2 * P for dv, mv in runs):
                    traw[k] = t
                    break
    return canon, traw, tnodes


def mul_operands(nodes, t):
    """The `mulhu x y` of the product in raw node `t` (not the one by `p`)."""
    a, b = int(nodes[t][2]), int(nodes[t][3])
    s = a if nodes[a][1] == "add" else b
    for u in (int(nodes[s][2]), int(nodes[s][3])):
        x = nodes[u]
        if x[0] == "op" and x[1] == "mulhu":
            l, r = int(x[2]), int(x[3])
            if not any(nodes[j] == ["const", str(P)] for j in (l, r)):
                return l, r
    raise ValueError(t)


# ---------------------------------------------------------------- Lean output

def V(i): return f"V[{i}]"


def gen(name, nodes, model, outs, bases, outdir):
    canon, traw, tnodes = analyse(nodes, model, bases)
    steps = model.steps
    for o in outs:
        assert o in canon, f"output {steps[o][0]} not found"
    for k, (nm, op, _, _) in enumerate(steps):
        if op == "mul":
            assert k in traw or k in canon, f"{nm}: no node"
    used_t = sorted(set(traw.values()))
    cuts = sorted(set(canon.values()) | set(used_t))
    const_node = {}
    for i, x in enumerate(nodes):
        if x[0] == "const":
            const_node[i] = int(x[1])

    def atom(k):
        """(Lean Nat term, F term, bounds) of model value `k` in terms of cut nodes."""
        nm, op, args, extra = steps[k]
        if k in canon and op != "const":
            i = canon[k]
            return V(i), f"mont (MulAdd.σ.pool.val c {i})", {(i, 1)}
        if op == "mul" and k in traw:
            t = traw[k]
            return f"{V(t)} % BabyBearP", f"((({V(t)} : Nat) : F) * (RINV : F))", {(t, 2)}
        if op in ("add", "sub"):
            (na, fa, ba), (nb, fb, bb) = atom(args[0]), atom(args[1])
            f = "amN" if op == "add" else "smN"
            sgn = "+" if op == "add" else "-"
            return f"{f} ({na}) ({nb})", f"({fa} {sgn} {fb})", ba | bb
        raise ValueError(nm)

    def hyp(i, kind):
        return f"(h{i} : {V(i)} < {'2 * ' if kind == 2 else ''}BabyBearP)"

    header = f"""import Slop.RV.MulAdd.Block
import Slop.RV.BBPlain

/-! GENERATED by lean/gen/clusters.sh from the DAG of `{name}` and the op sequence of `rust/src/bb.rs` — do not
edit. -/

namespace RV.{name}
open _root_.RV.Sym Spec
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option hygiene false in
local notation "V[" i "]" => BitVec.toNat (Pool.val c {name}.σ.pool i)
"""
    # raw Montgomery products
    raw = [header.replace("namespace RV", "namespace RV").rstrip() + "\n",
           f"/-- The cut points: values of field operations, and raw Montgomery products. -/\n"
           f"def cuts : List Nat := {cuts}\n"]
    tlem = {}
    for t in used_t:
        x, y = mul_operands(nodes, t)
        xs = f"(BitVec.toNat ({const_node[x]}#32 : Word))" if x in const_node else V(x)
        xw = f"({const_node[x]}#32 : Word)" if x in const_node else f"(MulAdd.σ.pool.val c {x})"
        assert y not in const_node
        tlem[t] = (x, y, xw)
        raw.append(f"""
theorem t{t} (c : Ctx) {hyp(y, 1)} :
    {V(t)} < 2 * BabyBearP ∧ {V(t)} % BabyBearP = {xs} * {V(y)} * RINV % BabyBearP := by
  sym_unfold using cuts.erase {t}
  mm_cluster
""")
    raw.append(f"\nend RV.{name}\n")

    # canonical nodes
    canon_lem = []
    for k, (nm, op, args, _) in enumerate(steps):
        if k not in canon or op in ("ld", "const"):
            continue
        i = canon[k]
        if op == "mul":
            t = traw[k]
            rhs, bounds = f"{V(t)} % BabyBearP", {(t, 2)}
            frhs = f"((({V(t)} : Nat) : F) * (RINV : F))"
        else:
            (na, fa, ba), (nb, fb, bb) = atom(args[0]), atom(args[1])
            f = "amN" if op == "add" else "smN"
            rhs, bounds = f"{f} ({na}) ({nb})", ba | bb
            frhs = f"({fa} {'+' if op == 'add' else '-'} {fb})"
        hs = " ".join(hyp(j, kd) for j, kd in sorted(bounds))
        canon_lem.append((i, nm, rhs, frhs, sorted(bounds), f"""
/-- `{nm}` -/
theorem n{i} (c : Ctx) {hs} :
    {V(i)} = {rhs} := by
  sym_unfold using cuts.erase {i}
  lin_cluster
"""))
    canon_lem.sort()
    half = (len(canon_lem) + 1) // 2
    files = {"Raw.lean": "".join(raw)}
    for part, chunk in (("Nodes1.lean", canon_lem[:half]), ("Nodes2.lean", canon_lem[half:])):
        files[part] = header.replace("import Slop.RV.MulAdd.Block\n", "import Slop.RV.MulAdd.Raw\n") + \
            "".join(x[-1] for x in chunk) + f"\nend RV.{name}\n"

    # the assembly
    loads = {steps[k][3]: canon[k] for k in canon if steps[k][1] == "ld"}
    lh = " ".join(hyp(loads[j], 1) for j in range(12))
    ow = [f"(MulAdd.σ.pool.val c {canon[o]})" for o in outs]
    lw = [f"(MulAdd.σ.pool.val c {loads[j]})" for j in range(12)]
    body = []
    order = sorted([(i, "n") for (i, *_r) in canon_lem] + [(t, "t") for t in used_t])
    for i, kind in order:
        if kind == "t":
            x, y, xw = tlem[i]
            body.append(f"  have t{i} := t{i} c h{y}\n  have h{i} := t{i}.1")
        else:
            (_, _, rhs, _, bounds, _) = next(x for x in canon_lem if x[0] == i)
            args = " ".join(f"h{j}" for j, _ in bounds)
            lt = "amN_lt _ _" if rhs.startswith("amN") else "smN_lt _ _" if rhs.startswith("smN") else "mod_p_lt _"
            body.append(f"  have n{i} := n{i} c {args}\n"
                        f"  have h{i} : {V(i)} < BabyBearP := (n{i}).trans_lt ({lt})")
    fl = []
    for i, kind in order:
        if kind == "t":
            x, y, xw = tlem[i]
            fl.append(f"  have m{i} : ((({V(i)} : Nat) : F) * (RINV : F)) = mont {xw} * mont (MulAdd.σ.pool.val c {y}) := mm_F t{i}.2")
        else:
            (_, _, rhs, frhs, bounds, _) = next(x for x in canon_lem if x[0] == i)
            fl.append(f"  have m{i} : mont (MulAdd.σ.pool.val c {i}) = {frhs} := by\n"
                      f"    simp only [mont]; rw [n{i}]\n"
                      f"    simp (disch := first | omega | exact (mod_p_lt _).le | exact (amN_lt _ _).le | exact (smN_lt _ _).le) only\n"
                      f"      [amN_cast, smN_cast, modp_cast]\n"
                      f"    all_goals ring")
    names = ", ".join(f"m{i}" for i, _ in order)
    values = header.replace("import Slop.RV.MulAdd.Block\n", "import Slop.RV.MulAdd.Nodes1\nimport Slop.RV.MulAdd.Nodes2\n") + f"""
/-- The four stored limbs: canonical, and `acc · x + c` in `F[w]/(w⁴ - 11)`. -/
theorem values (c : Ctx) {lh} :
    {" ∧ ".join(f"{V(canon[o])} < BabyBearP" for o in outs)} ∧
    e4 {" ".join(ow)} = e4 {" ".join(lw[0:4])} * e4 {" ".join(lw[4:8])} + e4 {" ".join(lw[8:12])} := by
{chr(10).join(body)}
  refine ⟨{", ".join(f"h{canon[o]}" for o in outs)}, ?_⟩
{chr(10).join(fl)}
  clear * - {names.replace(",", "")}
  simp only [e4]
  rw [Spec.ofLimbs_mul, Spec.ofLimbs_add]
{chr(10).join(f"  generalize mont (MulAdd.σ.pool.val c {loads[j]}) = x{j} at *" for j in range(12))}
  simp only [{names}, mont_nonres]
  refine ofLimbs_congr ?_ ?_ ?_ ?_ <;> ring

end RV.{name}
"""
    files["Values.lean"] = values
    for fn, txt in files.items():
        with open(f"{outdir}/{fn}", "w") as f:
            f.write(txt)
    print(f"{name}: {len(cuts)} cuts ({len(used_t)} raw), {len(canon_lem)} node lemmas", file=sys.stderr)


if __name__ == "__main__":
    name, outdir = sys.argv[1], sys.argv[2]
    nodes, writes = parse(sys.stdin.read().splitlines())
    m, outs, bases = MODELS[name]()
    gen(name, nodes, m, outs, bases, outdir)
