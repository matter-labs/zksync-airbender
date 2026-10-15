#!/usr/bin/env python3
"""Cut a block's value DAG at the results of its field operations and write the proof files.

Input: the DAG printed by `gen/Dag.lean` (stdin). The block's model (the op sequence of `rust/src/bb.rs`, below) is
evaluated next to the DAG on random inputs; a DAG node whose value always equals a model value is a cut point
("canonical" node), and so is each raw Montgomery product `T` (structural: `add` with a `sltu`-of-`mul` operand).
Nothing here is trusted: the files only state lemmas, which Lean then proves (`mm_cluster`, `mm1_cluster`,
`lin_cluster`) or rejects.

usage: clusters.py BLOCK OUTDIR < dag.txt   (BLOCK: MulAdd, PolyA, PolyB)
"""
import random
import sys

P = 0x78000001
K = 0x77ffffff
M32 = (1 << 32) - 1
RINV = pow(1 << 32, P - 2, P)
NR = 939524073   # new_ct(11): 11 in Montgomery form
R2 = 1172168163  # MONT_R2


def mm(a, b):
    return a * b * RINV % P


# ---------------------------------------------------------------- the DAG

def parse(lines):
    nodes = []
    for ln in lines:
        t = ln.split()
        if t and t[0] != "write":
            assert int(t[0]) == len(nodes)
            nodes.append(t[1:])
    return nodes


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


# ---------------------------------------------------------------- models

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
    inputs = [(r, 4 * j) for r in (10, 11, 12) for j in range(4)]  # acc = a0, x = a1, c = a2

    def final(o, ld, V, val):
        stmt = (f"e4 {' '.join(val(i) for i in o)} = e4 {' '.join(val(ld[j]) for j in range(4))} * "
                f"e4 {' '.join(val(ld[j]) for j in range(4, 8))} + e4 {' '.join(val(ld[j]) for j in range(8, 12))}")
        tac = ("  simp only [e4]\n  rw [Spec.ofLimbs_mul, Spec.ofLimbs_add]\n" +
               "".join(f"  generalize mont {val(ld[j])} = x{j} at *\n" for j in range(12)) +
               "  simp only [{M}, mont_nonres]\n  refine ofLimbs_congr ?_ ?_ ?_ ?_ <;> ring")
        return [stmt], tac
    return m, outs, inputs, {}, final


def model_poly_a():
    """`ext4_poly`, before the call: `yy = new(y)`, limb by limb (y at a1)."""
    m = Model()
    y = [m.ld(f"y{i}", i) for i in range(4)]
    r2 = m.const("R2", R2)
    outs = [m.mul(f"yy{i}", y[i], r2) for i in range(4)]
    inputs = [(11, 4 * j) for j in range(4)]

    def final(o, ld, V, val):
        return ([f"mont {val(o[i])} = ({V(ld[i])} : F)" for i in range(4)],
                "  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [{M}, new_F]")
    return m, outs, inputs, {}, final


def model_poly_b():
    """`ext4_poly`, after the call: `to_u32` of the result `e` (at sp + 20), limb by limb; `s2..s4` hold `p - 1`,
    `p`, `K` from before the call."""
    m = Model()
    e = [m.ld(f"e{i}", i) for i in range(4)]
    one = m.const("1", 1)
    outs = [m.mul(f"out{i}", e[i], one) for i in range(4)]
    inputs = [(2, 20 + 4 * j) for j in range(4)]

    def final(o, ld, V, val):
        return ([f"({V(o[i])} : F) = mont {val(ld[i])}" for i in range(4)],
                "  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [{M}]")
    return m, outs, inputs, {18: P - 1, 19: P, 20: K}, final


MODELS = {"MulAdd": model_mul_add, "PolyA": model_poly_a, "PolyB": model_poly_b}
DIRS = {"MulAdd": ("MulAdd", ""), "PolyA": ("Ext4Poly", "A"), "PolyB": ("Ext4Poly", "B")}
DOCS = {"MulAdd": "The four stored limbs: canonical, and `acc · x + c` in `F[w]/(w⁴ - 11)`.",
        "PolyA": "The four limbs of `yy`: canonical, and `y` in Montgomery form.",
        "PolyB": "The four results: canonical, and the values of `e`'s limbs (`to_u32`)."}


# ---------------------------------------------------------------- matching

def analyse(nodes, model, inputs, env, samples=40):
    rnd = random.Random(1)
    bases = sorted({r for r, _ in inputs})
    base_addr = {r: 0x1200000 + 0x100 * i for i, r in enumerate(bases)}
    runs = []
    for s in range(samples):
        edge = [0, 1, P - 1, P - 2]
        vals = [rnd.choice(edge) if s < 4 and rnd.random() < 0.5 else rnd.randrange(P) for _ in inputs]
        regs = {i: rnd.randrange(1 << 32) for i in range(32)}
        regs[0] = 0
        regs.update(env)
        mem = {}
        for r in bases:
            regs[r] = base_addr[r]
        for (r, off), v in zip(inputs, vals):
            mem[base_addr[r] + off] = v
        runs.append((evaluate(nodes, regs, mem), model.run(vals)))
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
        if op == "mul":
            for t in tnodes:
                if all(dv[t] % P == mv[k] and dv[t] < 2 * P for dv, mv in runs):
                    traw[k] = t
                    break
    return canon, traw


def const_val(nodes, env, j):
    x = nodes[j]
    if x[0] == "const": return int(x[1])
    if x[0] == "var" and int(x[1]) in env: return env[int(x[1])]
    return None


def raw_operands(nodes, env, t):
    """`(x, y)` of `mulhu x y` in raw node `t` (the product, not the one by `p`); `(x, None)` for a product by 1."""
    a, b = int(nodes[t][2]), int(nodes[t][3])
    s, cy = (a, b) if nodes[b][1] == "sltu" else (b, a)
    for u in ([int(nodes[s][2]), int(nodes[s][3])] if nodes[s][1] == "add" else []):
        x = nodes[u]
        if x[0] == "op" and x[1] == "mulhu":
            l, r = int(x[2]), int(x[3])
            if P not in (const_val(nodes, env, l), const_val(nodes, env, r)):
                return l, r
    # product by 1: `T = mulhu(m, p) + carry(x + mp)`, `x` the first summand of the carry's sum
    sm = int(nodes[cy][2])
    return int(nodes[sm][2]), None


# ---------------------------------------------------------------- Lean output

def V(i): return f"V[{i}]"


def gen(name, nodes, outdir):
    model, outs, inputs, env, final = MODELS[name]()
    d, pre = DIRS[name]
    canon, traw = analyse(nodes, model, inputs, env)
    steps = model.steps
    for o in outs:
        assert o in canon, f"output {steps[o][0]} not found"
    for k, (nm, op, _, _) in enumerate(steps):
        if op == "mul":
            assert k in traw or k in canon, f"{nm}: no node"
    used_t = sorted(set(traw.values()))
    cuts = sorted(set(canon.values()) | set(used_t))
    tinfo = {t: raw_operands(nodes, env, t) for t in used_t}

    def val(i): return f"({name}.σ.pool.val c {i})"

    def tbound(t): return "≤" if tinfo[t][1] is None else "<"

    def hyp(i, kind):
        if kind == 1: return f"(h{i} : {V(i)} < BabyBearP)"
        return f"(h{i} : {V(i)} {tbound(i)} {'' if tbound(i) == '≤' else '2 * '}BabyBearP)"

    def atom(k):
        """(Nat term, F term, bounds) of model value `k` in terms of cut nodes."""
        nm, op, args, extra = steps[k]
        if k in canon and op != "const":
            i = canon[k]
            return V(i), f"mont {val(i)}", {(i, 1)}
        if op == "mul" and k in traw:
            t = traw[k]
            return f"{V(t)} % BabyBearP", f"((({V(t)} : Nat) : F) * (RINV : F))", {(t, 2)}
        if op in ("add", "sub"):
            (na, fa, ba), (nb, fb, bb) = atom(args[0]), atom(args[1])
            f = "amN" if op == "add" else "smN"
            sgn = "+" if op == "add" else "-"
            return f"{f} ({na}) ({nb})", f"({fa} {sgn} {fb})", ba | bb
        raise ValueError(nm)

    envh = " ".join(f"(e{r} : c.env {r} = {w}#32)" for r, w in sorted(env.items()))
    sp = lambda *xs: " ".join(x for x in xs if x)
    envs = ", ".join(f"e{r}" for r in sorted(env))
    envpre = f"  try simp only [{envs}]\n" if env else ""
    envargs = " ".join(f"e{r}" for r in sorted(env))
    mod = f"Slop.RV.{d}"
    header = f"""import {{IMPORTS}}

/-! GENERATED by lean/gen/clusters.sh from the DAG of `{name}` and the op sequence of `rust/src/bb.rs` — do not
edit. -/

namespace RV.{name}
open _root_.RV.Sym Spec
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option hygiene false in
local notation "V[" i "]" => BitVec.toNat (Pool.val c {name}.σ.pool i)
"""

    def hdr(imports): return header.replace("{IMPORTS}", "\nimport ".join(imports))

    raw = [hdr([f"{mod}.Block", "Slop.RV.BBPlain"]),
           f"/-- The cut points: values of field operations, and raw Montgomery products. -/\n"
           f"def cuts : List Nat := {cuts}\n"]
    for t in used_t:
        x, y = tinfo[t]
        if y is None:
            raw.append(f"""
theorem t{t} {sp("(c : Ctx)", envh)} :
    {V(t)} ≤ BabyBearP ∧ {V(t)} % BabyBearP = {V(x)} * RINV % BabyBearP := by
  sym_unfold using cuts.erase {t}
{envpre}  mm1_cluster
""")
            continue
        xc, yc = const_val(nodes, env, x), const_val(nodes, env, y)
        xs = f"(BitVec.toNat ({xc}#32 : Word))" if xc is not None else V(x)
        ys = f"(BitVec.toNat ({yc}#32 : Word))" if yc is not None else V(y)
        hy = "" if yc is not None else hyp(y, 1)
        raw.append(f"""
theorem t{t} {sp("(c : Ctx)", envh, hy)} :
    {V(t)} < 2 * BabyBearP ∧ {V(t)} % BabyBearP = {xs} * {ys} * RINV % BabyBearP := by
  sym_unfold using cuts.erase {t}
{envpre}  mm_cluster
""")
    raw.append(f"\nend RV.{name}\n")

    lemmas = []
    for k, (nm, op, args, _) in enumerate(steps):
        if k not in canon or op in ("ld", "const"):
            continue
        i = canon[k]
        if op == "mul":
            t = traw[k]
            rhs, bounds, frhs = f"{V(t)} % BabyBearP", {(t, 2)}, f"((({V(t)} : Nat) : F) * (RINV : F))"
        else:
            (na, fa, ba), (nb, fb, bb) = atom(args[0]), atom(args[1])
            f = "amN" if op == "add" else "smN"
            rhs, bounds = f"{f} ({na}) ({nb})", ba | bb
            frhs = f"({fa} {'+' if op == 'add' else '-'} {fb})"
        hs = " ".join(hyp(j, kd) for j, kd in sorted(bounds))
        lemmas.append((i, nm, rhs, frhs, sorted(bounds), f"""
/-- `{nm}` -/
theorem n{i} {sp("(c : Ctx)", envh, hs)} :
    {V(i)} = {rhs} := by
  sym_unfold using cuts.erase {i}
{envpre}  lin_cluster
"""))
    lemmas.sort()
    chunks = [lemmas[i:i + 18] for i in range(0, len(lemmas), 18)] or [[]]
    files = {f"{pre}Raw.lean": "".join(raw)}
    node_mods = []
    for j, chunk in enumerate(chunks):
        fn = f"{pre}Nodes{j + 1}"
        node_mods.append(f"{mod}.{fn}")
        files[fn + ".lean"] = hdr([f"{mod}.{pre}Raw"]) + "".join(x[-1] for x in chunk) + f"\nend RV.{name}\n"

    # the assembly
    loads = {steps[k][3]: canon[k] for k in canon if steps[k][1] == "ld"}
    nin = len(inputs)
    lh = " ".join(hyp(loads[j], 1) for j in range(nin))
    body = []
    order = sorted([(i, "n") for (i, *_r) in lemmas] + [(t, "t") for t in used_t])
    for i, kind in order:
        if kind == "t":
            x, y = tinfo[i]
            yarg = "" if y is None or const_val(nodes, env, y) is not None else f" h{y}"
            body.append(f"  have t{i} := {sp(f't{i} c', envargs, yarg.strip())}\n  have h{i} := t{i}.1")
        else:
            (_, _, rhs, _, bounds, _) = next(x for x in lemmas if x[0] == i)
            args = " ".join(f"h{j}" for j, _ in bounds)
            lt = "amN_lt _ _" if rhs.startswith("amN") else "smN_lt _ _" if rhs.startswith("smN") else "mod_p_lt _"
            body.append(f"  have n{i} := {sp(f'n{i} c', envargs, args)}\n"
                        f"  have h{i} : {V(i)} < BabyBearP := (n{i}).trans_lt ({lt})")
    fl, mnames = [], []
    for i, kind in order:
        if kind == "t":
            x, y = tinfo[i]
            if y is None:
                fl.append(f"  have m{i} : (({V(i)} : Nat) : F) = mont {val(x)} := mm1_F t{i}.2")
            else:
                xw = f"({const_val(nodes, env, x)}#32 : Word)" if const_val(nodes, env, x) is not None else val(x)
                yw = f"({const_val(nodes, env, y)}#32 : Word)" if const_val(nodes, env, y) is not None else val(y)
                fl.append(f"  have m{i} : ((({V(i)} : Nat) : F) * (RINV : F)) = mont {xw} * mont {yw} := mm_F t{i}.2")
        else:
            (_, _, rhs, frhs, bounds, _) = next(x for x in lemmas if x[0] == i)
            fl.append(f"  have m{i} : mont {val(i)} = {frhs} := by\n"
                      f"    simp only [mont]; rw [n{i}]\n"
                      f"    simp (disch := first | omega | exact (mod_p_lt _).le | exact (amN_lt _ _).le | exact (smN_lt _ _).le) only\n"
                      f"      [amN_cast, smN_cast, modp_cast]\n"
                      f"    all_goals ring")
        mnames.append(f"m{i}")
    o = [canon[x] for x in outs]
    fstmts, ftac = final(o, loads, V, val)
    if name == "PolyB":  # the results are plain values: `(V[o] : F)`, from the node lemma and `T ≡ x · 2^-32`
        fl = [f"  have v{i} : (({V(i)} : Nat) : F) = mont {val(tinfo[traw[k]][0])} := by\n"
              f"    rw [n{i}, modp_cast]; exact mm1_F t{traw[k]}.2"
              for k in outs for i in [canon[k]]]
        mnames = [f"v{canon[k]}" for k in outs]
    values = hdr(node_mods) + f"""
/-- {DOCS[name]} -/
theorem values {sp("(c : Ctx)", envh, lh)} :
    {" ∧ ".join(f"{V(i)} < BabyBearP" for i in o)} ∧
    {" ∧ ".join(fstmts)} := by
{chr(10).join(body)}
  refine ⟨{", ".join(f"h{i}" for i in o)}, ?_⟩
{chr(10).join(fl)}
  clear * - {" ".join(mnames)}
{ftac.replace("{M}", ", ".join(mnames))}

end RV.{name}
"""
    files[f"{pre}Values.lean"] = values
    for fn, txt in files.items():
        with open(f"{outdir}/{fn}", "w") as f:
            f.write(txt)
    print(f"{name}: {len(cuts)} cuts ({len(used_t)} raw), {len(lemmas)} node lemmas, files {sorted(files)}",
          file=sys.stderr)


if __name__ == "__main__":
    name, outdir = sys.argv[1], sys.argv[2]
    gen(name, parse(sys.stdin.read().splitlines()), outdir)
