import Slop.Sym.Expr

/-! # Symbolic execution of straight-line code

`symRun` runs a list of (non-control-flow) instructions on a symbolic state: registers hold node ids (with an
address form `base + offset`), memory is the initial memory plus a list of symbolic writes, and the facts the
concrete run needs (alignment, ranges, disjointness of accesses through different base pointers) are collected
as side conditions. `Exec.lean` proves it sound (`run_block`): if it succeeds and the side conditions hold, the
concrete machine runs the same code to the corresponding state. -/

namespace RV.Sym

/-- A register: its value's node id, an address form `value = base + off`, and its value if known to be a
constant (folded at once, so that the constants the compiler builds with `lui`/`addi` become single nodes). -/
structure SReg where
  val : Nat
  base : Nat
  off : Word
  cst : Option Word
deriving DecidableEq, Repr

/-- A store: `n` bytes of `src.val` at `base + off`. -/
structure SWrite where
  base : Nat
  off : Word
  n : Nat
  src : SReg
deriving DecidableEq, Repr

/-- Side conditions of a run (addresses `base + off`). -/
inductive SCond
  | aligned (b : Nat) (k : Word) (n : Nat)
  | readable (b : Nat) (k : Word) (n : Nat)
  | writable (b : Nat) (k : Word) (n : Nat)
  /-- the `n₁` bytes at `b₁ + k₁` and the `n₂` bytes at `b₂ + k₂` do not overlap (and do not wrap around) -/
  | disj (b₁ : Nat) (k₁ : Word) (n₁ : Nat) (b₂ : Nat) (k₂ : Word) (n₂ : Nat)
deriving DecidableEq, Repr

structure SState where
  pool : Pool
  regs : List SReg
  writes : List SWrite
  conds : List SCond

def SState.reg (σ : SState) (r : Reg) : SReg := σ.regs.getD r.toNat ⟨0, 0, 0, none⟩

def SState.setReg (σ : SState) (r : Reg) (x : SReg) : SState :=
  if r = 0 then σ else { σ with regs := σ.regs.set r.toNat x }

/-- Two accesses at constant offsets from the same base do not overlap (as in `read_write_off`). -/
def disjOff (k₁ : Word) (n₁ : Nat) (k₂ : Word) (n₂ : Nat) : Bool :=
  decide (n₁ ≤ (k₂ - k₁).toNat ∧ n₂ ≤ (k₁ - k₂).toNat)

/-- A load of `n` bytes at `b + k` against the pending writes (newest first): the stored register if a write
at the same place and size (`n = 4`) is found, `none` (read the initial memory) if all are disjoint; side
conditions for writes through other bases. Fails (`some none` is "initial memory") on partial overlaps. -/
def resolve (b : Nat) (k : Word) (n : Nat) : List SWrite → List SCond → Option (Option SReg × List SCond)
  | [], cs => some (none, cs)
  | w :: ws, cs =>
    if w.base = b then
      if w.off = k ∧ w.n = n ∧ n = 4 then some (some w.src, cs)
      else if disjOff k n w.off w.n then resolve b k n ws cs
      else none
    else resolve b k n ws (.disj b k n w.base w.off w.n :: cs)

def commutes : Op → Bool
  | .add | .xor | .or | .and | .mul | .mulhu => true
  | _ => false

/-- A new value node (with commutative arguments in a canonical order). -/
def SState.add (σ : SState) (n : Node) : Option (SState × Nat) := do
  let (p, i) ← σ.pool.node n
  return ({ σ with pool := p }, i)

def opNode (o : Op) (a b : Nat) : Node := if commutes o ∧ b < a then .op o b a else .op o a b

/-- A constant register. -/
def SState.cst (σ : SState) (w : Word) : Option (SState × SReg) := do
  let (σ, v) ← σ.add (.const w)
  return (σ, ⟨v, v, 0, some w⟩)

/-- `mopVal` reads the old `rd` only for `fma` and `triAdd`; otherwise that operand is canonically node 0. -/
def mopUsesRd : FieldOp → Bool
  | .fma | .triAdd => true
  | _ => false

def symStep (σ : SState) : Instr → Option SState
  | .lui rd imm => do
    let (σ, x) ← σ.cst imm
    return σ.setReg rd x
  | .opImm o rd rs1 imm => do
    let r := σ.reg rs1
    match r.cst with
    | some a =>
      let (σ, x) ← σ.cst (alu o a imm)
      return σ.setReg rd x
    | none =>
      match o with
      | .add =>
        -- `addi` keeps `rs1`'s base: `base + (off + imm)`, the base itself at offset 0 (so `sp` comes back)
        if r.off + imm = 0 then return σ.setReg rd ⟨r.base, r.base, 0, none⟩
        let (σ, c) ← σ.add (.const (r.off + imm))
        let (σ, v) ← σ.add (.op .add r.base c)
        return σ.setReg rd ⟨v, r.base, r.off + imm, none⟩
      | o =>
        let (σ, c) ← σ.add (.const imm)
        let (σ, v) ← σ.add (.op o r.val c)
        return σ.setReg rd ⟨v, v, 0, none⟩
  | .op o rd rs1 rs2 => do
    match (σ.reg rs1).cst, (σ.reg rs2).cst with
    | some a, some b =>
      let (σ, x) ← σ.cst (alu o a b)
      return σ.setReg rd x
    | _, _ =>
      let (σ, v) ← σ.add (opNode o (σ.reg rs1).val (σ.reg rs2).val)
      return σ.setReg rd ⟨v, v, 0, none⟩
  | .mop o rd rs1 rs2 => do
    if rd = 0 then none
    let (σ, v) ← σ.add (.mop o (σ.reg rs1).val (σ.reg rs2).val (if mopUsesRd o then (σ.reg rd).val else 0))
    return σ.setReg rd ⟨v, v, 0, none⟩
  | .load n sg rd rs1 off => do
    if rd = 0 then return σ
    let r := σ.reg rs1
    let k := r.off + off
    let cs := .aligned r.base k n :: .readable r.base k n :: σ.conds
    match ← resolve r.base k n σ.writes cs with
    | (some x, cs) => return { σ.setReg rd x with conds := cs }
    | (none, cs) =>
      let (σ, v) ← σ.add (.load n sg r.base k)
      return { σ.setReg rd ⟨v, v, 0, none⟩ with conds := cs }
  | .store n rs2 rs1 off => do
    let r := σ.reg rs1
    let k := r.off + off
    return { σ with writes := ⟨r.base, k, n, σ.reg rs2⟩ :: σ.writes,
                    conds := .aligned r.base k n :: .writable r.base k n :: σ.conds }
  | _ => none

def symRun : List Instr → SState → Option SState
  | [], σ => some σ
  | i :: is, σ => (symStep σ i).bind (symRun is)

end RV.Sym

namespace RV.Sym

/-- The pool of the initial registers: id `i` is register `i` (`x0` is the constant 0). -/
def initPool : Pool :=
  let nodes := (List.range 32).reverse.map fun i => if i = 0 then Node.const 0 else Node.var i
  ⟨nodes, nodes.map Node.key, 32⟩

def initState : SState := ⟨initPool, (List.range 32).map fun i => ⟨i, i, 0, if i = 0 then some 0 else none⟩, [], []⟩

end RV.Sym
