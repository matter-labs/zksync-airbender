/-
# Running the official Sail RISC-V model (RV32) on a simple state.

`SailRV32` is generated from sail-riscv by `sail/regen.sh` (pinned, see `sail/PINS.md`).
Sail's semantics is a program in an effect monad (`SailM`); `runF` interprets those effects on
`FState` the same way lean-sail's `interpretSailEffects` does on its hash-map state.
-/
import SailRV32

open Sail Sail.ArchSem SailRV32 SailRV32.Functions

namespace Human

/-- All Sail registers (x1..x31, PC, CSRs, ...) and byte-addressed physical memory. -/
structure FState where
  regs : (r : Register) → RegisterType r
  mem  : Nat → BitVec 8

/-- Set register `r` to `v`. -/
def FState.set (s : FState) (r : Register) (v : RegisterType r) : FState :=
  { s with regs := fun r' => if h : r = r' then h ▸ v else s.regs r' }

abbrev FM := EStateM (Sail.Error exception) FState

/-- `n` bytes at `addr`, little endian. -/
def readBytes (mem : Nat → BitVec 8) (addr : Nat) : (n : Nat) → BitVec (8 * n)
  | 0 => 0#0
  | n+1 => (by omega : 8 * n + 8 = 8 * (n + 1)) ▸ ((readBytes mem (addr+1) n).append (mem addr))

def writeBytes (mem : Nat → BitVec 8) (addr : Nat) : (n : Nat) → BitVec (8 * n) → (Nat → BitVec 8)
  | 0, _ => mem
  | n+1, v =>
    let v' : BitVec (8 + 8 * n) := (by omega : 8 * (n + 1) = 8 + 8 * n) ▸ v
    let m' := writeBytes mem (addr+1) n (v'.extractLsb' 8 (8*n))
    fun a => if a = addr then v'.extractLsb' 0 8 else m' a

/-- How each Sail effect acts on the state. Effects with no meaning for a single in-order hart
(barriers, cache/TLB ops, trace messages, ...) do nothing. -/
noncomputable def interpEff : (eff : InstructionEffect) → FM eff.ret
  | .regRead reg _ => do pure ((← get).regs reg)
  | .regWrite reg _ v => modify (·.set reg v)
  | .barrier _ | .cacheOp _ | .tlbOp _ | .translationStart _ | .translationEnd _ | .archException _
  | .returnException | .memWriteAnnounce _ | .printMessage _ | .clockCycle => pure ()
  | .getCycleCount => pure (0 : Nat)
  | .memRead req => do pure (.ok (readBytes (← get).mem req.address.toNat req.size, 0#req.numTag))
  | .memWrite req v _ => do
      modify fun s => { s with mem := writeBytes s.mem req.address.toNat req.size v }
      pure (.ok ())

/-- Run a Sail computation. Nondeterministic choices are resolved to the first option. -/
noncomputable def runF {α} (m : SailM α) (s : FState) : EStateM.Result (Sail.Error exception) FState α :=
  (FreeM.liftM (fun
    | .inl (.error err) => throw err
    | .inl (.ok eff) => interpEff eff
    | .inr (n : Nat) => if h : 0 < n then pure (⟨0, h⟩ : Fin n) else throw .Unreachable) m : FM α).run s

end Human
