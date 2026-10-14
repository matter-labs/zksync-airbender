/-
# Running the official Sail RISC-V model (RV32) on a simple state.

`SailRV32` is generated from sail-riscv by `sail/regen.sh` (pinned, see `sail/PINS.md`).
Sail's semantics is a program in an effect monad (`SailM`); `runSail` interprets those effects on
`SailState` the same way lean-sail's `interpretSailEffects` does on its hash-map state.
-/
import SailRV32

open Sail Sail.ArchSem SailRV32 SailRV32.Functions

namespace Human

/-- All Sail registers (x1..x31, PC, CSRs, ...) and byte-addressed physical memory. -/
structure SailState where
  regs : (r : Register) → RegisterType r
  mem  : Nat → BitVec 8

/-- Set register `r` to `value`. -/
def SailState.set (s : SailState) (r : Register) (value : RegisterType r) : SailState :=
  { s with regs := fun r' => if h : r = r' then h ▸ value else s.regs r' }

abbrev FM := EStateM (Sail.Error exception) SailState

/-- The `numBytes` bytes at `addr`, little-endian. -/
def readBytes (mem : Nat → BitVec 8) (addr : Nat) : (numBytes : Nat) → BitVec (8 * numBytes)
  | 0 => 0#0
  | n+1 => (by omega : 8 * n + 8 = 8 * (n + 1)) ▸ ((readBytes mem (addr+1) n).append (mem addr))

/-- Memory after writing the `numBytes` bytes of `value` at `addr`, little-endian. -/
def writeBytes (mem : Nat → BitVec 8) (addr : Nat) : (numBytes : Nat) → BitVec (8 * numBytes) → (Nat → BitVec 8)
  | 0, _ => mem
  | n+1, value =>
    let bytes : BitVec (8 + 8 * n) := (by omega : 8 * (n + 1) = 8 + 8 * n) ▸ value
    let restWritten := writeBytes mem (addr+1) n (bytes.extractLsb' 8 (8*n))
    fun a => if a = addr then bytes.extractLsb' 0 8 else restWritten a

/-- How each Sail effect acts on the state. Effects with no meaning for a single in-order hart
(barriers, cache/TLB ops, trace messages, ...) do nothing. -/
noncomputable def applyEffect : (eff : InstructionEffect) → FM eff.ret
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
noncomputable def runSail {α} (m : SailM α) (s : SailState) : EStateM.Result (Sail.Error exception) SailState α :=
  (FreeM.liftM (fun
    | .inl (.error err) => throw err
    | .inl (.ok eff) => applyEffect eff
    | .inr (n : Nat) => if h : 0 < n then pure (⟨0, h⟩ : Fin n) else throw .Unreachable) m : FM α).run s

end Human
