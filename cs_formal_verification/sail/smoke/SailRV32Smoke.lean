/-
Smoke test + minimal proof-friendly machine for the generated Sail RV32 model (copied into lean/sail-rv32 by
sail/regen.sh; build with `lake build SailRV32Smoke`). Everything is checked by the *kernel* (`decide +kernel`).

lean-sail's `SequentialState` keeps registers/memory in `Std.ExtDHashMap`s, which the kernel cannot evaluate.
`FState` below uses total functions instead, and `runF` is the same interpreter as lean-sail's
`interpretSailEffects`/`interpretInstructionEffect` for that state.
-/
import SailRV32

open Sail Sail.ArchSem SailRV32 SailRV32.Functions
set_option maxRecDepth 1000000

namespace SailRV32Smoke

structure FState where
  regs : (r : Register) → RegisterType r
  mem  : Nat → BitVec 8            -- byte-addressed physical memory (little endian)

abbrev FM := EStateM (Sail.Error exception) FState

def readBytesF (mem : Nat → BitVec 8) (addr : Nat) : (n : Nat) → BitVec (8 * n)
  | 0 => 0#0
  | n+1 =>
    have h : 8 * n + 8 = 8 * (n + 1) := by omega
    h ▸ ((readBytesF mem (addr+1) n).append (mem addr))

def writeBytesF (mem : Nat → BitVec 8) (addr : Nat) : (n : Nat) → BitVec (8 * n) → (Nat → BitVec 8)
  | 0, _ => mem
  | n+1, v =>
    have h : 8 * (n + 1) = 8 + 8 * n := by omega
    let v' : BitVec (8 + 8 * n) := h ▸ v
    let m' := writeBytesF mem (addr+1) n (v'.extractLsb' 8 (8*n))
    fun a => if a = addr then v'.extractLsb' 0 8 else m' a

noncomputable def interpEff : (eff : InstructionEffect) → FM eff.ret
  | .regRead reg _ => do pure ((← get).regs reg)
  | .regWrite reg _ v => modify fun s => { s with regs := fun r => if h : reg = r then h ▸ v else s.regs r }
  | .barrier _ | .cacheOp _ | .tlbOp _ | .translationStart _ | .translationEnd _ | .archException _
  | .returnException | .memWriteAnnounce _ | .printMessage _ | .clockCycle => pure ()
  | .getCycleCount => pure (0 : Nat)
  | .memRead req => do
      let s ← get
      pure (.ok (readBytesF s.mem req.address.toNat req.size, 0#req.numTag))
  | .memWrite req v _ => do
      modify fun s => { s with mem := writeBytesF s.mem req.address.toNat req.size v }
      pure (.ok ())

noncomputable def runF {α} (m : SailM α) (s : FState) : EStateM.Result (Sail.Error exception) FState α :=
  (FreeM.liftM (fun
    | .inl (.error err) => throw err
    | .inl (.ok eff) => interpEff eff
    | .inr (choice : Nat) => if h : (0 : Nat) < choice then pure (⟨0, h⟩ : Fin choice) else throw .Unreachable) m : FM α).run s

/-- every register starts at `default` (zeros); `initM` then runs the model's own initialisation. -/
noncomputable def dflt : (r : Register) → RegisterType r := fun r => by cases r <;> exact default

noncomputable def s0 : FState := { regs := dflt, mem := fun _ => 0 }

/-- what sail-riscv's own emulator does before running: register initialisers, then reset. -/
noncomputable def initM : SailM Unit := do sail_model_init (); init_model ""

/-- `add a0, a0, a1` (0x00b50533) at 0x80000000 (the default config's main-memory region). -/
def prog : Nat → BitVec 8 := fun a =>
  if a = 0x80000000 then 0x33#8 else if a = 0x80000001 then 0x05#8
  else if a = 0x80000002 then 0xb5#8 else if a = 0x80000003 then 0x00#8 else 0#8

noncomputable def stepM : SailM Bool := do
  initM
  writeReg Register.x10 (4#32); writeReg Register.x11 (3#32)
  writeReg Register.PC (0x80000000#32); writeReg Register.nextPC (0x80000000#32)
  try_step 0 false

noncomputable def run1 := runF stepM { s0 with mem := prog }

noncomputable def x10v : BitVec 32 := match run1 with | .ok _ s => s.regs Register.x10 | .error _ _ => 0
noncomputable def pcv  : BitVec 32 := match run1 with | .ok _ s => s.regs Register.PC  | .error _ _ => 0
noncomputable def machine : Bool :=
  match run1 with
  | .ok _ s => match (s.regs Register.cur_privilege : Privilege) with | .Machine => true | _ => false
  | .error _ _ => false

/-- one `try_step` of the *official* model, run from the reset state, executes the ADD. -/
example : x10v = 7#32 := by decide +kernel
example : pcv = 0x80000004#32 := by decide +kernel
example : machine = true := by decide +kernel

/-! decode of concrete words (state-dependent: `currentlyEnabled` reads misa & co.) -/
noncomputable def stI : FState := match runF initM s0 with | .ok _ s => s | .error _ s => s

noncomputable def isAdd (w : BitVec 32) : Bool :=
  match runF (ext_decode w) stI with
  | .ok (.RTYPE (_, _, _, .ADD)) _ => true
  | _ => false
noncomputable def isMul (w : BitVec 32) : Bool :=
  match runF (ext_decode w) stI with
  | .ok (.MUL (_, _, _, _)) _ => true
  | _ => false
example : isAdd 0x00b50533#32 = true := by decide +kernel
example : isMul 0x02b50533#32 = true := by decide +kernel   -- mul a0,a0,a1 : M is enabled by the reset misa

end SailRV32Smoke
