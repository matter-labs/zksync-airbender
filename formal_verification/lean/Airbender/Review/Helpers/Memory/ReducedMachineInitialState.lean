import Airbender.Review.Helpers.Memory.ReducedMachineROMImage
import Airbender.Review.Helpers.Memory.BytePadding

namespace Airbender.ReducedMachine.NativeInitialState
open Reference.RiscV.Sail

/-- Exactly the original Sail PC and writable GPR keys. x0 stays hardwired by
    Sail; nextPC and every configuration register remain independent. -/
def zeroKeys : List SailRV32.Register := [.PC,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30,.x31]

/-- Explicit finite dependent-map inserts, including missing original registers. -/
def zeroRegisters (registers : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType) :=
  ((((((((((((((((((((((((((((((((registers).insert .PC 0).insert .x1 0).insert .x2 0).insert .x3 0).insert .x4 0).insert .x5 0).insert .x6 0).insert .x7 0).insert .x8 0).insert .x9 0).insert .x10 0).insert .x11 0).insert .x12 0).insert .x13 0).insert .x14 0).insert .x15 0).insert .x16 0).insert .x17 0).insert .x18 0).insert .x19 0).insert .x20 0).insert .x21 0).insert .x22 0).insert .x23 0).insert .x24 0).insert .x25 0).insert .x26 0).insert .x27 0).insert .x28 0).insert .x29 0).insert .x30 0).insert .x31 0

/-- Logical reference-input constructor: original PC/GPR zero inserts, exact
    native ROM bytes, and explicit zero bytes at/above four MiB. The three bytes
    above the RV32 address range support ORIGINAL natural-address readBytes 4
    at any canonical, possibly unaligned, RV32 cell. This is not a Rust loader,
    physical setup, platform permission or native alignment certificate. -/
def memoryState (before : State) : State :=
  { before with mem := zeroByteMemory before.mem 4194304 (4294967299 - 4194304) }

def state (before : State) : State :=
  NativeROM.state { memoryState before with regs := zeroRegisters before.regs }

end Airbender.ReducedMachine.NativeInitialState
