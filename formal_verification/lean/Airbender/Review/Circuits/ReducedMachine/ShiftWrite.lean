import Airbender.Review.Circuits.ReducedMachine.Row

namespace Airbender.ReducedMachine.Native

/-- Native source-one read and destination write, interpreted from actual ports. -/
def source1 (w : Nat → ZMod mersenne31Modulus) : Vector (ZMod mersenne31Modulus) 2 :=
  (importedConstraintsMemoryPorts[0]'(by decide)).readValue.evaluate w

def rdPort : Trace.MemoryPort := importedConstraintsMemoryPorts[2]'(by decide)

def rdWrite (w : Nat → ZMod mersenne31Modulus) : Vector (ZMod mersenne31Modulus) 2 :=
  (rdPort.writeValue.getD rdPort.readValue).evaluate w

def rdIndex (w : Nat → ZMod mersenne31Modulus) : ZMod mersenne31Modulus :=
  w importedConstraintsDecoderColumns.rd

def rdZeroFlag (w : Nat → ZMod mersenne31Modulus) : ZMod mersenne31Modulus :=
  w importedConstraintsDecoderColumns.rdIsZero

def shiftLowParts (w : Nat → ZMod mersenne31Modulus) : Vector (ZMod mersenne31Modulus) 2 :=
  #v[w 66,w 67]

def shiftHighParts (w : Nat → ZMod mersenne31Modulus) : Vector (ZMod mersenne31Modulus) 2 :=
  #v[w 75,w 76]

/-- Original native field packing for the direction, amount and one input limb. -/
def ShiftMode.lookupKey (mode : ShiftMode) (limb amount : ZMod mersenne31Modulus) :
    ZMod mersenne31Modulus :=
  limb + 65536 * amount + 2097152 * (if mode = .left then 0 else 1)

/-- Native contribution assembly only. Table-37 arithmetic meaning is separate. -/
def ShiftMode.assemble (mode : ShiftMode) (low high fill : Vector (ZMod mersenne31Modulus) 2) :
    Vector (ZMod mersenne31Modulus) 2 :=
  if mode = .left then #v[low[0] + fill[0],high[0] + low[1] + fill[1]]
  else #v[low[0] + high[1] + fill[0],high[0] + fill[1]]

def finalPC (w : Nat → ZMod mersenne31Modulus) : Vector (ZMod mersenne31Modulus) 2 :=
  importedConstraintsTraceColumns.finalPC.map w

def defaultPC (w : Nat → ZMod mersenne31Modulus) : Vector (ZMod mersenne31Modulus) 2 :=
  #v[w 49,w 50]

end Airbender.ReducedMachine.Native
