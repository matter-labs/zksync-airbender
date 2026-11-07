import Airbender.Review.Circuits.Blake2Worker.Processing

namespace Airbender.Blake2Worker.Native
open Verification

inductive KeyLocation where
  | register (index : Nat)
  | indirect (base : Vector Nat 2) (offset : Nat)
  deriving DecidableEq, Inhabited

structure KeyDescriptor where
  location : KeyLocation
  access : Access
  deriving DecidableEq, Inhabited

/-- Actual native register/indirect order, retaining all43 accesses. -/
def keyDescriptors : Array KeyDescriptor := constraintsABI.registers.flatMap fun register =>
  #[⟨.register register.register,register.access⟩] ++ register.indirects.map
    (fun access => ⟨.indirect register.access.readValue access.offset,access⟩)

def keyDescriptor (slot : Fin 43) : KeyDescriptor := keyDescriptors[slot.val]!

structure MemoryKeyAddress where
  isRegister : ZMod mersenne31Modulus
  low : ZMod mersenne31Modulus
  high : ZMod mersenne31Modulus
  deriving DecidableEq

structure MemoryKey where
  address : MemoryKeyAddress
  value : Vector (ZMod mersenne31Modulus) 2
  time : Vector (ZMod mersenne31Modulus) 2
  deriving DecidableEq

/-- Reviewed quotient key at unit normalization, selected empty-carry metadata.
    This is not an initialized architectural address or a physical LDE point. -/
def quotientKeyAddress (w : Nat → ZMod mersenne31Modulus) : KeyLocation → MemoryKeyAddress
  | .register index => ⟨1,index,0⟩
  | .indirect base offset => ⟨0,w base[0]+offset,w base[1]⟩

/-- Reviewed native stage2 u16 conversion/addition; high overflow makes the
    native helper's assert fail. No failed address is silently discarded. -/
def stageTwoIndirectAddress (lo hi : ZMod mersenne31Modulus) (offset : Nat) : Option MemoryKeyAddress :=
  let sum := lo.val % 65536 + offset
  let high := hi.val % 65536 + sum / 65536
  if high < 65536 then some ⟨0,((sum % 65536 : Nat) : ZMod mersenne31Modulus),(high : ZMod mersenne31Modulus)⟩ else none

def stageTwoKeyAddress (w : Nat → ZMod mersenne31Modulus) : KeyLocation → Option MemoryKeyAddress
  | .register index => some ⟨1,index,0⟩
  | .indirect base offset => stageTwoIndirectAddress (w base[0]) (w base[1]) offset

def keyValue (w : Nat → ZMod mersenne31Modulus) (slot : Fin 43) (write : Bool) : Vector (ZMod mersenne31Modulus) 2 :=
  let access := memoryAccess slot
  (if write then access.writeValue.getD access.readValue else access.readValue).map w

def keyTime (w : Nat → ZMod mersenne31Modulus) (slot : Fin 43) (write : Bool) : Vector (ZMod mersenne31Modulus) 2 :=
  (if write then constraintsABI.writeTime else (memoryAccess slot).readTime).map w

def quotientMemoryKey (w : Nat → ZMod mersenne31Modulus) (slot : Fin 43) (write : Bool) : MemoryKey :=
  ⟨quotientKeyAddress w (keyDescriptor slot).location,keyValue w slot write,keyTime w slot write⟩

def stageTwoMemoryKey (w : Nat → ZMod mersenne31Modulus) (slot : Fin 43) (write : Bool) : Option MemoryKey :=
  (stageTwoKeyAddress w (keyDescriptor slot).location).map
    (fun address => ⟨address,keyValue w slot write,keyTime w slot write⟩)

structure MemoryKeyChallenges (R : Type) where
  gamma : R
  addressLow : R
  addressHigh : R
  timeLow : R
  timeHigh : R
  valueLow : R
  valueHigh : R

/-- Native affine factor: register indicator has literal coefficient1; the six
    challenge positions are address low/high,time low/high,value low/high. -/
def memoryKeyArgument {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : MemoryKeyChallenges R) (key : MemoryKey) : R :=
  ch.gamma + embed key.address.isRegister + ch.addressLow*embed key.address.low +
    ch.addressHigh*embed key.address.high + ch.timeLow*embed key.time[0] +
    ch.timeHigh*embed key.time[1] + ch.valueLow*embed key.value[0] + ch.valueHigh*embed key.value[1]

def memoryKeyProduct {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : MemoryKeyChallenges R) (w : Nat → ZMod mersenne31Modulus) (write : Bool) : R :=
  ((List.finRange 43).map fun slot => memoryKeyArgument embed ch (quotientMemoryKey w slot write)).prod

/-- Unused-row precompression key agreement only. No active-key refinement,
    memory matching, inverse, issued stream or quotient enforcement is assumed. -/
structure PaddingMemoryKeys (w : Nat → ZMod mersenne31Modulus) : Prop where
  addresses : w constraintsABI.multiplicity = 0 → ∀ slot : Fin 43,
    stageTwoKeyAddress w (keyDescriptor slot).location = some (quotientKeyAddress w (keyDescriptor slot).location)
  readKeys : w constraintsABI.multiplicity = 0 → ∀ slot : Fin 43,
    stageTwoMemoryKey w slot false = some (quotientMemoryKey w slot false)
  writeKeys : w constraintsABI.multiplicity = 0 → ∀ slot : Fin 43,
    stageTwoMemoryKey w slot true = some (quotientMemoryKey w slot true)
  equalKeys : w constraintsABI.multiplicity = 0 → ∀ slot : Fin 43,
    quotientMemoryKey w slot false = quotientMemoryKey w slot true

end Airbender.Blake2Worker.Native
