import Airbender.Review.Circuits.ReducedMachine.MainAuxiliary
import Airbender.Review.Helpers.Context.Model

namespace Airbender.NativeMemoryTokens
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMainAuxiliary

/-- Lossless Clean address coding of the native field tuple. Native register1/
    RAM0 becomes Clean space0/1 by FIELD complement, before canonical Nat coding.
    No Boolean selector, address/word/clock range or stage2 truncation is assumed. -/
def encodeAddress (address : MemoryKeyAddress) : Nat :=
  Nat.pair (1-address.isRegister).val (Nat.pair address.low.val address.high.val)

def encodeKey (key : MemoryKey) : Trace.MemoryToken mersenne31Modulus :=
  ⟨encodeAddress key.address,(key.time[0],key.time[1]),Nat.pair key.value[0].val key.value[1].val⟩

/-- Algebraic decoder used to prove losslessness ON encoded native keys. An
    arbitrary Clean Nat token need not be a canonical native field-key encoding. -/
def decodeKey (token : Trace.MemoryToken mersenne31Modulus) : MemoryKey :=
  let address := Nat.unpair token.address
  let limbs := Nat.unpair address.2
  let value := Nat.unpair token.value
  ⟨⟨1-(address.1 : ZMod mersenne31Modulus),limbs.1,limbs.2⟩,
    #v[(value.1 : ZMod mersenne31Modulus),(value.2 : ZMod mersenne31Modulus)],
    #v[token.time.1,token.time.2]⟩

/-- ALL actual imported main ports, without an execute/CSR/issued-row filter.
    Readonly accesses retain the timestamp refresh and third-port writes remain
    unmasked here; full-domain execute masking is a separate native argument. -/
def mainTokens (w : Nat → ZMod mersenne31Modulus) (write : Bool) : List (Trace.MemoryToken mersenne31Modulus) :=
  Airbender.ReducedMachine.Native.importedConstraintsMemoryPorts.toList.map
    (if write then Trace.writeToken Airbender.ReducedMachine.Native.importedConstraintsTraceColumns w
      else Trace.readToken w)

/-- ALL43 reviewed raw quotient keys, including inactive rows, OLDREADs and
    readonly refreshes. This is not stage2 u16 address refinement or matching. -/
def workerTokens (w : Nat → ZMod mersenne31Modulus) (write : Bool) : List (Trace.MemoryToken mersenne31Modulus) :=
  (List.finRange 43).map fun slot => encodeKey (quotientMemoryKey w slot write)

/-- Compression reference on decoded keys; not an injective map or an argument
    that a scalar product equality establishes precompression token matching. -/
def tokenArgument {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : MemoryKeyChallenges R) (token : Trace.MemoryToken mersenne31Modulus) : R :=
  memoryKeyArgument embed ch (decodeKey token)

end Airbender.NativeMemoryTokens
