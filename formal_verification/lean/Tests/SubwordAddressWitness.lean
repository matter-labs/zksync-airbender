import Tests.SubwordBoundsWitness

namespace Tests.SubwordAddressWitness
open Airbender Verification Arithmetic Trace SubwordMemory
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

abbrev rom := Tests.SubwordDecoderFixture.rom

/-- Full native rows for 0xffffffff + 1 and 0 + signExtend(-3).
    Retain actual native queries and original public instruction shadow bytes. -/
def wrapValues : Array Nat := #[0,0,4,0,1,1,0,3,0,1,0,0,0,4,0,8,0,65535,65535,0,0,1,0,1,1,0,0,0,0,0,0,0,33155,16,1,3,0,0,0,65534,65535,33022,4660,33022,65534,65535,33155,0,98556,0,98556,0,0,33022,4660,46,33022,65534,65535,45,65534,65535,65534,65535,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
def negativeValues : Array Nat := #[0,0,4,0,1,1,0,3,0,65533,65535,0,0,4,0,8,0,0,0,65533,65535,0,1,1,1,0,1,63,0,0,65532,65535,32769,32769,1,3,0,0,0,65408,65535,65408,65535,65408,0,0,32769,0,65408,0,65408,0,98305,65408,65535,45,0,0,0,0,65408,65535,65408,65535,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]

def assignment (sample : Fin 2) (column : Nat) : ZMod mersenne31Modulus :=
  ((if sample.val = 0 then wrapValues else negativeValues)[column]?.getD 0 : Nat)

def entry : Fin 2 → SubwordMemory.ProgramEntry
  | 0 => ⟨0,0x00108183,.LOAD (1,.Regidx 1,.Regidx 3,false,1),⟨.lb,1,0,3,⟨1,0⟩,0,0⟩⟩
  | 1 => ⟨0,0xffd08183,.LOAD (4093,.Regidx 1,.Regidx 3,false,1),⟨.lb,1,0,3,⟨65533,65535⟩,0,0⟩⟩

end Tests.SubwordAddressWitness
