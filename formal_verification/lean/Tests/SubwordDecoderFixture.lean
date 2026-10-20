import Airbender.Review.Circuits.SubwordMemory.Decoding
import Tests.SubwordRoutingFixture

namespace Tests.SubwordDecoderFixture
open Airbender Verification Arithmetic Trace SubwordMemory
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

abbrev rom := Tests.SubwordRoutingFixture.rom

/-- Seven full native rows with decoder-compatible unused indices and store x0
    flags. Keep the original local fixtures unchanged and add unsigned byte data. -/
def values : Fin 7 → Array Nat
  | 0 => #[0,0,4,0,1,1,0,3,0,0,0,0,0,4,0,8,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,32769,32769,1,3,0,0,0,65534,65535,33022,4660,33022,65534,65535,32769,0,98556,0,98556,0,0,33022,4660,46,33022,65534,65535,45,65534,65535,65534,65535,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
  | 1 => #[0,0,4,0,1,1,0,3,0,0,0,5,0,4,0,8,0,6,0,6,0,0,2,3,1,1,0,0,0,0,4,0,32769,32769,1,3,0,0,0,35243,0,52719,35243,35243,35243,0,32769,0,0,87962,0,87962,1,52719,35243,46,1477035,35243,0,45,35243,0,35243,0,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
  | 2 => #[0,0,4,0,1,1,0,3,0,0,0,0,0,4,0,8,0,1,64,1,64,0,1,1,1,0,1,0,0,0,0,64,32769,32769,1,3,0,0,0,65408,65535,65408,65535,65408,0,0,32769,0,65408,0,65408,0,98305,65408,65535,45,0,0,0,0,65408,65535,65408,65535,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
  | 3 => #[0,0,4,0,1,1,0,0,1,0,0,1,0,4,0,8,0,2,64,2,64,0,2,3,1,1,1,0,0,0,0,64,32769,32769,1,0,0,0,0,0,0,32769,65535,65535,0,0,32769,0,0,32769,0,32769,425985,32769,65535,45,0,0,0,0,32769,65535,0,0,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
  | 4 => #[0,0,4,0,1,1,2,0,1,0,0,0,1,4,0,8,0,3,64,3,64,0,3,3,1,1,1,0,0,0,2,0,4779,57005,0,0,64,17767,35277,17767,43981,205,0,0,43776,0,57005,35277,17767,43981,17767,43981,231885,205,0,54,201387,43776,0,55,0,0,0,0,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
  | 5 => #[0,0,4,0,1,1,2,0,1,0,0,1,1,4,0,8,0,0,64,0,64,0,0,1,1,0,1,0,0,0,2,0,4779,57005,0,0,64,17767,35277,4779,35277,0,0,0,4779,0,4779,17767,4779,35277,4779,35277,279911,0,0,54,266923,4779,0,55,0,0,0,0,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
  | 6 => #[0,0,4,0,1,1,0,3,0,0,0,4,0,4,0,8,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,32769,32769,1,3,0,0,0,254,0,33022,4660,33022,254,0,32769,0,33276,0,33276,0,0,33022,4660,46,1081598,254,0,45,254,0,254,0,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]

def assignment (sample : Fin 7) (column : Nat) : ZMod mersenne31Modulus :=
  ((values sample)[column]?.getD 0 : Nat)

/-- Independent original instructions and their public bytes at PC zero. -/
def entry : Fin 7 → SubwordMemory.ProgramEntry
  | 0 => ⟨0,0x00008183,.LOAD (0,.Regidx 1,.Regidx 3,false,1),⟨.lb,1,0,3,⟨0,0⟩,0,0⟩⟩
  | 1 => ⟨0,0x0000d183,.LOAD (0,.Regidx 1,.Regidx 3,true,2),⟨.lhu,1,0,3,⟨0,0⟩,0,5⟩⟩
  | 2 => ⟨0,0x00008183,.LOAD (0,.Regidx 1,.Regidx 3,false,1),⟨.lb,1,0,3,⟨0,0⟩,0,0⟩⟩
  | 3 => ⟨0,0x00009003,.LOAD (0,.Regidx 1,.Regidx 0,false,2),⟨.lh,1,0,0,⟨0,0⟩,0,1⟩⟩
  | 4 => ⟨0,0x00208023,.STORE (0,.Regidx 2,.Regidx 1,1),⟨.sb,1,2,0,⟨0,0⟩,1,0⟩⟩
  | 5 => ⟨0,0x00209023,.STORE (0,.Regidx 2,.Regidx 1,2),⟨.sh,1,2,0,⟨0,0⟩,1,1⟩⟩
  | 6 => ⟨0,0x0000c183,.LOAD (0,.Regidx 1,.Regidx 3,true,1),⟨.lbu,1,0,3,⟨0,0⟩,0,4⟩⟩

def before (sample : Fin 7) : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    mem := ((Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 0 (BitVec.ofNat 8 (entry sample).bits.toNat)
      |>.insert 1 (BitVec.ofNat 8 ((entry sample).bits.toNat / 256))
      |>.insert 2 (BitVec.ofNat 8 ((entry sample).bits.toNat / 65536))
      |>.insert 3 (BitVec.ofNat 8 ((entry sample).bits.toNat / 16777216))) }

def setup (sample : Fin 7) : SparseDecoderSetup Operation := ⟨[some (entry sample)],1048575⟩

/-- Dynamic queries remain original native queries, with one added unsigned byte row. -/
theorem lookup_members (sample : Fin 7) (slot : Fin 2) :
    (NativeSubwordLookup.table rom).Contains #[]
      #v[assignment sample (52 + 4 * slot.val),assignment sample (53 + 4 * slot.val),
        assignment sample (54 + 4 * slot.val),assignment sample (55 + 4 * slot.val)] := by
  fin_cases sample
  · have same : (fun j : Fin 2 => #v[assignment ⟨0,by decide⟩ (52 + 4 * j.val),
        assignment ⟨0,by decide⟩ (53 + 4 * j.val),assignment ⟨0,by decide⟩ (54 + 4 * j.val),
        assignment ⟨0,by decide⟩ (55 + 4 * j.val)]) = (fun j : Fin 2 =>
        #v[Tests.SubwordRoutingFixture.assignment ⟨0,by decide⟩ (52 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨0,by decide⟩ (53 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨0,by decide⟩ (54 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨0,by decide⟩ (55 + 4 * j.val)]) := by
      funext j; fin_cases j <;> decide +kernel
    rw [congrFun same slot]
    exact Tests.SubwordRoutingFixture.lookup_members ⟨0,by decide⟩ slot
  · have same : (fun j : Fin 2 => #v[assignment ⟨1,by decide⟩ (52 + 4 * j.val),
        assignment ⟨1,by decide⟩ (53 + 4 * j.val),assignment ⟨1,by decide⟩ (54 + 4 * j.val),
        assignment ⟨1,by decide⟩ (55 + 4 * j.val)]) = (fun j : Fin 2 =>
        #v[Tests.SubwordRoutingFixture.assignment ⟨1,by decide⟩ (52 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨1,by decide⟩ (53 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨1,by decide⟩ (54 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨1,by decide⟩ (55 + 4 * j.val)]) := by
      funext j; fin_cases j <;> decide +kernel
    rw [congrFun same slot]
    exact Tests.SubwordRoutingFixture.lookup_members ⟨1,by decide⟩ slot
  · have same : (fun j : Fin 2 => #v[assignment ⟨2,by decide⟩ (52 + 4 * j.val),
        assignment ⟨2,by decide⟩ (53 + 4 * j.val),assignment ⟨2,by decide⟩ (54 + 4 * j.val),
        assignment ⟨2,by decide⟩ (55 + 4 * j.val)]) = (fun j : Fin 2 =>
        #v[Tests.SubwordRoutingFixture.assignment ⟨2,by decide⟩ (52 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨2,by decide⟩ (53 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨2,by decide⟩ (54 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨2,by decide⟩ (55 + 4 * j.val)]) := by
      funext j; fin_cases j <;> decide +kernel
    rw [congrFun same slot]
    exact Tests.SubwordRoutingFixture.lookup_members ⟨2,by decide⟩ slot
  · have same : (fun j : Fin 2 => #v[assignment ⟨3,by decide⟩ (52 + 4 * j.val),
        assignment ⟨3,by decide⟩ (53 + 4 * j.val),assignment ⟨3,by decide⟩ (54 + 4 * j.val),
        assignment ⟨3,by decide⟩ (55 + 4 * j.val)]) = (fun j : Fin 2 =>
        #v[Tests.SubwordRoutingFixture.assignment ⟨3,by decide⟩ (52 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨3,by decide⟩ (53 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨3,by decide⟩ (54 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨3,by decide⟩ (55 + 4 * j.val)]) := by
      funext j; fin_cases j <;> decide +kernel
    rw [congrFun same slot]
    exact Tests.SubwordRoutingFixture.lookup_members ⟨3,by decide⟩ slot
  · have same : (fun j : Fin 2 => #v[assignment ⟨4,by decide⟩ (52 + 4 * j.val),
        assignment ⟨4,by decide⟩ (53 + 4 * j.val),assignment ⟨4,by decide⟩ (54 + 4 * j.val),
        assignment ⟨4,by decide⟩ (55 + 4 * j.val)]) = (fun j : Fin 2 =>
        #v[Tests.SubwordRoutingFixture.assignment ⟨4,by decide⟩ (52 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨4,by decide⟩ (53 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨4,by decide⟩ (54 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨4,by decide⟩ (55 + 4 * j.val)]) := by
      funext j; fin_cases j <;> decide +kernel
    rw [congrFun same slot]
    exact Tests.SubwordRoutingFixture.lookup_members ⟨4,by decide⟩ slot
  · have same : (fun j : Fin 2 => #v[assignment ⟨5,by decide⟩ (52 + 4 * j.val),
        assignment ⟨5,by decide⟩ (53 + 4 * j.val),assignment ⟨5,by decide⟩ (54 + 4 * j.val),
        assignment ⟨5,by decide⟩ (55 + 4 * j.val)]) = (fun j : Fin 2 =>
        #v[Tests.SubwordRoutingFixture.assignment ⟨5,by decide⟩ (52 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨5,by decide⟩ (53 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨5,by decide⟩ (54 + 4 * j.val),
          Tests.SubwordRoutingFixture.assignment ⟨5,by decide⟩ (55 + 4 * j.val)]) := by
      funext j; fin_cases j <;> decide +kernel
    rw [congrFun same slot]
    exact Tests.SubwordRoutingFixture.lookup_members ⟨5,by decide⟩ slot
  · fin_cases slot
    · change (NativeSubwordLookup.table rom).Contains #[] #v[0,33022,4660,46]
      exact (native_lookup_rom rom #v[0,33022,4660]).mpr ⟨⟨0,by decide⟩,by decide +kernel⟩
    · change (NativeSubwordLookup.table rom).Contains #[] #v[1081598,254,0,45]
      exact (native_lookup_load rom #v[1081598,254,0]).mpr ⟨⟨1081598,by decide⟩,by decide +kernel⟩

end Tests.SubwordDecoderFixture
