import Airbender.Review.Helpers.Memory.ReducedMachineWordMemory
import Airbender.Review.Circuits.ReducedMachine.Tables.WordMemory
import Airbender.Review.Circuits.ReducedMachine.PC
import Airbender.Review.Circuits.ReducedMachine.ShiftResult

namespace Airbender.ReducedMachine.Native
open Arithmetic Trace
set_option autoImplicit false

/-- Actual native second-read and third-write words, in their derived spaces. -/
def wordMemorySecondWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 37).val,(w 38).val⟩
def wordMemoryWrittenWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 43).val,(w 44).val⟩

def wordMemoryROMWord (index : Nat) : Word :=
  ⟨(NativeFixed.wordROMValue index)[0],(NativeFixed.wordROMValue index)[1]⟩

/-- The exact native fixture supplies ROM loads; RAM loads select their actual
    initialized memory read. This is not an original Sail memory observation. -/
def wordMemoryLoadWord (w : Nat → ZMod mersenne31Modulus) : Word :=
  if (wordMemoryAddressWord w).hi < 64 then wordMemoryROMWord ((wordMemoryAddressWord w).value/4)
  else wordMemorySecondWord w

def wordMemoryResult (w : Nat → ZMod mersenne31Modulus) (entry : WordMemoryProgramEntry) : Word :=
  if entry.data.family then wordMemorySecondWord w
  else if entry.data.rd = 0 then ⟨0,0⟩ else wordMemoryLoadWord w

/-- Native numerical and port observations only. Original GPR/memory realization,
    shadow-ledger/ROM-byte correspondence and retained Sail execution are separate. -/
structure WordMemoryNumericalEffects (w : Nat → ZMod mersenne31Modulus) (entry : WordMemoryProgramEntry) : Prop where
  ports : ∀ i : Fin 3, importedConstraintsMemoryPorts[i].address.code w =
    (wordMemoryPortCells w entry)[i].addressCode
  address : wordMemoryAddressWord w = Word.ofBitVec ((sourceWord w).toBitVec+entry.data.immediate.toBitVec)
  aligned : (wordMemoryAddressWord w).value%4 = 0
  storeRAM : entry.data.family = true → 4194304 ≤ (wordMemoryAddressWord w).value
  written : wordMemoryWrittenWord w = wordMemoryResult w entry
  pcBound : (finalPCWord w).Bounded
  pc : (finalPCWord w).toBitVec = (initialPCWord w).toBitVec+4

end Airbender.ReducedMachine.Native
