import Airbender.Review.Circuits.Blake2Worker.Schedule

namespace Airbender.NativeWorkerInitial
open Airbender.NativeWorkerSchedule
abbrev F := ZMod mersenne31Modulus
/-- Pinned native BLAKE2s IV words, before the configured digest twist. -/
def iv : Vector Nat 8 := #v[0x6A09E667,0xBB67AE85,0x3C6EF372,0xA54FF53A,0x510E527F,0x9B05688C,0x1F83D9AB,0x5BE0CD19]
def configuredIV (word : Fin 8) : Nat := if word.val = 0 then 0x6B08E647 else iv[word]
def limbOf (word : Nat) (limb : Fin 2) : F := ((word / 2^(16*limb.val) % 65536 : Nat) : F)
def oldExtended (w : Nat → F) (word : Fin 16) (limb : Fin 2) : F := w (36+4*word.val+limb.val)
def finalBase (w : Nat → F) (word : Fin 8) (limb : Fin 2) : F :=
  if inputBit w 2 = 0 then state w word limb else limbOf (configuredIV word) limb
def compressionIV (word : Fin 16) : Nat :=
  if h : word.val < 8 then configuredIV ⟨word.val,h⟩ else
  if word.val = 12 then 0x510E523F else if word.val = 14 then 0xE07C2654 else iv[(⟨word.val%8,by omega⟩ : Fin 8)]
/-- Pre-mixing state from actual original reads and actual control bits. Words
    12/14 retain their old values in normal mode, even on the first round. -/
def initial (w : Nat → F) (word : Fin 16) (limb : Fin 2) : F :=
  if inputBit w 3 = 0 then oldExtended w word limb else
  if h : word.val < 8 then finalBase w ⟨word.val,h⟩ limb else
  if word.val = 12 ∨ word.val = 14 then
    if inputBit w 2 = 0 then oldExtended w word limb else limbOf (compressionIV word) limb
  else limbOf iv[(⟨word.val%8,by omega⟩ : Fin 8)] limb
/-- Actual imported logical columns; no physical-column coercion. -/
def initialColumns : Vector Nat 32 := #v[155,157,159,161,163,165,167,169,171,173,175,177,179,181,183,185,186,187,188,189,190,191,192,193,198,199,194,195,200,201,196,197]
def observed (w : Nat → F) (word : Fin 16) (limb : Fin 2) : F := w initialColumns[(⟨2*word.val+limb.val,by have := word.isLt; have := limb.isLt; omega⟩ : Fin 32)]
structure RowEffects (w : Nat → F) : Prop where
  schedule : Airbender.NativeWorkerSchedule.RowEffects w
  bases : ∀ word : Fin 8, ∀ limb : Fin 2, w (154+4*word.val+2*limb.val) = finalBase w word limb
  initialized : ∀ word : Fin 16, ∀ limb : Fin 2, observed w word limb = initial w word limb
end Airbender.NativeWorkerInitial
