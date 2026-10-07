import Sail

namespace Sail.ArchSem

/-- The pinned backend emits runtime errors inside early-return computations.
    Reuse the existing Sail effects, keeping errors distinct from early returns. -/
def catchRuntimeErrors {ue ε α : Type} [Arch] (program : PreSailME ue ε α)
    (handler : Sail.Error ue → PreSailME ue ε α) : PreSailME ue ε α :=
  match program with
  | .pure value => .pure value
  | .impure (.ok (.inl (.error error))) _ => handler error
  | .impure effect cont => .impure effect (fun value => catchRuntimeErrors (cont value) handler)

instance runtimeErrors {ue ε : Type} [Arch] :
    MonadExcept (Sail.Error ue) (PreSailME ue ε) where
  throw error := .impure (.ok (.inl (.error error))) Empty.elim
  tryCatch := catchRuntimeErrors

/-- Selected emulator setting: experimental extensions disabled. Source: pinned
    c_emulator/riscv_model_impl.h's default and riscv_model_impl.cpp's getter.
    This is a platform configuration binding, not an instruction definition. -/
def sys_enable_experimental_extensions (_ : Unit) : Bool := false

/-- External platform calls left abstract. Memory proofs quantify over the
    bindings; this interface supplies no implementation or behavioral axiom. -/
class MemoryPlatform (ue : Type) [Arch] where
  terminalWrite : BitVec 8 → PreSailM ue Unit
  reserve : BitVec Arch.addr_size → Nat → PreSailM ue Unit
  reservationMatches : BitVec Arch.addr_size → Bool

def plat_term_write {ue : Type} [Arch] [MemoryPlatform ue] (byte : BitVec 8) :
    PreSailM ue Unit := MemoryPlatform.terminalWrite byte

def load_reservation {ue : Type} [Arch] [MemoryPlatform ue]
    (address : BitVec Arch.addr_size) (width : Nat) : PreSailM ue Unit :=
  MemoryPlatform.reserve address width

def match_reservation {ue : Type} [Arch] [MemoryPlatform ue]
    (address : BitVec Arch.addr_size) : Bool :=
  MemoryPlatform.reservationMatches (ue := ue) address

end Sail.ArchSem
