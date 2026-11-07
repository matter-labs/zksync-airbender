import Airbender.Proofs.ReducedMachine.NativeMemoryTokens

namespace Airbender.NativeMemoryTokens
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMainAuxiliary

theorem native_address_token_injective : Function.Injective encodeAddress :=
  NativeMemoryTokenProofs.address_injective

theorem native_key_token_injective : Function.Injective encodeKey :=
  NativeMemoryTokenProofs.encode_injective

theorem actual_main_memory_tokens (w : Nat → ZMod mersenne31Modulus) (write : Bool) :
    ((List.finRange 3).map fun slot => encodeKey (mainMemoryKey w slot write)) = mainTokens w write :=
  NativeMemoryTokenProofs.main_list w write

theorem native_token_matching_iff (initial terminal reads writes : List MemoryKey) :
    (initial.map encodeKey ++ writes.map encodeKey).Perm
      (terminal.map encodeKey ++ reads.map encodeKey) ↔
    (initial ++ writes).Perm (terminal ++ reads) :=
  NativeMemoryTokenProofs.matching_encoding initial terminal reads writes

end Airbender.NativeMemoryTokens
