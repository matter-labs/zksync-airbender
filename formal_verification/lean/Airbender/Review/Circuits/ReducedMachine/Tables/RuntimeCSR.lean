import Airbender.Import.RuntimeCSRSetup

namespace Airbender.ReducedMachine.NativeRuntimeCSR
set_option autoImplicit false
-- Separately exported actual runtime region; the original full pool is unchanged.
import_native_runtime_csr data from "artifacts/setup/reduced-runtime-csr-native.json"

def supported (key : Nat) : Nat := if key = 1984 ∨ key = 1991 then 1 else 0
def delegated (key : Nat) : Nat := if key = 1991 then 1 else 0
def row (key : Nat) : Vector Nat 4 := #v[key,supported key,delegated key,25]
def Contains (query : Vector (ZMod mersenne31Modulus) 4) : Prop := ∃ i : Fin data.length, query = data.row i
end Airbender.ReducedMachine.NativeRuntimeCSR
