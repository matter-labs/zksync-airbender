# Native initialization products

[Model.lean](Model.lean) gives the extracted wiring types, the raw memory bank and the memory-token encoding.
[Extract.lean](Extract.lean) selects the two RAM output dependency trees from the existing typed circuit.
It checks their producers, virtual setup inputs, set indices, memory columns and output map.
[Products.lean](Products.lean) defines the output products, the virtual setup address limbs of a row and the native
memory bank of an instance. It keeps the row products symbolic. It does not enumerate the native row domain.
The compiled semantics of the initialization pair is `NativeMemory.InitializationHolds`
([NativeMemory.lean](../../../Compiler/NativeMemory.lean)). It follows the verifier
(`gkr_eval_ir/src/lower/memory.rs`): the tuple of set `k` adds the public top bits of set `k` to the high address
limb, shifted left as a 32-bit unsigned word by `InitsTeardowns.topShift` of the bound layout.

| Claim | Result |
| --- | --- |
| `Airbender.InitsTeardowns.Native.StandaloneBindingClaim` | The standalone graph is extracted from the existing artifact. |
| `Airbender.InitsTeardowns.Native.UnifiedBindingClaim` | The cached unified capture has the initialization layout, and its inline graph is extracted from it. |
| `Airbender.InitsTeardowns.Native.StandaloneSoundnessClaim` | Compiled acceptance of the standalone capture gives the products of the boot interface tokens on its output wires. |
| `Airbender.InitsTeardowns.Native.UnifiedSoundnessClaim` | Compiled acceptance of the cached unified capture gives the products of the boot interface tokens on its output wires. |
| `Airbender.InitsTeardowns.Native.StandaloneSatisfiableClaim` | An instance with checked windows meets the compiled acceptance premises of the standalone capture. |
| `Airbender.InitsTeardowns.Native.UnifiedSatisfiableClaim` | An instance with checked windows meets the compiled acceptance premises of the cached unified capture. |

The [final proofs](../../../../../proven/Proven/Final/Circuits/InitsTeardowns/NativeProducts.lean) use one generic tree and product argument.
The kernel checks both extraction bindings. The unified binding reads the cached capture `Captures.Unified.imported`,
the circuit that production proves, and checks its initialization layout as well.
The soundness claims take compiled acceptance on every row of the bound circuit. The virtual setup wires of a row are
the setup address limbs that the verifier computes (`withSetupAddresses`); they are not premises.
The [bridge proof](../../../../../proven/Proven/InitsTeardowns/Native/Bridge.lean) checks in the kernel that each
extracted gate is the decoded form of a compiled relation of the bound circuit, and that the extracted window stride
is the compiled window shift. The CPU memory claims of the cached capture read no initialization output.
The [import command](../../../Import/NativeRamProducts.lean) emits data only.
Its output must pass those bindings. Product equality does not prove a token permutation.
The extension wires and the product challenges are universally quantified.

The soundness claims state both products over `Witness.initTokens` and `Witness.teardownTokens`.
The machine boot interface uses the same token lists for its seeds and teardowns.
The native memory bank of an instance reads its assignment at a fixed column offset (0 standalone, 96 unified).
The [standalone token proof](../../../../../proven/Proven/InitsTeardowns/Native/Standalone.lean) and
[unified token proof](../../../../../proven/Proven/InitsTeardowns/Native/Unified.lean) check this offset against
the imported teardown memory placements. They use the checked public windows.

The EVM verifier pins the deployment window values through upstream fix #548.
The Rust full statement verifier also requires strictly increasing top bits below 64 across all instances.
Both conditions matter for the initialization-window fix.
The unified capture has `2 ^ 23` rows and a high-limb window stride of `2 ^ 9`.
Its geometry permits 128 windows. The Rust verifier ceiling admits only 64.
Thus the accepted inline windows reach addresses below `2 ^ 31`.
This restriction comes from the verifier ceiling together with the circuit geometry.
