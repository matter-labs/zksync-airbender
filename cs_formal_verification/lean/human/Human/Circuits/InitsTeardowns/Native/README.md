# Native initialization products

[Model.lean](Model.lean) gives the three native extension-gate forms and their memory-token encoding.
[Extract.lean](Extract.lean) selects the two RAM output dependency trees from the existing typed circuit.
It checks their producers, virtual setup inputs, set indices, memory columns and output map.
[Products.lean](Products.lean) defines the root products and the native memory bank of an instance.
It keeps the row products symbolic. It does not enumerate the native row domain.

| Claim | Result |
| --- | --- |
| `Airbender.InitsTeardowns.Native.StandaloneBindingClaim` | The standalone graph is extracted from the existing artifact. |
| `Airbender.InitsTeardowns.Native.UnifiedBindingClaim` | The inline unified graph is extracted from the existing artifact. |
| `Airbender.InitsTeardowns.Native.StandaloneSoundnessClaim` | Accepted standalone gates compute the products of the boot interface tokens. |
| `Airbender.InitsTeardowns.Native.UnifiedSoundnessClaim` | Accepted inline gates compute the products of the boot interface tokens. |
| `Airbender.InitsTeardowns.Native.StandaloneSatisfiableClaim` | An instance with checked windows meets the standalone gate premises. |
| `Airbender.InitsTeardowns.Native.UnifiedSatisfiableClaim` | An instance with checked windows meets the inline gate premises. |

The [final proofs](../../../../../proven/Proven/Final/Circuits/InitsTeardowns/NativeProducts.lean) use one generic tree and product argument.
The kernel checks both extraction bindings. The [import command](../../../Import/NativeRamProducts.lean) emits data only.
Its output must pass those bindings. Product equality does not prove a token permutation.
The extension-wire and product-challenge interfaces remain explicit.

The soundness claims state both products over `Witness.initTokens` and `Witness.teardownTokens`.
The machine boot interface uses the same token lists for its seeds and teardowns.
The native memory bank of an instance reads its assignment at a fixed column offset (0 standalone, 96 unified).
The [standalone token proof](../../../../../proven/Proven/InitsTeardowns/Native/Standalone.lean) and
[unified token proof](../../../../../proven/Proven/InitsTeardowns/Native/Unified.lean) check this offset against
the imported teardown memory placements. They use the checked public windows.

The EVM verifier pins the deployment window values through upstream fix #548.
The Rust full statement verifier also requires strictly increasing top bits below 64 across all instances.
Both conditions matter for the initialization-window fix.
The unified artifact has `2 ^ 23` rows and a high-limb window stride of `2 ^ 9`.
Its geometry permits 128 windows. The Rust verifier ceiling admits only 64.
Thus the accepted inline windows reach addresses below `2 ^ 31`.
This restriction comes from the verifier ceiling together with the circuit geometry.
