# Native initialization products

[Model.lean](Model.lean) gives the three native extension-gate forms and their memory-token encoding.
[Extract.lean](Extract.lean) selects the two RAM output dependency trees from the existing typed circuit.
It checks their producers, virtual setup inputs, set indices, memory columns and output map.
[Products.lean](Products.lean) keeps the row products symbolic. It does not enumerate the native row domain.

| Claim | Result |
| --- | --- |
| `Airbender.InitsTeardowns.Native.StandaloneBindingClaim` | The standalone graph is extracted from the existing artifact. |
| `Airbender.InitsTeardowns.Native.UnifiedBindingClaim` | The inline unified graph is extracted from the existing artifact. |
| `Airbender.InitsTeardowns.Native.StandaloneSoundnessClaim` | Accepted standalone gates compute both complete token products. |
| `Airbender.InitsTeardowns.Native.UnifiedSoundnessClaim` | Accepted inline gates compute both complete token products. |
| `Airbender.InitsTeardowns.Native.StandaloneSatisfiableClaim` | The standalone gate premises admit an assignment. |
| `Airbender.InitsTeardowns.Native.UnifiedSatisfiableClaim` | The inline gate premises admit an assignment. |

The [final proofs](../../../../../proven/Proven/Final/Circuits/InitsTeardowns/NativeProducts.lean) use one generic tree and product argument.
The kernel checks both extraction bindings. The [import command](../../../Import/NativeRamProducts.lean) emits data only.
Its output must pass those bindings. Product equality does not prove a token permutation.
The raw-column and product-challenge interfaces remain explicit.

The EVM verifier pins the deployment window values through upstream fix #548.
The Rust full statement verifier also requires strictly increasing top bits below 64 across all instances.
Both conditions matter for the initialization-window fix.
The unified artifact has `2 ^ 23` rows and a high-limb window stride of `2 ^ 9`.
Its geometry permits 128 windows. The Rust verifier ceiling admits only 64.
Thus the accepted inline windows reach addresses below `2 ^ 31`.
This restriction comes from the verifier ceiling together with the circuit geometry.
