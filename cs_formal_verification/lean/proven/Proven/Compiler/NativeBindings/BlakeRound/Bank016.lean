module
public import Proven.Compiler.NativeBridge
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCached
@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.BlakeRound
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768
/-- This bank coordinate has a checked literal lookup. -/
theorem coordinate853 : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address ⟨853, by decide⟩ = GKRAddress.Cached 0 172 :=
  bank_lookup Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.addresses (by decide) ⟨853, by decide⟩ (GKRAddress.Cached 0 172) (by cbv)
/-- This bank coordinate has a checked literal lookup. -/
theorem coordinate854 : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address ⟨854, by decide⟩ = GKRAddress.Cached 0 173 :=
  bank_lookup Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.addresses (by decide) ⟨854, by decide⟩ (GKRAddress.Cached 0 173) (by cbv)
/-- This bank coordinate has a checked literal lookup. -/
theorem coordinate855 : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address ⟨855, by decide⟩ = GKRAddress.Cached 0 174 :=
  bank_lookup Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.addresses (by decide) ⟨855, by decide⟩ (GKRAddress.Cached 0 174) (by cbv)
/-- This bank coordinate has a checked literal lookup. -/
theorem coordinate856 : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address ⟨856, by decide⟩ = GKRAddress.Cached 0 175 :=
  bank_lookup Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.addresses (by decide) ⟨856, by decide⟩ (GKRAddress.Cached 0 175) (by cbv)
/-- This bank coordinate has a checked literal lookup. -/
theorem coordinate857 : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address ⟨857, by decide⟩ = GKRAddress.Cached 0 176 :=
  bank_lookup Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.addresses (by decide) ⟨857, by decide⟩ (GKRAddress.Cached 0 176) (by cbv)
end Airbender.Compiler.NativeBindings.BlakeRound
