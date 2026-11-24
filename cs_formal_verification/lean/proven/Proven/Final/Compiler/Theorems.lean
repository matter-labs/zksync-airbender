module
public import Proven.Compiler.Bindings.AddSub
public import Proven.Compiler.Bindings.Bigint
public import Proven.Compiler.Bindings.BlakeG
public import Proven.Compiler.Bindings.BlakeRound
public import Proven.Compiler.Bindings.JumpBranch
public import Proven.Compiler.Bindings.Keccak
public import Proven.Compiler.Bindings.MulDiv
public import Proven.Compiler.Bindings.ShiftBinop
public import Proven.Compiler.Bindings.SubwordMemory
public import Proven.Compiler.Bindings.Unified
public import Proven.Compiler.Bindings.WordMemory

@[expose] public section

namespace Airbender.Compiler

/-- The cached capture retains the reviewed constraint description. -/
theorem addSub_cached_description : AddSubCachedDescriptionClaim := Bindings.AddSub.cached_description

/-- The cached capture retains the reviewed constraint description. -/
theorem bigint_cached_description : BigintCachedDescriptionClaim := Bindings.Bigint.cached_description

/-- The cached capture retains the reviewed constraint description. -/
theorem blakeG_cached_description : BlakeGCachedDescriptionClaim := Bindings.BlakeG.cached_description

/-- The cached capture retains the reviewed constraint description. -/
theorem blakeRound_cached_description : BlakeRoundCachedDescriptionClaim := Bindings.BlakeRound.cached_description

/-- The cached capture retains the reviewed constraint description. -/
theorem jumpBranch_cached_description : JumpBranchCachedDescriptionClaim := Bindings.JumpBranch.cached_description

/-- The cached capture retains the reviewed constraint description. -/
theorem keccak_cached_description : KeccakCachedDescriptionClaim := Bindings.Keccak.cached_description

/-- The cached capture retains the reviewed constraint description. -/
theorem mulDiv_cached_description : MulDivCachedDescriptionClaim := Bindings.MulDiv.cached_description

/-- The cached capture retains the reviewed constraint description. -/
theorem shiftBinop_cached_description : ShiftBinopCachedDescriptionClaim := Bindings.ShiftBinop.cached_description

/-- The cached capture retains the reviewed constraint description. -/
theorem subwordMemory_cached_description : SubwordMemoryCachedDescriptionClaim := Bindings.SubwordMemory.cached_description

/-- The cached capture retains the reviewed constraint description. -/
theorem unified_cached_description : UnifiedCachedDescriptionClaim := Bindings.Unified.cached_description

/-- The cached capture retains the reviewed constraint description. -/
theorem wordMemory_cached_description : WordMemoryCachedDescriptionClaim := Bindings.WordMemory.cached_description

end Airbender.Compiler
