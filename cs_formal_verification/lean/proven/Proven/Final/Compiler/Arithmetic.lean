module
public import Proven.Compiler.NativeBindings.AddSub
public import Proven.Compiler.NativeBindings.Bigint
public import Proven.Compiler.NativeBindings.BlakeG
public import Proven.Compiler.NativeBindings.BlakeRound
public import Proven.Compiler.NativeBindings.JumpBranch
public import Proven.Compiler.NativeBindings.Keccak
public import Proven.Compiler.NativeBindings.MulDiv
public import Proven.Compiler.NativeBindings.ShiftBinop
public import Proven.Compiler.NativeBindings.SubwordMemory
public import Proven.Compiler.NativeBindings.Unified
public import Proven.Compiler.NativeBindings.WordMemory

@[expose] public section
namespace Airbender.Compiler

/-- Actual cached native equations preserve the imported arithmetic description. -/
theorem addSub_cached_arithmetic : AddSubCachedArithmeticClaim := NativeBindings.AddSub.arithmetic

/-- Actual cached native equations preserve the imported arithmetic description. -/
theorem bigint_cached_arithmetic : BigintCachedArithmeticClaim := NativeBindings.Bigint.arithmetic

/-- Actual cached native equations preserve the imported arithmetic description. -/
theorem blakeG_cached_arithmetic : BlakeGCachedArithmeticClaim := NativeBindings.BlakeG.arithmetic

/-- Actual cached native equations preserve the imported arithmetic description. -/
theorem blakeRound_cached_arithmetic : BlakeRoundCachedArithmeticClaim := NativeBindings.BlakeRound.arithmetic

/-- Actual cached native equations preserve the imported arithmetic description. -/
theorem jumpBranch_cached_arithmetic : JumpBranchCachedArithmeticClaim := NativeBindings.JumpBranch.arithmetic

/-- Actual cached native equations preserve the imported arithmetic description. -/
theorem keccak_cached_arithmetic : KeccakCachedArithmeticClaim := NativeBindings.Keccak.arithmetic

/-- Actual cached native equations preserve the imported arithmetic description. -/
theorem mulDiv_cached_arithmetic : MulDivCachedArithmeticClaim := NativeBindings.MulDiv.arithmetic

/-- Actual cached native equations preserve the imported arithmetic description. -/
theorem shiftBinop_cached_arithmetic : ShiftBinopCachedArithmeticClaim := NativeBindings.ShiftBinop.arithmetic

/-- Actual cached native equations preserve the imported arithmetic description. -/
theorem subwordMemory_cached_arithmetic : SubwordMemoryCachedArithmeticClaim := NativeBindings.SubwordMemory.arithmetic

/-- Actual cached native equations preserve the imported arithmetic description. -/
theorem unified_cached_arithmetic : UnifiedCachedArithmeticClaim := NativeBindings.Unified.arithmetic

/-- Actual cached native equations preserve the imported arithmetic description. -/
theorem wordMemory_cached_arithmetic : WordMemoryCachedArithmeticClaim := NativeBindings.WordMemory.arithmetic

end Airbender.Compiler
