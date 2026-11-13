module
public import Proven.Compiler.NativeSatisfiable.AddSub
public import Proven.Compiler.NativeSatisfiable.Bigint
public import Proven.Compiler.NativeSatisfiable.BlakeG
public import Proven.Compiler.NativeSatisfiable.BlakeRound
public import Proven.Compiler.NativeSatisfiable.JumpBranch
public import Proven.Compiler.NativeSatisfiable.Keccak
public import Proven.Compiler.NativeSatisfiable.MulDiv
public import Proven.Compiler.NativeSatisfiable.ShiftBinop
public import Proven.Compiler.NativeSatisfiable.SubwordMemory
public import Proven.Compiler.NativeSatisfiable.Unified
public import Proven.Compiler.NativeSatisfiable.WordMemory
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

namespace Airbender.Compiler

/-- The cached native arithmetic premises have a complete physical witness. -/
theorem addSub_cached_arithmetic_satisfiable : AddSubCachedArithmeticSatisfiableClaim := NativeSatisfiable.AddSub.witness

/-- The cached native arithmetic premises have a complete physical witness. -/
theorem bigint_cached_arithmetic_satisfiable : BigintCachedArithmeticSatisfiableClaim := NativeSatisfiable.Bigint.witness

/-- The cached native arithmetic premises have a complete physical witness. -/
theorem blakeG_cached_arithmetic_satisfiable : BlakeGCachedArithmeticSatisfiableClaim := NativeSatisfiable.BlakeG.witness

/-- The cached native arithmetic premises have a complete physical witness. -/
theorem blakeRound_cached_arithmetic_satisfiable : BlakeRoundCachedArithmeticSatisfiableClaim := NativeSatisfiable.BlakeRound.witness

/-- The cached native arithmetic premises have a complete physical witness. -/
theorem jumpBranch_cached_arithmetic_satisfiable : JumpBranchCachedArithmeticSatisfiableClaim := NativeSatisfiable.JumpBranch.witness

/-- The cached native arithmetic premises have a complete physical witness. -/
theorem keccak_cached_arithmetic_satisfiable : KeccakCachedArithmeticSatisfiableClaim := NativeSatisfiable.Keccak.witness

/-- The cached native arithmetic premises have a complete physical witness. -/
theorem mulDiv_cached_arithmetic_satisfiable : MulDivCachedArithmeticSatisfiableClaim := NativeSatisfiable.MulDiv.witness

/-- The cached native arithmetic premises have a complete physical witness. -/
theorem shiftBinop_cached_arithmetic_satisfiable : ShiftBinopCachedArithmeticSatisfiableClaim := NativeSatisfiable.ShiftBinop.witness

/-- The cached native arithmetic premises have a complete physical witness. -/
theorem subwordMemory_cached_arithmetic_satisfiable : SubwordMemoryCachedArithmeticSatisfiableClaim := NativeSatisfiable.SubwordMemory.witness

/-- The cached native arithmetic premises have a complete physical witness. -/
theorem unified_cached_arithmetic_satisfiable : UnifiedCachedArithmeticSatisfiableClaim := NativeSatisfiable.Unified.witness

/-- The cached native arithmetic premises have a complete physical witness. -/
theorem wordMemory_cached_arithmetic_satisfiable : WordMemoryCachedArithmeticSatisfiableClaim := NativeSatisfiable.WordMemory.witness

end Airbender.Compiler
