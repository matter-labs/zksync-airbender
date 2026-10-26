import Airbender.Import.GKRProtocol.Source
import Airbender.Import.Compiler.Arithmetic.AddSubCached
import Airbender.Import.Compiler.Arithmetic.AddSubUncached
import Airbender.Import.Compiler.Arithmetic.BigintCached
import Airbender.Import.Compiler.Arithmetic.BigintUncached
import Airbender.Import.Compiler.Arithmetic.BlakeGCached
import Airbender.Import.Compiler.Arithmetic.BlakeGUncached
import Airbender.Import.Compiler.Arithmetic.BlakeRoundCached
import Airbender.Import.Compiler.Arithmetic.BlakeRoundUncached
import Airbender.Import.Compiler.Arithmetic.JumpBranchCached
import Airbender.Import.Compiler.Arithmetic.JumpBranchUncached
import Airbender.Import.Compiler.Arithmetic.KeccakCached
import Airbender.Import.Compiler.Arithmetic.KeccakUncached
import Airbender.Import.Compiler.Arithmetic.MulDivCached
import Airbender.Import.Compiler.Arithmetic.MulDivUncached
import Airbender.Import.Compiler.Arithmetic.ShiftBinopCached
import Airbender.Import.Compiler.Arithmetic.ShiftBinopUncached
import Airbender.Import.Compiler.Arithmetic.SubwordMemoryCached
import Airbender.Import.Compiler.Arithmetic.SubwordMemoryUncached
import Airbender.Import.Compiler.Arithmetic.UnifiedCached
import Airbender.Import.Compiler.Arithmetic.UnifiedUncached
import Airbender.Import.Compiler.Arithmetic.WordMemoryCached
import Airbender.Import.Compiler.Arithmetic.WordMemoryUncached

namespace Airbender.Compiler

def arithmeticCapture : Configuration → CapturedArithmetic Source.BaseField
  | .addSubCached => ⟨_, _, Native.AddSubCached.native.artifact, Native.AddSubCached.native.selected⟩
  | .addSubUncached => ⟨_, _, Native.AddSubUncached.native.artifact, Native.AddSubUncached.native.selected⟩
  | .bigintCached => ⟨_, _, Native.BigintCached.native.artifact, Native.BigintCached.native.selected⟩
  | .bigintUncached => ⟨_, _, Native.BigintUncached.native.artifact, Native.BigintUncached.native.selected⟩
  | .blakeGCached => ⟨_, _, Native.BlakeGCached.native.artifact, Native.BlakeGCached.native.selected⟩
  | .blakeGUncached => ⟨_, _, Native.BlakeGUncached.native.artifact, Native.BlakeGUncached.native.selected⟩
  | .blakeRoundCached => ⟨_, _, Native.BlakeRoundCached.native.artifact, Native.BlakeRoundCached.native.selected⟩
  | .blakeRoundUncached => ⟨_, _, Native.BlakeRoundUncached.native.artifact, Native.BlakeRoundUncached.native.selected⟩
  | .jumpBranchCached => ⟨_, _, Native.JumpBranchCached.native.artifact, Native.JumpBranchCached.native.selected⟩
  | .jumpBranchUncached => ⟨_, _, Native.JumpBranchUncached.native.artifact, Native.JumpBranchUncached.native.selected⟩
  | .keccakCached => ⟨_, _, Native.KeccakCached.native.artifact, Native.KeccakCached.native.selected⟩
  | .keccakUncached => ⟨_, _, Native.KeccakUncached.native.artifact, Native.KeccakUncached.native.selected⟩
  | .mulDivCached => ⟨_, _, Native.MulDivCached.native.artifact, Native.MulDivCached.native.selected⟩
  | .mulDivUncached => ⟨_, _, Native.MulDivUncached.native.artifact, Native.MulDivUncached.native.selected⟩
  | .shiftBinopCached => ⟨_, _, Native.ShiftBinopCached.native.artifact, Native.ShiftBinopCached.native.selected⟩
  | .shiftBinopUncached => ⟨_, _, Native.ShiftBinopUncached.native.artifact, Native.ShiftBinopUncached.native.selected⟩
  | .subwordMemoryCached => ⟨_, _, Native.SubwordMemoryCached.native.artifact, Native.SubwordMemoryCached.native.selected⟩
  | .subwordMemoryUncached => ⟨_, _, Native.SubwordMemoryUncached.native.artifact, Native.SubwordMemoryUncached.native.selected⟩
  | .unifiedCached => ⟨_, _, Native.UnifiedCached.native.artifact, Native.UnifiedCached.native.selected⟩
  | .unifiedUncached => ⟨_, _, Native.UnifiedUncached.native.artifact, Native.UnifiedUncached.native.selected⟩
  | .wordMemoryCached => ⟨_, _, Native.WordMemoryCached.native.artifact, Native.WordMemoryCached.native.selected⟩
  | .wordMemoryUncached => ⟨_, _, Native.WordMemoryUncached.native.artifact, Native.WordMemoryUncached.native.selected⟩

end Airbender.Compiler
