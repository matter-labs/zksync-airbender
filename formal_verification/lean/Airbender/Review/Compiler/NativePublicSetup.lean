import Airbender.Data.Compiler.NativeProgramSetup
import Airbender.Review.Compiler.PublicProgramSetup

namespace Airbender.Compiler.NativeProgramSetup

/-- The native cache modes select the same public family columns. -/
def pooledFamily : Configuration → Option Trace.PooledFamily
  | .addSubUncached | .addSubCached => some .addSub
  | .jumpBranchUncached | .jumpBranchCached => some .jumpBranchSlt
  | .mulDivUncached | .mulDivCached => some .mulDiv
  | .shiftBinopUncached | .shiftBinopCached => some .shiftBinop
  | .wordMemoryUncached | .wordMemoryCached => some .wordMemory
  | .subwordMemoryUncached | .subwordMemoryCached => some .subwordMemory
  | _ => none

def unrolledDecoderColumns (columns : Trace.PooledFamily → List (List Source.BaseField)) :
    Configuration → List (List Source.BaseField) :=
  fun configuration => (pooledFamily configuration).map columns |>.getD []

def unifiedDecoderColumns (columns : List (List Source.BaseField)) :
    Configuration → List (List Source.BaseField)
  | .unifiedUncached | .unifiedCached => columns
  | _ => []

/-- Bind native program rows to public decoder columns and initial Sail bytes. -/
noncomputable def unrolledLookupRows (initial : Reference.RiscV.Sail.State)
    (columns : Trace.PooledFamily → List (List Source.BaseField)) : ProgramLookupRows :=
  rows (unrolledDecoderColumns columns) (Trace.ROM.words initial)

noncomputable def unifiedLookupRows (initial : Reference.RiscV.Sail.State)
    (columns : List (List Source.BaseField)) : ProgramLookupRows :=
  rows (unifiedDecoderColumns columns) (Trace.ROM.words initial)

end Airbender.Compiler.NativeProgramSetup
