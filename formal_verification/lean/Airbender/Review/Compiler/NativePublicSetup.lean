import Airbender.Data.Compiler.NativeProgramSetup
import Airbender.Review.Compiler.PublicProgramSetup

namespace Airbender.Compiler.NativeProgramSetup

/-- The cached configuration selects its public family columns. -/
def pooledFamily : Configuration → Option Trace.PooledFamily
  | .addSubCached => some .addSub
  | .jumpBranchCached => some .jumpBranchSlt
  | .mulDivCached => some .mulDiv
  | .shiftBinopCached => some .shiftBinop
  | .wordMemoryCached => some .wordMemory
  | .subwordMemoryCached => some .subwordMemory
  | _ => none

def unrolledDecoderColumns (columns : Trace.PooledFamily → List (List Source.BaseField)) :
    Configuration → List (List Source.BaseField) :=
  fun configuration => (pooledFamily configuration).map columns |>.getD []

def unifiedDecoderColumns (columns : List (List Source.BaseField)) :
    Configuration → List (List Source.BaseField)
  | .unifiedCached => columns
  | _ => []

/-- Bind native program rows to public decoder columns and initial Sail bytes. -/
noncomputable def unrolledLookupRows (initial : Reference.RiscV.Sail.State)
    (columns : Trace.PooledFamily → List (List Source.BaseField)) : ProgramLookupRows :=
  rows (unrolledDecoderColumns columns) (Trace.ROM.words initial)

noncomputable def unifiedLookupRows (initial : Reference.RiscV.Sail.State)
    (columns : List (List Source.BaseField)) : ProgramLookupRows :=
  rows (unifiedDecoderColumns columns) (Trace.ROM.words initial)

end Airbender.Compiler.NativeProgramSetup
