import Airbender.Review.Compiler.NativePublicSetup
import Airbender.Review.Helpers.Tables.Subword

namespace Airbender.Compiler.NativeProgramSetup
open Airbender.Reference.Compiler

/-- The public subword prefix includes fixed helpers and both program ROM views.
The decoder region follows that prefix. The remaining rows are zero padding. -/
noncomputable def subwordRows (decoder : List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (index : Nat) : List Source.BaseField :=
  if bounded : index < 13238273 then
    ((Verification.subwordNativeRow wordAt ⟨index, bounded⟩).map
      (fun value : Nat => (value : Source.BaseField))).toList
  else if index - 13238273 < 1048576 then
    ProgramSetup.packTagged 9 46
      (decoder[index - 13238273]?.getD (ProgramSetup.decoderPadding 8))
  else List.replicate 9 0

/-- Program setup rows include the subword halfword and byte ROM tables.
The other circuit families use their decoder and full-word ROM factory. -/
noncomputable def programRows (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) : ProgramLookupRows :=
  fun configuration group index =>
    match configuration with
    | .subwordMemoryUncached | .subwordMemoryCached =>
      if group.val = 0 then subwordRows (decoder configuration) wordAt index
      else retainedRows configuration group index
    | _ => rows decoder wordAt configuration group index

/-- Bind all unrolled program regions to public decoder columns and bytes. -/
noncomputable def unrolledProgramLookupRows (initial : Reference.RiscV.Sail.State)
    (columns : Trace.PooledFamily → List (List Source.BaseField)) : ProgramLookupRows :=
  programRows (unrolledDecoderColumns columns) (Trace.ROM.words initial)

end Airbender.Compiler.NativeProgramSetup
