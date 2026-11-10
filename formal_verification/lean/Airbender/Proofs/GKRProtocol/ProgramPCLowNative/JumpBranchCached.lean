import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.JumpBranchCached
import Airbender.Proofs.Constraints
import Airbender.Proofs.GKRProtocol.ProgramConstraintsNative.JumpBranchCached
import Airbender.Proofs.Tables.DecoderPCLow

namespace Airbender.Compiler.ProgramPCLowNative.JumpBranchCached
open Airbender Airbender.Compiler Airbender.Compiler.PooledRowNative.JumpBranchCached
set_option warningAsError true
set_option Elab.async false


theorem final_pc_low
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .jumpBranchCached group index.val) input) (setup : Trace.PooledSetup babyBearModulus) :
    (inputRow input).finish.word.lo < 65536 :=
  Trace.NativeDecoder.Proofs.pooled_final_pc_low (by decide +kernel) (inputRow input) setup
    (ProgramConstraintsNative.JumpBranchCached.input_constraints decoder wordAt input arguments setup)

end Airbender.Compiler.ProgramPCLowNative.JumpBranchCached
