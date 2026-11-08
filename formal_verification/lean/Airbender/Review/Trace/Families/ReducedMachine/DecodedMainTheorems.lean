import Airbender.Proofs.ReducedMachine.NativeDecodedMain

namespace Airbender.NativeDecodedMain
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native

/-- Original public image membership derives the actual non-CSR domains and
    every assertion/query in the retained fixed BODY. No whole-table equivalence
    or expected per-row mask is supplied; CSR is outside this ordinary scope. -/
theorem native_public_ordinary_body {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup UnifiedMode} {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w)
      (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    (∀ slot : Fin 4, (lookupSelectors w)[slot] ≠ 25) ∧
      FlatOperation.ConstraintsHoldFlat (environment w)
        (importedConstraints Airbender.ReducedMachine.NativeFixed.table) :=
  NativeDecodedQueryDomainProofs.public_body image holds member

/-- Exact original decoded fields derive the ordinary-or-CSR local write law.
    Initialization will supply earlier read bounds; this law does not assume them. -/
theorem native_decoded_main_write_rule (row : Row mersenne31Modulus NativeReducedFamily)
    {entry : Airbender.NativeCallerDecoder.Program}
    (holds : FlatOperation.ConstraintsHoldFlat (environment row.assignment)
      (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table))
    (fields : Airbender.NativeCallerDecoder.decoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) (aligned : row.start.word.lo % 4 = 0) : RowWriteRule row :=
  NativeDecodedQueryDomainProofs.main_write_rule row holds fields query aligned

/-- SAME complete counted source plus the old named logical lookup boundary.
    Public image supplies all row fields and PC alignment as conclusions. -/
theorem native_counted_main_write_rules {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch) : Effects batch :=
  NativeDecodedQueryDomainProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups
end Airbender.NativeDecodedMain
