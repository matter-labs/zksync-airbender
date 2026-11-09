import Airbender.Review.Trace.Families.ReducedMachine.ControlCaller
import Airbender.Proofs.ReducedMachine.NativeControlSource

namespace Airbender.NativeControlCallerProofs
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlFold Airbender.NativeControlLastReset Airbender.NativeControlSource Airbender.NativeControlCaller
open Airbender.NativeDelegationSupport (callerRows callerKey workerKey)
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Generic unique-partner composition before native data. -/
theorem unique_compose {A B : Type} (first : A → Prop) (second : A → B → Prop)
    (one : ∃! a, first a) (next : ∀ a, first a → ∃! b, second a b) :
    ∃! b, ∃ a, first a ∧ second a b := by
  obtain ⟨a,ha,onlyA⟩ := one
  obtain ⟨b,hb,onlyB⟩ := next a ha
  refine ⟨b,⟨a,ha,hb⟩,?_⟩
  rintro other ⟨a',ha',hb'⟩
  have same := onlyA a' ha'
  subst a'
  exact onlyB other hb'

theorem provenance {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeCallerCount.Effects batch workers inputs) {edge : Token × Token}
    (selected : WorkerEdge workers edge) : ∃ caller, CallerAt batch.main.proofs workers edge caller := by
  obtain ⟨source,matched,_⟩ := Airbender.NativeControlSourceProofs.source_unique prior.prior.clocksUnique selected
  have present : workerKey (Airbender.NativeTokenLedger.workerRows workers)[source.val] ∈
      Airbender.NativeDelegationKeyAccounting.keys workers := by
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨List.getElem_mem source.isLt,by simpa using matched.1⟩,rfl⟩
  obtain ⟨caller,member,one,key⟩ := prior.workerCaller _ present
  obtain ⟨index,same⟩ := Airbender.NativeControlLastResetProofs.member_position member
  have equal : (callerRows batch.main.proofs)[index.val] = caller := by simpa only [List.get_eq_getElem] using same
  exact ⟨index,source,matched,by simpa only [equal] using one,by simpa only [equal] using key⟩


/-- Exact raw four-key fields, not physical caller activity or original CSR execution. -/
theorem caller_fields {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {edge : Token × Token} {caller : Fin (callerRows proofs).length}
    (matched : CallerAt proofs workers edge caller) :
    ∃ source : Fin (Airbender.NativeTokenLedger.workerRows workers).length, SourceAt workers edge source ∧
      (callerRows proofs)[caller.val] 92 = 1 ∧ (callerRows proofs)[caller.val] 94 = 1991 ∧
      (callerRows proofs)[caller.val] 93 = (Airbender.NativeTokenLedger.workerRows workers)[source.val] 1 ∧
      ((callerRows proofs)[caller.val] 2 + 3,(callerRows proofs)[caller.val] 3) = edge.2.time := by
  obtain ⟨source,atSource,request,key⟩ := matched
  refine ⟨source,atSource,request,congrArg CSRArgumentKey.kind key,congrArg CSRArgumentKey.abi key,?_⟩
  rw [atSource.2,Airbender.NativeActiveWorkerClockProofs.write_clock]
  exact Prod.ext (congrArg CSRArgumentKey.low key) (congrArg CSRArgumentKey.high key)

theorem caller_unique {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (clocks : Airbender.NativeDelegationKeyAccounting.Effects batch workers inputs)
    (partners : Airbender.NativeCallerPosition.Matching batch workers) {edge : Token × Token}
    (selected : WorkerEdge workers edge) : ∃! caller, CallerAt batch.main.proofs workers edge caller := by
  apply unique_compose (SourceAt workers edge) (fun source (caller : Fin (callerRows batch.main.proofs).length) =>
    (callerRows batch.main.proofs)[caller.val] 92 = 1 ∧
      callerKey (callerRows batch.main.proofs)[caller.val] = workerKey (Airbender.NativeTokenLedger.workerRows workers)[source.val])
    (Airbender.NativeControlSourceProofs.source_unique clocks.clocksUnique selected)
  intro source matched
  exact partners.2 source matched.1

theorem path_matching {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {path : List Token}
    (clocks : Airbender.NativeDelegationKeyAccounting.Effects batch workers inputs)
    (partners : Airbender.NativeCallerPosition.Matching batch workers)
    (sources : Airbender.NativeControlSource.Matching workers path) : PathMatching batch.main.proofs workers path := by
  refine ⟨fun _ selected => caller_unique clocks partners selected,?_⟩
  intro caller active
  obtain ⟨source,matched,onlySource⟩ := partners.1 caller active
  obtain ⟨index,atSource,onlyIndex⟩ := sources.2 source matched.1
  refine ⟨index,⟨source,atSource,active,matched.2⟩,?_⟩
  rintro other ⟨source',atSource',request,key⟩
  have same := onlySource source' ⟨atSource'.1,key⟩
  subst source'
  exact onlyIndex other atSource'

theorem segment_count {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} (partners : Airbender.NativeCallerPosition.Matching batch workers)
    (path : List Token) (target : Fin path.length) (start : Fin (target.val+1)) :
    sourceCount workers path target start = callerCount batch.main.proofs workers path target start := by
  classical
  change Fintype.card {source // SegmentSource workers path target start source} =
    Fintype.card {caller // SegmentCaller batch.main.proofs workers path target start caller}
  apply Airbender.NativeControlSourceProofs.matching_card (fun source caller =>
    (callerRows batch.main.proofs)[caller.val.val] 92 = 1 ∧
      callerKey (callerRows batch.main.proofs)[caller.val.val] = workerKey (Airbender.NativeTokenLedger.workerRows workers)[source.val.val])
  · intro source
    obtain ⟨index,atSource⟩ := source.property
    obtain ⟨caller,matched,only⟩ := partners.2 source.val atSource.1
    refine ⟨⟨caller,index,source.val,atSource,matched⟩,matched,?_⟩
    intro other hm
    exact Subtype.ext (only other.val hm)
  · intro caller
    obtain ⟨index,source,atSource,request,key⟩ := caller.property
    obtain ⟨chosen,matched,only⟩ := partners.1 caller.val request
    have same : source = chosen := only source ⟨atSource.1,key⟩
    subst chosen
    refine ⟨⟨source,index,atSource⟩,⟨request,key⟩,?_⟩
    intro other hm
    have am : (Airbender.NativeTokenLedger.workerRows workers)[other.val.val] constraintsABI.multiplicity = 1 := by
      obtain ⟨_,actual⟩ := other.property
      exact actual.1
    exact Subtype.ext (only other.val ⟨am,hm.2⟩)

theorem caller_count_bound {Setup R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R))
    (workers : WorkerBatch Setup R) (path : List Token) (target : Fin path.length) (start : Fin (target.val+1)) :
    callerCount proofs workers path target start ≤ (callerRows proofs).length := by
  classical
  simpa only [callerCount,Fintype.card_fin] using Fintype.card_subtype_le (SegmentCaller proofs workers path target start)


theorem caller_member {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {edge : Token × Token} {caller : Fin (callerRows proofs).length}
    (matched : CallerAt proofs workers edge caller) : WorkerEdge workers edge := by
  obtain ⟨source,atSource,_,_⟩ := matched
  exact Airbender.NativeControlSourceProofs.source_member atSource

theorem caller_fold {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {path : List Token}
    (history : History batch.main.proofs workers inputs path)
    (clocks : Airbender.NativeDelegationKeyAccounting.Effects batch workers inputs)
    (partners : Airbender.NativeCallerPosition.Matching batch workers)
    (target : Fin path.length) (start : Fin (target.val+1)) (fold : Fold workers path target start) :
    limbs (path.get target) = iterate advance (callerCount batch.main.proofs workers path target start)
      (limbs (path.get ⟨start.val,by have := start.isLt; have := target.isLt; omega⟩)) := by
  have result := Airbender.NativeControlSourceProofs.source_fold history clocks.clocksUnique target start fold
  simpa only [segment_count partners path target start] using result

theorem from_prior {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
    {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (prior : Airbender.NativeControlSource.Effects before publicSetup batch workers inputs) :
    Airbender.NativeControlCaller.Effects before publicSetup batch workers inputs := by
  have positions : Airbender.NativeCallerPosition.Effects batch workers inputs := prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.prior
  obtain ⟨path,history,origins,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,results,workersAt,sources,counts⟩ := prior.path
  refine ⟨prior,path,history,origins,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,results,workersAt,sources,counts,?_,?_⟩
  · intro _ selected; exact provenance positions.prior selected
  · rcases positions.matching_or_large with partners | large
    · left
      exact ⟨path_matching positions.prior.prior partners sources,
        fun target start => (counts target start).trans (segment_count partners path target start)⟩
    · exact Or.inr large

theorem counted {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) :
    Airbender.NativeControlCaller.Effects before publicSetup batch workers inputs :=
  from_prior (Airbender.NativeControlSourceProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity)
end Airbender.NativeControlCallerProofs
