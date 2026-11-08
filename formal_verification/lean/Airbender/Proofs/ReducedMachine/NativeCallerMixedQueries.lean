import Airbender.Review.Circuits.ReducedMachine.CallerMixedQueries
import Airbender.Proofs.ReducedMachine.NativeCallerRequests
import Airbender.Proofs.ReducedMachine.NativeDelegationKeyAccounting

namespace Airbender.NativeCallerMixedQueryProofs
open Airbender.NativeCallerRequests (F)
open Airbender.NativeCallerMixedQueries Airbender.Verification Airbender.ReducedMachine.Native
open Airbender.Trace
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private def linearSyntax (terms : List (Int × Nat)) : Expression F :=
  terms.foldl (fun e t => .add e (.mul (.mul (.const 1) (.const (t.1 : F))) (.var ⟨t.2⟩))) (.add (.const 0) (.const 0))
private def quadraticSyntax (row : List (Int × Nat) × List (Int × Nat × Nat)) : Expression F :=
  row.2.foldl (fun e t => .add e (.mul (.mul (.mul (.const 1) (.const (t.1 : F))) (.var ⟨t.2.1⟩)) (.var ⟨t.2.2⟩)))
    (.add (.const 0) (linearSyntax row.1))
private def sourceData : Vector (List (Int × Nat) × List (Int × Nat × Nat)) 16 := #v[
  ([(-1,100)],[(1,9,24),(1,61,25),(1,61,31),(1,62,27),(1,69,23),(1,22,55),(1,29,47)]),
  ([(-1,101)],[(1,22,58),(1,23,64),(1,24,64),(1,25,64),(1,27,64),(1,29,64),(1,31,64)]),
  ([(-1,102)],[(1,22,64),(1,23,65),(1,24,65),(1,25,65),(1,27,65),(1,29,65),(1,31,65)]),
  ([(17,23),(25,24),(17,25),(23,27),(47,29),(18,31),(-1,103)],[(1,11,22)]),
  ([(-1,104)],[(1,11,23),(1,61,27),(1,62,31),(-8388608,22,55),(8388608,22,35),(8,23,63),(16,23,68),(32,23,56),(64,23,59),(65536,27,65),(2097152,29,33),(65536,29,64),(1,29,35)]),
  ([(-1,105)],[(8388608,22,47),(-8388608,22,58),(1,23,66),(1,27,66),(1,29,66),(1,31,66)]),
  ([(-1,106)],[(1,22,65),(1,23,67),(1,27,67),(1,29,67),(1,31,67)]),
  ([(22,23),(24,27),(37,29),(23,31),(-1,107)],[(1,11,22)]),
  ([(-1,108)],[(-256,22,57),(1,22,36),(2097152,29,33),(65536,29,64),(1,29,36)]),
  ([(-1,109)],[(1,22,48),(-256,22,60),(1,29,75)]),
  ([(-1,110)],[(1,22,66),(1,29,76)]),
  ([(37,29),(-1,111)],[(1,11,22)]),
  ([(-1,112)],[(1,22,57),(2,29,32),(1,29,56),(4,29,64)]),
  ([(-1,113)],[(1,22,60),(1,29,79)]),
  ([(-1,114)],[(1,22,67),(1,29,80)]),
  ([(20,29),(-1,115)],[(1,11,22)])
 ]

/-- Bind all sixteen actual ASTs BEFORE evaluating any witness. -/
private theorem shape (setup : Table F (fields 4)) (piece : Fin 16) :
    (FlatOperation.constraints (importedConstraints setup)).get
      ⟨82 + piece.val,by change 82 + piece.val < 117; have := piece.isLt; omega⟩ =
        quadraticSyntax sourceData[piece] := by
  fin_cases piece <;> rfl

private theorem equation {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (piece : Fin 16) : (quadraticSyntax sourceData[piece]).eval (environment w) = 0 := by
  rw [← shape setup piece]
  exact assertion_of_holds holds _

/-- All four complete tuples, without projecting away mixed opcode inputs. -/
theorem exact_queries {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (slot : Fin 4) : query w slot = (normalized w)[slot] := by
  have point (piece : Fin 4) : (query w slot)[piece] = (normalized w)[slot][piece] := by
    have h := equation holds (⟨4 * slot.val + piece.val,by have := slot.isLt; have := piece.isLt; omega⟩ : Fin 16)
    fin_cases slot <;> fin_cases piece
    all_goals
      simp [quadraticSyntax,linearSyntax,sourceData,Expression.eval,environment] at h
      dsimp [query,normalized]
      linear_combination -h
  exact Vector.ext fun i bound => point ⟨i,bound⟩

theorem body {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) : RowEffects w := by
  have caller := Airbender.NativeCallerRequestProofs.body holds
  have first := exact_queries holds 0
  have third := exact_queries holds 2
  have fourth := exact_queries holds 3
  refine ⟨caller,exact_queries holds,?_,?_,?_⟩
  · intro present
    obtain ⟨enabled,_,supported,_⟩ := caller.present present
    have h := congrArg (fun q => q[1]) first
    simp [query,normalized,enabled,supported] at h
    linear_combination h
  · intro present
    obtain ⟨enabled,_,supported,_⟩ := caller.present present
    have h := congrArg (fun q => q[2]) first
    simp [query,normalized,enabled,supported] at h
    linear_combination h
  · have h := congrArg (fun q => q[3]) third
    have j := congrArg (fun q => q[3]) fourth
    simp [query,normalized] at h j
    linear_combination h-j

/-- Original Clean lookup membership, rewritten by the checked normal form. -/
theorem membership {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (slot : Fin 4) : setup.Contains #[] (normalized w)[slot] := by
  rw [← exact_queries holds slot]
  fin_cases slot
  · have h := lookup_of_holds holds ⟨18,by change 18 < 22; decide⟩
    simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Table.toRaw,
      Expression.eval,environment,ProvableType.fromElements,query] using h
  · have h := lookup_of_holds holds ⟨19,by change 19 < 22; decide⟩
    simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Table.toRaw,
      Expression.eval,environment,ProvableType.fromElements,query] using h
  · have h := lookup_of_holds holds ⟨20,by change 20 < 22; decide⟩
    simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Table.toRaw,
      Expression.eval,environment,ProvableType.fromElements,query] using h
  · have h := lookup_of_holds holds ⟨21,by change 21 < 22; decide⟩
    simpa [importedConstraints,FlatOperation.lookups,Lookup.Contains,Table.toRaw,
      Expression.eval,environment,ProvableType.fromElements,query] using h

theorem runtime {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w)
      (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table)) : RuntimeRowEffects w :=
  ⟨body holds,membership holds⟩

theorem all_rows {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) : Effects proofs := by
  have source : ∀ proof ∈ Airbender.NativeInitializationBatch.mainProofs proofs, ∀ i < callerAuxiliaryLayout.traceLength-1,
      RuntimeRowEffects (proof.rows i) := by
    intro proof member i bound
    obtain ⟨origin,present,rfl⟩ := List.mem_map.mp member
    exact runtime ((accepted.arguments.mainDelegation origin.main (List.mem_map.mpr ⟨origin,present,rfl⟩)).body i bound)
  exact Airbender.NativeActiveWorkerClockProofs.sampled_property
    (Airbender.NativeInitializationBatch.mainProofs proofs) (fun proof => proof.rows)
    (callerAuxiliaryLayout.traceLength-1) RuntimeRowEffects source

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
    Airbender.NativeDelegationKeyAccounting.Effects batch workers inputs ∧
      Airbender.NativeCallerMixedQueries.Effects batch.main.proofs :=
  ⟨Airbender.NativeDelegationKeyAccountingProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity,
    all_rows embed memory ch pc gamma config accepted.counted.component⟩
end Airbender.NativeCallerMixedQueryProofs
