import Airbender.Review.Circuits.Blake2Worker.StateInitialization
import Airbender.Proofs.ReducedMachine.NativeWorkerSchedule

namespace Airbender.NativeWorkerInitialProofs
open Airbender.NativeWorkerInitial Airbender.NativeWorkerSchedule
open Airbender.Blake2Worker.Native Airbender.Verification
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private theorem block2 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock2 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock2 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup) := List.sublist_append_right _ _
  exact ((((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

private theorem block3 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock3 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock3 setup).Sublist
      ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup ++ constraintsBlock3 setup) :=
    List.sublist_append_right _ _
  exact (((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))


private def equation (setup : Table F (fields 4)) (q : Fin 49) : Expression F :=
  if h : q.val < 22 then (FlatOperation.constraints (constraintsBlock2 setup)).get ⟨42+q.val,by change 42+q.val < 64; omega⟩
  else (FlatOperation.constraints (constraintsBlock3 setup)).get ⟨q.val-22,by change q.val-22 < 64; have := q.isLt; omega⟩
private theorem equation_holds {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (q : Fin 49) :
    (equation setup q).eval (environment w) = 0 := by
  unfold equation
  split
  · exact assertion_of_holds (block2 holds) _
  · exact assertion_of_holds (block3 holds) _
private def baseFormula (w : Nat → F) (piece : Fin 16) : Prop :=
  w (154+2*piece.val) = w 140 * limbOf (configuredIV ⟨piece.val/2,by have := piece.isLt; omega⟩) ⟨piece.val%2,by omega⟩ +
    (1-w 140)*w (4+4*(piece.val/2)+piece.val%2)
private def rawInitial (w : Nat → F) (piece : Fin 32) : F :=
  if h : piece.val < 16 then w 141*w (154+2*piece.val)+(1-w 141)*w (36+4*(piece.val/2)+piece.val%2) else
  if piece.val/2 = 12 ∨ piece.val/2 = 14 then
    (1-w 141+w 153)*w (36+4*(piece.val/2)+piece.val%2)+w 141*w 140*limbOf (compressionIV ⟨piece.val/2,by have := piece.isLt; omega⟩) ⟨piece.val%2,by omega⟩
  else (1-w 141)*w (36+4*(piece.val/2)+piece.val%2)+w 141*limbOf iv[(⟨(piece.val/2)%8,by omega⟩ : Fin 8)] ⟨piece.val%2,by omega⟩
private def initialFormula (w : Nat → F) (piece : Fin 32) : Prop := w initialColumns[piece] = rawInitial w piece

private theorem base_part0 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    baseFormula w ⟨0 + i.val,by have := i.isLt; omega⟩ := by
  have eq := equation_holds holds ⟨1+2*(0 + i.val),by have := i.isLt; omega⟩
  fin_cases i
  all_goals
    simp [equation,constraintsBlock2,FlatOperation.constraints,Expression.eval,environment] at eq
    simp [baseFormula,limbOf,configuredIV,iv]
    linear_combination -eq

private theorem base_part1 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    baseFormula w ⟨8 + i.val,by have := i.isLt; omega⟩ := by
  have eq := equation_holds holds ⟨1+2*(8 + i.val),by have := i.isLt; omega⟩
  fin_cases i
  all_goals
    simp [equation,constraintsBlock2,constraintsBlock3,FlatOperation.constraints,Expression.eval,environment] at eq
    simp [baseFormula,limbOf,configuredIV,iv]
    linear_combination -eq

private theorem initial_part0 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    initialFormula w ⟨0 + i.val,by have := i.isLt; omega⟩ := by
  let indices : Vector (Fin 49) 8 := #v[2,4,6,8,10,12,14,16]
  have eq := equation_holds holds indices[i]
  fin_cases i
  all_goals
    simp [indices,equation,constraintsBlock2,FlatOperation.constraints,Expression.eval,environment] at eq
    simp [initialFormula,initialColumns,rawInitial]
    linear_combination -eq

private theorem initial_part1 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    initialFormula w ⟨8 + i.val,by have := i.isLt; omega⟩ := by
  let indices : Vector (Fin 49) 8 := #v[18,20,22,24,26,28,30,32]
  have eq := equation_holds holds indices[i]
  fin_cases i
  all_goals
    simp [indices,equation,constraintsBlock2,constraintsBlock3,FlatOperation.constraints,Expression.eval,environment] at eq
    simp [initialFormula,initialColumns,rawInitial]
    linear_combination -eq

private theorem initial_part2 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    initialFormula w ⟨16 + i.val,by have := i.isLt; omega⟩ := by
  let indices : Vector (Fin 49) 8 := #v[33,34,35,36,37,38,39,40]
  have eq := equation_holds holds indices[i]
  fin_cases i
  all_goals
    simp [indices,equation,constraintsBlock3,FlatOperation.constraints,Expression.eval,environment] at eq
    simp [initialFormula,initialColumns,rawInitial,limbOf,iv]
    linear_combination -eq

private theorem initial_part3 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    initialFormula w ⟨24 + i.val,by have := i.isLt; omega⟩ := by
  let indices : Vector (Fin 49) 8 := #v[45,46,41,42,47,48,43,44]
  have eq := equation_holds holds indices[i]
  fin_cases i
  all_goals
    simp [indices,equation,constraintsBlock3,FlatOperation.constraints,Expression.eval,environment] at eq
    simp [initialFormula,initialColumns,rawInitial,limbOf,compressionIV,iv]
    linear_combination -eq


private theorem base_all {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (piece : Fin 16) : baseFormula w piece := by
  by_cases low : piece.val < 8
  · have same : (⟨0+piece.val,by omega⟩ : Fin 16) = piece := by apply Fin.ext; change 0+piece.val = piece.val; omega
    exact same ▸ base_part0 holds ⟨piece.val,low⟩
  have localIndex : piece.val-8 < 8 := by have := piece.isLt; omega
  have same : (⟨8+(piece.val-8),by omega⟩ : Fin 16) = piece := by apply Fin.ext; change 8+(piece.val-8) = piece.val; omega
  exact same ▸ base_part1 holds ⟨piece.val-8,localIndex⟩
private theorem bit (w : Nat → F) (slot : Fin 13) : inputBit w slot = 0 ∨ inputBit w slot = 1 := by
  have h := Nat.mod_lt ((w 135).val/2^slot.val) (show 0 < 2 by decide +kernel)
  unfold inputBit
  omega

/-- All16 final-XOR base limbs select original state or the configured IV. -/
theorem bases {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (word : Fin 8) (limb : Fin 2) : w (154+4*word.val+2*limb.val) = finalBase w word limb := by
  have cflag : w 140 = (inputBit w 2 : F) := by simpa using Airbender.NativeWorkerScheduleProofs.flags holds 2
  have eq := base_all holds ⟨2*word.val+limb.val,by have := word.isLt; have := limb.isLt; omega⟩
  have div : (2*word.val+limb.val)/2 = word.val := by have := limb.isLt; omega
  have mod : (2*word.val+limb.val)%2 = limb.val := by have := limb.isLt; omega
  have coord : 154+2*(2*word.val+limb.val) = 154+4*word.val+2*limb.val := by omega
  rcases bit w 2 with zero | one
  · simpa [baseFormula,div,mod,coord,cflag,finalBase,zero,state] using eq
  · simpa [baseFormula,div,mod,coord,cflag,finalBase,one] using eq


private theorem reference_part0 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    w initialColumns[(⟨0 + i.val,by have := i.isLt; omega⟩ : Fin 32)] =
      initial w ⟨(0 + i.val)/2,by have := i.isLt; omega⟩ ⟨(0 + i.val)%2,by omega⟩ := by
  have fflag : w 141 = (inputBit w 3 : F) := by simpa using Airbender.NativeWorkerScheduleProofs.flags holds 3
  have base0 : w 154 = finalBase w 0 0 := bases holds 0 0
  have base1 : w 156 = finalBase w 0 1 := bases holds 0 1
  have base2 : w 158 = finalBase w 1 0 := bases holds 1 0
  have base3 : w 160 = finalBase w 1 1 := bases holds 1 1
  have base4 : w 162 = finalBase w 2 0 := bases holds 2 0
  have base5 : w 164 = finalBase w 2 1 := bases holds 2 1
  have base6 : w 166 = finalBase w 3 0 := bases holds 3 0
  have base7 : w 168 = finalBase w 3 1 := bases holds 3 1
  have eq := initial_part0 holds i
  fin_cases i
  all_goals
    simp [initialFormula,initialColumns,rawInitial] at eq
    simp only [base0,base1,base2,base3,base4,base5,base6,base7,fflag] at eq
    rcases bit w 3 with firstBit | firstBit
    all_goals
      simp [firstBit] at eq
      simpa [initialColumns,initial,oldExtended,firstBit] using eq

private theorem reference_part1 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    w initialColumns[(⟨8 + i.val,by have := i.isLt; omega⟩ : Fin 32)] =
      initial w ⟨(8 + i.val)/2,by have := i.isLt; omega⟩ ⟨(8 + i.val)%2,by omega⟩ := by
  have fflag : w 141 = (inputBit w 3 : F) := by simpa using Airbender.NativeWorkerScheduleProofs.flags holds 3
  have base8 : w 170 = finalBase w 4 0 := bases holds 4 0
  have base9 : w 172 = finalBase w 4 1 := bases holds 4 1
  have base10 : w 174 = finalBase w 5 0 := bases holds 5 0
  have base11 : w 176 = finalBase w 5 1 := bases holds 5 1
  have base12 : w 178 = finalBase w 6 0 := bases holds 6 0
  have base13 : w 180 = finalBase w 6 1 := bases holds 6 1
  have base14 : w 182 = finalBase w 7 0 := bases holds 7 0
  have base15 : w 184 = finalBase w 7 1 := bases holds 7 1
  have eq := initial_part1 holds i
  fin_cases i
  all_goals
    simp [initialFormula,initialColumns,rawInitial] at eq
    simp only [base8,base9,base10,base11,base12,base13,base14,base15,fflag] at eq
    rcases bit w 3 with firstBit | firstBit
    all_goals
      simp [firstBit] at eq
      simpa [initialColumns,initial,oldExtended,firstBit] using eq

private theorem reference_part2 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    w initialColumns[(⟨16 + i.val,by have := i.isLt; omega⟩ : Fin 32)] =
      initial w ⟨(16 + i.val)/2,by have := i.isLt; omega⟩ ⟨(16 + i.val)%2,by omega⟩ := by
  have fflag : w 141 = (inputBit w 3 : F) := by simpa using Airbender.NativeWorkerScheduleProofs.flags holds 3
  have eq := initial_part2 holds i
  fin_cases i
  all_goals
    simp [initialFormula,initialColumns,rawInitial] at eq
    simp only [fflag] at eq
    rcases bit w 3 with firstBit | firstBit
    all_goals
      simp [firstBit] at eq
      simpa [initialColumns,initial,oldExtended,firstBit] using eq

private theorem reference_part3 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    w initialColumns[(⟨24 + i.val,by have := i.isLt; omega⟩ : Fin 32)] =
      initial w ⟨(24 + i.val)/2,by have := i.isLt; omega⟩ ⟨(24 + i.val)%2,by omega⟩ := by
  have fflag : w 141 = (inputBit w 3 : F) := by simpa using Airbender.NativeWorkerScheduleProofs.flags holds 3
  have cflag : w 140 = (inputBit w 2 : F) := by simpa using Airbender.NativeWorkerScheduleProofs.flags holds 2
  have normal := equation_holds holds 0
  simp [equation,constraintsBlock2,FlatOperation.constraints,Expression.eval,environment] at normal
  have normalEq : w 153 = w 141-w 140*w 141 := by linear_combination -normal
  have eq := initial_part3 holds i
  fin_cases i
  all_goals
    simp [initialFormula,initialColumns,rawInitial] at eq
    simp only [normalEq,cflag,fflag] at eq
    rcases bit w 3 with firstBit | firstBit <;> rcases bit w 2 with compBit | compBit
    all_goals
      simp [firstBit,compBit] at eq
      simpa [initialColumns,initial,oldExtended,firstBit,compBit] using eq
private theorem reference_all {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (piece : Fin 32) : w initialColumns[piece] = initial w ⟨piece.val/2,by have := piece.isLt; omega⟩ ⟨piece.val%2,by omega⟩ := by
  by_cases h0 : piece.val < 8
  · have localIndex : piece.val-0 < 8 := by have := piece.isLt; omega
    have same : (⟨0+(piece.val-0),by omega⟩ : Fin 32) = piece := by apply Fin.ext; change 0+(piece.val-0) = piece.val; omega
    exact same ▸ reference_part0 holds ⟨piece.val-0,localIndex⟩
  by_cases h1 : piece.val < 16
  · have localIndex : piece.val-8 < 8 := by have := piece.isLt; omega
    have same : (⟨8+(piece.val-8),by omega⟩ : Fin 32) = piece := by apply Fin.ext; change 8+(piece.val-8) = piece.val; omega
    exact same ▸ reference_part1 holds ⟨piece.val-8,localIndex⟩
  by_cases h2 : piece.val < 24
  · have localIndex : piece.val-16 < 8 := by have := piece.isLt; omega
    have same : (⟨16+(piece.val-16),by omega⟩ : Fin 32) = piece := by apply Fin.ext; change 16+(piece.val-16) = piece.val; omega
    exact same ▸ reference_part2 holds ⟨piece.val-16,localIndex⟩
  have localIndex : piece.val-24 < 8 := by have := piece.isLt; omega
  have same : (⟨24+(piece.val-24),by omega⟩ : Fin 32) = piece := by apply Fin.ext; change 24+(piece.val-24) = piece.val; omega
  exact same ▸ reference_part3 holds ⟨piece.val-24,localIndex⟩

/-- All32 actual pre-mixing limbs from original extended/state reads. -/
theorem initialized {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (word : Fin 16) (limb : Fin 2) : observed w word limb = initial w word limb := by
  have eq := reference_all holds ⟨2*word.val+limb.val,by have := word.isLt; have := limb.isLt; omega⟩
  have div : (2*word.val+limb.val)/2 = word.val := by have := limb.isLt; omega
  have mod : (2*word.val+limb.val)%2 = limb.val := by have := limb.isLt; omega
  simpa only [observed,div,mod,Fin.eta] using eq

/-- The same full BODY retains the checked schedule and derives state initialization. -/
theorem row {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) : Airbender.NativeWorkerInitial.RowEffects w :=
  ⟨Airbender.NativeWorkerScheduleProofs.row holds,bases holds,initialized holds⟩

open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary
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
    Airbender.NativeMixedReplay.Effects batch workers inputs ∧
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerInitial.RowEffects w := by
  have prior := Airbender.NativeMixedReplayProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted.counted.component
  exact ⟨prior,fun w member => row (processing w member).body⟩
end Airbender.NativeWorkerInitialProofs
