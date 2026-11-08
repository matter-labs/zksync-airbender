import Airbender.Review.Circuits.Blake2Worker.ExtendedOutput
import Airbender.Proofs.ReducedMachine.NativeWorkerDiagonalG

namespace Airbender.NativeWorkerExtendedOutputProofs
open Airbender.NativeWorkerExtendedOutput Airbender.Blake2Worker.Native Airbender.Verification
open Airbender.NativeWorkerFirstG (pack)
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
private theorem block4 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock4 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock4 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup ++ constraintsBlock3 setup ++ constraintsBlock4 setup) := by
    exact List.sublist_append_right _ _
  exact ((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))


/-- Exact native ports9..24, before their values are sampled. -/
private theorem write_shape (word : Fin 16) :
    (memoryAccess ⟨9+word.val,by have := word.isLt; omega⟩).writeValue = some #v[38+4*word.val,39+4*word.val] := by
  fin_cases word <;> rfl

theorem write_value (w : Nat → F) (word : Fin 16) (limb : Fin 2) :
    (keyValue w ⟨9+word.val,by have := word.isLt; omega⟩ true)[limb] = writeLimb w word limb := by
  fin_cases limb
  · simp [keyValue,write_shape,writeLimb]
  · simp [keyValue,write_shape,writeLimb]
    congr 1
    omega

/-- Exact logical coordinates obtained by reversing the existing physical map. -/
private def writeTerms : Vector (List (Int × Nat)) 32 := #v[
[(-65536,268),(-131072,269),(-65536,296),(-131072,297),(-65536,452),(-131072,453),(-65536,478),(-131072,479),(1,155),(1,171),(1,236),(1,290),(16,293),(128,294),(1,238),(1,357),(512,358),(1,252),(1,472),(16,475),(128,476),(1,254),(-1,38)],
[(1,268),(2,269),(-65536,270),(-131072,271),(1,296),(2,297),(-65536,298),(-131072,299),(1,452),(2,453),(-65536,454),(-131072,455),(1,478),(2,479),(-65536,480),(-131072,481),(1,157),(1,173),(1,237),(16,288),(128,289),(1,295),(1,239),(512,356),(1,359),(1,253),(16,470),(128,471),(1,477),(1,255),(-1,39)],
[(-65536,314),(-131072,315),(-65536,342),(-131072,343),(-65536,496),(-131072,497),(-65536,522),(-131072,523),(1,159),(1,175),(1,240),(1,336),(16,339),(128,340),(1,242),(1,403),(512,404),(1,256),(1,516),(16,519),(128,520),(1,258),(-1,42)],
[(1,314),(2,315),(-65536,316),(-131072,317),(1,342),(2,343),(-65536,344),(-131072,345),(1,496),(2,497),(-65536,498),(-131072,499),(1,522),(2,523),(-65536,524),(-131072,525),(1,161),(1,177),(1,241),(16,334),(128,335),(1,341),(1,243),(512,402),(1,405),(1,257),(16,514),(128,515),(1,521),(1,259),(-1,43)],
[(-65536,360),(-131072,361),(-65536,388),(-131072,389),(-65536,540),(-131072,541),(-65536,566),(-131072,567),(1,163),(1,179),(1,244),(1,382),(16,385),(128,386),(1,246),(1,449),(512,450),(1,260),(1,560),(16,563),(128,564),(1,262),(-1,46)],
[(1,360),(2,361),(-65536,362),(-131072,363),(1,388),(2,389),(-65536,390),(-131072,391),(1,540),(2,541),(-65536,542),(-131072,543),(1,566),(2,567),(-65536,568),(-131072,569),(1,165),(1,181),(1,245),(16,380),(128,381),(1,387),(1,247),(512,448),(1,451),(1,261),(16,558),(128,559),(1,565),(1,263),(-1,47)],
[(-65536,406),(-131072,407),(-65536,434),(-131072,435),(-65536,584),(-131072,585),(-65536,610),(-131072,611),(1,311),(512,312),(1,167),(1,183),(1,248),(1,428),(16,431),(128,432),(1,250),(1,264),(1,604),(16,607),(128,608),(1,266),(-1,50)],
[(1,406),(2,407),(-65536,408),(-131072,409),(1,434),(2,435),(-65536,436),(-131072,437),(1,584),(2,585),(-65536,586),(-131072,587),(1,610),(2,611),(-65536,612),(-131072,613),(512,310),(1,313),(1,169),(1,185),(1,249),(16,426),(128,427),(1,433),(1,251),(1,265),(16,602),(128,603),(1,609),(1,267),(-1,51)],
[(1,625),(512,626),(-1,54)],
[(512,624),(1,627),(-1,55)],
[(1,493),(512,494),(-1,58)],
[(512,492),(1,495),(-1,59)],
[(1,537),(512,538),(-1,62)],
[(512,536),(1,539),(-1,63)],
[(1,581),(512,582),(-1,66)],
[(512,580),(1,583),(-1,67)],
[(-65536,280),(-65536,306),(-65536,550),(-65536,576),(1,278),(256,279),(1,186),(1,303),(256,304),(1,548),(256,549),(1,573),(256,574),(-1,70)],
[(1,280),(-65536,281),(1,306),(-65536,307),(1,550),(-65536,551),(1,576),(-65536,577),(1,275),(256,276),(1,187),(256,302),(1,305),(1,546),(256,547),(256,572),(1,575),(-1,71)],
[(-65536,326),(-65536,352),(-65536,594),(-65536,620),(1,324),(256,325),(1,188),(1,349),(256,350),(1,592),(256,593),(1,617),(256,618),(-1,74)],
[(1,326),(-65536,327),(1,352),(-65536,353),(1,594),(-65536,595),(1,620),(-65536,621),(1,321),(256,322),(1,189),(256,348),(1,351),(1,590),(256,591),(256,616),(1,619),(-1,75)],
[(-65536,372),(-65536,398),(-65536,462),(-65536,488),(1,370),(256,371),(1,190),(1,395),(256,396),(1,460),(256,461),(1,485),(256,486),(-1,78)],
[(1,372),(-65536,373),(1,398),(-65536,399),(1,462),(-65536,463),(1,488),(-65536,489),(1,367),(256,368),(1,191),(256,394),(1,397),(1,458),(256,459),(256,484),(1,487),(-1,79)],
[(-65536,418),(-65536,444),(-65536,506),(-65536,532),(1,416),(256,417),(1,192),(1,441),(256,442),(1,504),(256,505),(1,529),(256,530),(-1,82)],
[(1,418),(-65536,419),(1,444),(-65536,445),(1,506),(-65536,507),(1,532),(-65536,533),(1,413),(256,414),(1,193),(256,440),(1,443),(1,502),(256,503),(256,528),(1,531),(-1,83)],
[(1,529),(256,530),(-1,86)],
[(256,528),(1,531),(-1,87)],
[(1,573),(256,574),(-1,90)],
[(256,572),(1,575),(-1,91)],
[(1,617),(256,618),(-1,94)],
[(256,616),(1,619),(-1,95)],
[(1,485),(256,486),(-1,98)],
[(256,484),(1,487),(-1,99)]]
private def linearSyntax (terms : List (Int × Nat)) : Expression F :=
  terms.foldl (fun e t => .add e (.mul (.mul (.const 1) (.const (t.1 : F))) (.var ⟨t.2⟩))) (.add (.const 0) (.const 0))
private def equation (setup : Table F (fields 4)) (piece : Fin 32) : Expression F :=
  if h : piece.val < 16 then (FlatOperation.constraints (constraintsBlock4 setup)).get ⟨48+piece.val,by change 48+piece.val < 64; omega⟩
  else (FlatOperation.constraints (constraintsBlock5 setup)).get ⟨piece.val-16,by change piece.val-16 < 32; have := piece.isLt; omega⟩
/-- Bind the complete native write ASTs BEFORE evaluating any witness. -/
private theorem shape (setup : Table F (fields 4)) (piece : Fin 32) :
    equation setup piece = linearSyntax writeTerms[piece] := by
  fin_cases piece <;> rfl
private theorem equation_holds {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (piece : Fin 32) :
    (linearSyntax writeTerms[piece]).eval (environment w) = 0 := by
  rw [← shape setup piece]
  unfold equation
  split
  · exact assertion_of_holds (block4 holds) _
  · exact assertion_of_holds (Airbender.Blake2Worker.QueryProofs.block5 holds) _

/-- The inverse permutation covers all sixteen actual memory outputs. -/
theorem destination_inverse (word : Fin 16) : destination (diagonalOf word) (componentOf word) = word := by
  fin_cases word <;> rfl

theorem component0 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (diagonal : Fin 4) (limb : Fin 2) :
    writeLimb w (destination diagonal 0) limb = resultLimb w diagonal 0 limb := by
  have eq := equation_holds holds ⟨8*0+2*((diagonal.val+0)%4)+limb.val,by have := Nat.mod_lt (diagonal.val+0) (by decide : 0<4); have := limb.isLt; omega⟩
  fin_cases diagonal <;> fin_cases limb
  all_goals
    simp [linearSyntax,writeTerms,Expression.eval,environment] at eq
    simp [writeLimb,destination,resultLimb,Airbender.NativeWorkerDiagonalAD.sumLimb,Airbender.NativeWorkerDiagonalAD.bInput,Airbender.NativeWorkerDiagonalAD.carry,Airbender.NativeWorkerDiagonalFirst.sumLimb,Airbender.NativeWorkerDiagonalFirst.inputLimb,Airbender.NativeWorkerDiagonalFirst.columnLimb,Airbender.NativeWorkerDiagonalFirst.sourceColumn,Airbender.NativeWorkerDiagonalFirst.bLimb,Airbender.NativeWorkerDiagonalFirst.carry,Airbender.NativeWorkerSecondAD.sumLimb,Airbender.NativeWorkerSecondAD.bInput,Airbender.NativeWorkerSecondAD.carry,Airbender.NativeWorkerFirstG.sumLimb,Airbender.NativeWorkerFirstG.carry,Airbender.NativeWorkerInitial.observed,Airbender.NativeWorkerInitial.initialColumns,Airbender.NativeWorkerSchedule.selected]
    linear_combination -eq

theorem component1 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (diagonal : Fin 4) (limb : Fin 2) :
    writeLimb w (destination diagonal 1) limb = resultLimb w diagonal 1 limb := by
  have eq := equation_holds holds ⟨8*1+2*((diagonal.val+1)%4)+limb.val,by have := Nat.mod_lt (diagonal.val+1) (by decide : 0<4); have := limb.isLt; omega⟩
  fin_cases diagonal <;> fin_cases limb
  all_goals
    simp [linearSyntax,writeTerms,Expression.eval,environment] at eq
    simp [writeLimb,destination,resultLimb,bLimb]
    linear_combination -eq

theorem component2 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (diagonal : Fin 4) (limb : Fin 2) :
    writeLimb w (destination diagonal 2) limb = resultLimb w diagonal 2 limb := by
  have eq := equation_holds holds ⟨8*2+2*((diagonal.val+2)%4)+limb.val,by have := Nat.mod_lt (diagonal.val+2) (by decide : 0<4); have := limb.isLt; omega⟩
  fin_cases diagonal <;> fin_cases limb
  all_goals
    simp [linearSyntax,writeTerms,Expression.eval,environment] at eq
    simp [writeLimb,destination,resultLimb,Airbender.NativeWorkerDiagonalG.cLimb,Airbender.NativeWorkerDiagonalG.cInput,Airbender.NativeWorkerDiagonalG.dLimb,Airbender.NativeWorkerDiagonalG.dByte,Airbender.NativeWorkerDiagonalG.carry,Airbender.NativeWorkerDiagonalCB.cLimb,Airbender.NativeWorkerDiagonalCB.cInput,Airbender.NativeWorkerDiagonalCB.dLimb,Airbender.NativeWorkerDiagonalCB.dByte,Airbender.NativeWorkerDiagonalCB.carry,Airbender.NativeWorkerDiagonalFirst.inputLimb,Airbender.NativeWorkerDiagonalFirst.columnLimb,Airbender.NativeWorkerDiagonalFirst.sourceColumn,Airbender.NativeWorkerSecondCB.cLimb,Airbender.NativeWorkerSecondCB.cInput,Airbender.NativeWorkerSecondCB.dLimb,Airbender.NativeWorkerSecondCB.dByte,Airbender.NativeWorkerSecondCB.carry,Airbender.NativeWorkerCB.cLimb,Airbender.NativeWorkerCB.cInput,Airbender.NativeWorkerCB.dLimb,Airbender.NativeWorkerCB.dByte,Airbender.NativeWorkerCB.carry,Airbender.NativeWorkerInitial.observed,Airbender.NativeWorkerInitial.initialColumns]
    linear_combination -eq

theorem component3 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (diagonal : Fin 4) (limb : Fin 2) :
    writeLimb w (destination diagonal 3) limb = resultLimb w diagonal 3 limb := by
  have eq := equation_holds holds ⟨8*3+2*((diagonal.val+3)%4)+limb.val,by have := Nat.mod_lt (diagonal.val+3) (by decide : 0<4); have := limb.isLt; omega⟩
  fin_cases diagonal <;> fin_cases limb
  all_goals
    simp [linearSyntax,writeTerms,Expression.eval,environment] at eq
    simp [writeLimb,destination,resultLimb,Airbender.NativeWorkerDiagonalG.dLimb,Airbender.NativeWorkerDiagonalG.dByte]
    linear_combination -eq

theorem limbs {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (diagonal component : Fin 4) (limb : Fin 2) :
    writeLimb w (destination diagonal component) limb = resultLimb w diagonal component limb := by
  fin_cases component
  · exact component0 holds diagonal limb
  · exact component1 holds diagonal limb
  · exact component2 holds diagonal limb
  · exact component3 holds diagonal limb
/-- Bind final B-output query syntax before deriving canonical chunk bounds. -/
private theorem b_shape (diagonal piece : Fin 4) :
    (fixedExpressions ⟨86+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[2] =
      .var ⟨492+44*diagonal.val+piece.val⟩ := by
  fin_cases diagonal <;> fin_cases piece <;> rfl
private def bWidth (piece : Fin 4) : Nat := #v[7,9,7,9][piece]
private theorem b_chunk_bounds {w : Nat → F} (effects : LookupEffects w) (diagonal piece : Fin 4) :
    (w (492+44*diagonal.val+piece.val)).val < 2^bWidth piece := by
  let slot : Fin 208 := ⟨86+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩
  have kind : (fixedKind slot).bound = 2^bWidth piece := by
    dsimp only [slot]
    fin_cases diagonal <;> fin_cases piece <;> norm_num [fixedKind,Airbender.Blake2Worker.Fixed.Kind.bound,bWidth]
  have same : (fixedQuery w slot)[2] = w (492+44*diagonal.val+piece.val) := by
    simpa [fixedQuery,slot,Expression.eval,environment] using congrArg (Expression.eval (environment w)) (b_shape diagonal piece)
  have h := effects.outputBounds slot
  rwa [same,kind] at h

theorem b_halves {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) :
    (bLimb w diagonal 0).val < 65536 ∧ (bLimb w diagonal 1).val < 65536 ∧
      pack (bLimb w diagonal 0) (bLimb w diagonal 1) = Airbender.NativeWorkerDiagonalG.bAfter w diagonal := by
  have b0 : (w (492+44*diagonal.val)).val < 128 := b_chunk_bounds effects diagonal 0
  have b1 : (w (493+44*diagonal.val)).val < 512 := by
    have h : (w (492+44*diagonal.val+1)).val < 512 := b_chunk_bounds effects diagonal 1
    rwa [show 492+44*diagonal.val+1=493+44*diagonal.val by omega] at h
  have b2 : (w (494+44*diagonal.val)).val < 128 := by
    have h : (w (492+44*diagonal.val+2)).val < 128 := b_chunk_bounds effects diagonal 2
    rwa [show 492+44*diagonal.val+2=494+44*diagonal.val by omega] at h
  have b3 : (w (495+44*diagonal.val)).val < 512 := by
    have h : (w (492+44*diagonal.val+3)).val < 512 := b_chunk_bounds effects diagonal 3
    rwa [show 492+44*diagonal.val+3=495+44*diagonal.val by omega] at h
  have low := Airbender.NativeWorkerDiagonalFirstProofs.pair97 (w (493+44*diagonal.val)+512*w (494+44*diagonal.val)) _ _ b1 b2 rfl
  have high := Airbender.NativeWorkerDiagonalFirstProofs.pair97 (w (495+44*diagonal.val)+512*w (492+44*diagonal.val)) _ _ b3 b0 rfl
  refine ⟨Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 512 (by omega),
    Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 512 (by omega),?_⟩
  change BitVec.append (BitVec.ofNat 16 (w (495+44*diagonal.val)+512*w (492+44*diagonal.val)).val)
    (BitVec.ofNat 16 (w (493+44*diagonal.val)+512*w (494+44*diagonal.val)).val) = _
  rw [low,high]
  change BitVec.append (BitVec.append (BitVec.ofNat 7 (w (492+44*diagonal.val)).val) (BitVec.ofNat 9 (w (495+44*diagonal.val)).val))
    (BitVec.append (BitVec.ofNat 7 (w (494+44*diagonal.val)).val) (BitVec.ofNat 9 (w (493+44*diagonal.val)).val)) =
    BitVec.append (BitVec.append (BitVec.ofNat 7 (w (492+44*diagonal.val)).val) (BitVec.ofNat 9 (w (493+44*diagonal.val+2)).val))
      (BitVec.append (BitVec.ofNat 7 (w (492+44*diagonal.val+2)).val) (BitVec.ofNat 9 (w (493+44*diagonal.val)).val))
  rw [show 493+44*diagonal.val+2=495+44*diagonal.val by omega,show 492+44*diagonal.val+2=494+44*diagonal.val by omega]

theorem packed {w : Nat → F} (effects : LookupEffects w) (diagonal component : Fin 4) :
    Airbender.NativeWorkerFirstG.pack (resultLimb w diagonal component 0) (resultLimb w diagonal component 1) =
      (Airbender.NativeWorkerDiagonalG.diagonalResult w diagonal)[component] := by
  fin_cases component
  · rfl
  · exact (b_halves effects diagonal).2.2
  · rfl
  · exact Airbender.NativeWorkerDiagonalGProofs.d_pack effects diagonal

theorem written {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) (word : Fin 16) :
    writeWord w word = (Airbender.NativeWorkerDiagonalG.diagonalResult w (diagonalOf word))[componentOf word] := by
  have low := limbs holds (diagonalOf word) (componentOf word) 0
  have high := limbs holds (diagonalOf word) (componentOf word) 1
  rw [destination_inverse] at low high
  unfold writeWord
  rw [low,high]
  exact packed (Airbender.Blake2Worker.QueryProofs.lookup_effects holds) _ _

theorem row {w : Nat → F} (prior : Airbender.NativeWorkerDiagonalG.RowEffects w)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    Airbender.NativeWorkerExtendedOutput.RowEffects w := by
  refine ⟨prior,limbs holds,written holds,?_⟩
  intro word
  rw [written holds,prior.complete]
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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerExtendedOutput.RowEffects w := by
  have prior := Airbender.NativeWorkerDiagonalGProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted.counted.component
  exact ⟨prior.1,fun w member => row (prior.2 w member) (processing w member).body⟩
end Airbender.NativeWorkerExtendedOutputProofs
