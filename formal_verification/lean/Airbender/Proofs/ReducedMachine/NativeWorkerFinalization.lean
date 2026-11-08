import Airbender.Review.Circuits.Blake2Worker.Finalization
import Airbender.Proofs.ReducedMachine.NativeWorkerExtendedOutput

namespace Airbender.NativeWorkerFinalizationProofs
open Airbender.Verification Airbender.Blake2Worker.Native
open Airbender.NativeWorkerFirstG (pack)
open Airbender.NativeWorkerFinalization
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Generic bounded XOR packing, before native source data. -/
private structure PairEffects (q : Vector F 4) (width : Nat) : Prop where
  left : q[0].val < 2^width
  right : q[1].val < 2^width
  output : q[2].val < 2^width
  result : q[2].val = q[0].val ^^^ q[1].val

private theorem append_xor {m n : Nat} (a c : BitVec m) (b d : BitVec n) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append

private theorem halves_xor (a b c d : BitVec 16) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append

private theorem word_xor (a0 a1 b0 b1 c0 c1 : BitVec 16) :
    BitVec.append ((a1 ^^^ b1) ^^^ c1) ((a0 ^^^ b0) ^^^ c0) =
      (BitVec.append a1 a0 ^^^ BitVec.append b1 b0) ^^^ BitVec.append c1 c0 := by
  rw [halves_xor,halves_xor]

theorem xor79 (lo hi : Vector F 4) (l : PairEffects lo 7) (h : PairEffects hi 9) :
    BitVec.ofNat 16 (lo[2]+128*hi[2]).val =
      BitVec.ofNat 16 (lo[0]+128*hi[0]).val ^^^ BitVec.ofNat 16 (lo[1]+128*hi[1]).val := by
  simp only [Nat.cast_ofNat]
  rw [Airbender.NativeWorkerSecondCBProofs.pair_pack _ _ _ l.output h.output rfl,
    Airbender.NativeWorkerSecondCBProofs.pair_pack _ _ _ l.left h.left rfl,
    Airbender.NativeWorkerSecondCBProofs.pair_pack _ _ _ l.right h.right rfl,append_xor,
    ← Airbender.NativeWorkerCBProofs.piece_xor 7 _ _ _ l.left l.right l.output l.result,
    ← Airbender.NativeWorkerCBProofs.piece_xor 9 _ _ _ h.left h.right h.output h.result]

theorem xor97 (lo hi : Vector F 4) (l : PairEffects lo 9) (h : PairEffects hi 7) :
    BitVec.ofNat 16 (lo[2]+512*hi[2]).val =
      BitVec.ofNat 16 (lo[0]+512*hi[0]).val ^^^ BitVec.ofNat 16 (lo[1]+512*hi[1]).val := by
  simp only [Nat.cast_ofNat]
  rw [Airbender.NativeWorkerDiagonalFirstProofs.pair97 _ _ _ l.output h.output rfl,
    Airbender.NativeWorkerDiagonalFirstProofs.pair97 _ _ _ l.left h.left rfl,
    Airbender.NativeWorkerDiagonalFirstProofs.pair97 _ _ _ l.right h.right rfl,append_xor,
    ← Airbender.NativeWorkerCBProofs.piece_xor 9 _ _ _ l.left l.right l.output l.result,
    ← Airbender.NativeWorkerCBProofs.piece_xor 7 _ _ _ h.left h.right h.output h.result]

theorem xor88 (lo hi : Vector F 4) (l : PairEffects lo 8) (h : PairEffects hi 8) :
    BitVec.ofNat 16 (lo[2]+256*hi[2]).val =
      BitVec.ofNat 16 (lo[0]+256*hi[0]).val ^^^ BitVec.ofNat 16 (lo[1]+256*hi[1]).val := by
  simp only [Nat.cast_ofNat]
  rw [Airbender.NativeWorkerFirstGProofs.pair_bytes _ _ _ l.output h.output rfl,
    Airbender.NativeWorkerFirstGProofs.pair_bytes _ _ _ l.left h.left rfl,
    Airbender.NativeWorkerFirstGProofs.pair_bytes _ _ _ l.right h.right rfl,append_xor,
    ← Airbender.NativeWorkerFirstGProofs.byte_xor _ _ _ l.left l.right l.output l.result,
    ← Airbender.NativeWorkerFirstGProofs.byte_xor _ _ _ h.left h.right h.output h.result]

private inductive SourceInput where
  | variable : Nat → SourceInput
  | linear : List (Int × Nat) → SourceInput
private def linearSyntax (terms : List (Int × Nat)) : Expression F :=
  terms.foldl (fun e t => .add e (.mul (.mul (.const 1) (.const (t.1 : F))) (.var ⟨t.2⟩))) (.add (.const 0) (.const 0))
private def inputSyntax : SourceInput → Expression F
  | .variable n => .var ⟨n⟩
  | .linear ts => linearSyntax ts
private def sourceData : Vector (Vector SourceInput 3) 64 := #v[
#v[.variable 628,.variable 578,.variable 629],
#v[.linear [(16777216,154),(-16777216,628)],.linear [(16777216,186),(16777216,278),(2,279),(-512,280),(16777216,303),(2,304),(-512,306),(16777216,548),(2,549),(-512,550),(16777216,573),(2,574),(-512,576),(-16777216,578)],.variable 630],
#v[.variable 629,.variable 631,.variable 633],
#v[.variable 630,.linear [(16777216,155),(16777216,171),(16777216,236),(16777216,238),(16777216,252),(16777216,254),(-512,268),(-1024,269),(16777216,290),(268435456,293),(1,294),(-512,296),(-1024,297),(16777216,357),(4,358),(-512,452),(-1024,453),(16777216,472),(268435456,475),(1,476),(-512,478),(-1024,479),(-16777216,482),(1,632)],.variable 634],
#v[.variable 635,.variable 579,.variable 636],
#v[.linear [(16777216,156),(-16777216,635)],.linear [(16777216,187),(16777216,275),(2,276),(16777216,280),(-512,281),(2,302),(16777216,305),(16777216,306),(-512,307),(16777216,546),(2,547),(16777216,550),(-512,551),(2,572),(16777216,575),(16777216,576),(-512,577),(-16777216,579)],.variable 637],
#v[.variable 636,.variable 638,.variable 640],
#v[.variable 637,.linear [(16777216,157),(16777216,173),(16777216,237),(16777216,239),(16777216,253),(16777216,255),(16777216,268),(33554432,269),(-512,270),(-1024,271),(268435456,288),(1,289),(16777216,295),(16777216,296),(33554432,297),(-512,298),(-1024,299),(4,356),(16777216,359),(16777216,452),(33554432,453),(-512,454),(-1024,455),(268435456,470),(1,471),(16777216,477),(16777216,478),(33554432,479),(-512,480),(-1024,481),(-16777216,483),(1,639)],.variable 641],
#v[.variable 642,.variable 622,.variable 643],
#v[.linear [(16777216,158),(-16777216,642)],.linear [(16777216,188),(16777216,324),(2,325),(-512,326),(16777216,349),(2,350),(-512,352),(16777216,592),(2,593),(-512,594),(16777216,617),(2,618),(-512,620),(-16777216,622)],.variable 644],
#v[.variable 643,.variable 645,.variable 647],
#v[.variable 644,.linear [(16777216,159),(16777216,175),(16777216,240),(16777216,242),(16777216,256),(16777216,258),(-512,314),(-1024,315),(16777216,336),(268435456,339),(1,340),(-512,342),(-1024,343),(16777216,403),(4,404),(-512,496),(-1024,497),(16777216,516),(268435456,519),(1,520),(-512,522),(-1024,523),(-16777216,526),(1,646)],.variable 648],
#v[.variable 649,.variable 623,.variable 650],
#v[.linear [(16777216,160),(-16777216,649)],.linear [(16777216,189),(16777216,321),(2,322),(16777216,326),(-512,327),(2,348),(16777216,351),(16777216,352),(-512,353),(16777216,590),(2,591),(16777216,594),(-512,595),(2,616),(16777216,619),(16777216,620),(-512,621),(-16777216,623)],.variable 651],
#v[.variable 650,.variable 652,.variable 654],
#v[.variable 651,.linear [(16777216,161),(16777216,177),(16777216,241),(16777216,243),(16777216,257),(16777216,259),(16777216,314),(33554432,315),(-512,316),(-1024,317),(268435456,334),(1,335),(16777216,341),(16777216,342),(33554432,343),(-512,344),(-1024,345),(4,402),(16777216,405),(16777216,496),(33554432,497),(-512,498),(-1024,499),(268435456,514),(1,515),(16777216,521),(16777216,522),(33554432,523),(-512,524),(-1024,525),(-16777216,527),(1,653)],.variable 655],
#v[.variable 656,.variable 490,.variable 657],
#v[.linear [(16777216,162),(-16777216,656)],.linear [(16777216,190),(16777216,370),(2,371),(-512,372),(16777216,395),(2,396),(-512,398),(16777216,460),(2,461),(-512,462),(16777216,485),(2,486),(-512,488),(-16777216,490)],.variable 658],
#v[.variable 657,.variable 659,.variable 661],
#v[.variable 658,.linear [(16777216,163),(16777216,179),(16777216,244),(16777216,246),(16777216,260),(16777216,262),(-512,360),(-1024,361),(16777216,382),(268435456,385),(1,386),(-512,388),(-1024,389),(16777216,449),(4,450),(-512,540),(-1024,541),(16777216,560),(268435456,563),(1,564),(-512,566),(-1024,567),(-16777216,570),(1,660)],.variable 662],
#v[.variable 663,.variable 491,.variable 664],
#v[.linear [(16777216,164),(-16777216,663)],.linear [(16777216,191),(16777216,367),(2,368),(16777216,372),(-512,373),(2,394),(16777216,397),(16777216,398),(-512,399),(16777216,458),(2,459),(16777216,462),(-512,463),(2,484),(16777216,487),(16777216,488),(-512,489),(-16777216,491)],.variable 665],
#v[.variable 664,.variable 666,.variable 668],
#v[.variable 665,.linear [(16777216,165),(16777216,181),(16777216,245),(16777216,247),(16777216,261),(16777216,263),(16777216,360),(33554432,361),(-512,362),(-1024,363),(268435456,380),(1,381),(16777216,387),(16777216,388),(33554432,389),(-512,390),(-1024,391),(4,448),(16777216,451),(16777216,540),(33554432,541),(-512,542),(-1024,543),(268435456,558),(1,559),(16777216,565),(16777216,566),(33554432,567),(-512,568),(-1024,569),(-16777216,571),(1,667)],.variable 669],
#v[.variable 670,.variable 534,.variable 671],
#v[.linear [(16777216,166),(-16777216,670)],.linear [(16777216,192),(16777216,416),(2,417),(-512,418),(16777216,441),(2,442),(-512,444),(16777216,504),(2,505),(-512,506),(16777216,529),(2,530),(-512,532),(-16777216,534)],.variable 672],
#v[.variable 671,.variable 673,.variable 675],
#v[.variable 672,.linear [(16777216,167),(16777216,183),(16777216,248),(16777216,250),(16777216,264),(16777216,266),(16777216,311),(4,312),(-512,406),(-1024,407),(16777216,428),(268435456,431),(1,432),(-512,434),(-1024,435),(-512,584),(-1024,585),(16777216,604),(268435456,607),(1,608),(-512,610),(-1024,611),(-16777216,614),(1,674)],.variable 676],
#v[.variable 677,.variable 535,.variable 678],
#v[.linear [(16777216,168),(-16777216,677)],.linear [(16777216,193),(16777216,413),(2,414),(16777216,418),(-512,419),(2,440),(16777216,443),(16777216,444),(-512,445),(16777216,502),(2,503),(16777216,506),(-512,507),(2,528),(16777216,531),(16777216,532),(-512,533),(-16777216,535)],.variable 679],
#v[.variable 678,.variable 680,.variable 682],
#v[.variable 679,.linear [(16777216,169),(16777216,185),(16777216,249),(16777216,251),(16777216,265),(16777216,267),(4,310),(16777216,313),(16777216,406),(33554432,407),(-512,408),(-1024,409),(268435456,426),(1,427),(16777216,433),(16777216,434),(33554432,435),(-512,436),(-1024,437),(16777216,584),(33554432,585),(-512,586),(-1024,587),(268435456,602),(1,603),(16777216,609),(16777216,610),(33554432,611),(-512,612),(-1024,613),(-16777216,615),(1,681)],.variable 683],
#v[.variable 625,.variable 684,.variable 685],
#v[.variable 626,.linear [(4194304,170),(-4194304,684)],.variable 686],
#v[.variable 529,.variable 687,.variable 689],
#v[.variable 530,.linear [(2,686),(1,688)],.variable 690],
#v[.variable 627,.variable 691,.variable 692],
#v[.variable 624,.linear [(4194304,172),(-4194304,691)],.variable 693],
#v[.variable 531,.variable 694,.variable 696],
#v[.variable 528,.linear [(2,693),(1,695)],.variable 697],
#v[.variable 493,.variable 698,.variable 699],
#v[.variable 494,.linear [(4194304,174),(-4194304,698)],.variable 700],
#v[.variable 573,.variable 701,.variable 703],
#v[.variable 574,.linear [(2,700),(1,702)],.variable 704],
#v[.variable 495,.variable 705,.variable 706],
#v[.variable 492,.linear [(4194304,176),(-4194304,705)],.variable 707],
#v[.variable 575,.variable 708,.variable 710],
#v[.variable 572,.linear [(2,707),(1,709)],.variable 711],
#v[.variable 537,.variable 712,.variable 713],
#v[.variable 538,.linear [(4194304,178),(-4194304,712)],.variable 714],
#v[.variable 617,.variable 715,.variable 717],
#v[.variable 618,.linear [(2,714),(1,716)],.variable 718],
#v[.variable 539,.variable 719,.variable 720],
#v[.variable 536,.linear [(4194304,180),(-4194304,719)],.variable 721],
#v[.variable 619,.variable 722,.variable 724],
#v[.variable 616,.linear [(2,721),(1,723)],.variable 725],
#v[.variable 581,.variable 726,.variable 727],
#v[.variable 582,.linear [(4194304,182),(-4194304,726)],.variable 728],
#v[.variable 485,.variable 729,.variable 731],
#v[.variable 486,.linear [(2,728),(1,730)],.variable 732],
#v[.variable 583,.variable 733,.variable 734],
#v[.variable 580,.linear [(4194304,184),(-4194304,733)],.variable 735],
#v[.variable 487,.variable 736,.variable 738],
#v[.variable 484,.linear [(2,735),(1,737)],.variable 739]]
private def query (w : Nat → F) (limb : Fin 16) (piece : Fin 4) : Vector F 4 :=
  fixedQuery w ⟨144+4*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩
/-- Bind every actual query input/output AST BEFORE witness evaluation. -/
private theorem shape (limb : Fin 16) (piece : Fin 4) (entry : Fin 3) :
    (fixedExpressions ⟨144+4*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[(⟨entry.val,by have := entry.isLt; omega⟩ : Fin 4)] =
      inputSyntax sourceData[(⟨4*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩ : Fin 64)][entry] := by
  fin_cases limb <;> fin_cases piece <;> fin_cases entry <;> rfl
private theorem value0 (w : Nat → F) (limb : Fin 16) (piece : Fin 4) :
    (query w limb piece)[0] = Expression.eval (environment w)
      (inputSyntax sourceData[(⟨4*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩ : Fin 64)][0]) := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape limb piece 0)
private theorem value1 (w : Nat → F) (limb : Fin 16) (piece : Fin 4) :
    (query w limb piece)[1] = Expression.eval (environment w)
      (inputSyntax sourceData[(⟨4*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩ : Fin 64)][1]) := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape limb piece 1)
private theorem value2 (w : Nat → F) (limb : Fin 16) (piece : Fin 4) :
    (query w limb piece)[2] = Expression.eval (environment w)
      (inputSyntax sourceData[(⟨4*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩ : Fin 64)][2]) := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape limb piece 2)
private def width (limb : Fin 16) (piece : Fin 4) : Nat :=
  if limb.val < 8 then #v[7,9,7,9][piece] else #v[9,7,8,8][piece]
private theorem query_effects {w : Nat → F} (effects : LookupEffects w) (limb : Fin 16) (piece : Fin 4) :
    PairEffects (query w limb piece) (width limb piece) := by
  let slot : Fin 208 := ⟨144+4*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩
  have kind : (fixedKind slot).bound = 2^width limb piece := by
    dsimp only [slot]
    fin_cases limb <;> fin_cases piece <;> norm_num [width,fixedKind,Airbender.Blake2Worker.Fixed.Kind.bound]
  exact ⟨by simpa only [query,slot,kind] using effects.leftBounds slot,
    by simpa only [query,slot,kind] using effects.rightBounds slot,
    by simpa only [query,slot,kind] using effects.outputBounds slot,effects.results slot⟩
private theorem block4 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock4 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock4 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup ++ constraintsBlock3 setup ++ constraintsBlock4 setup) := by
    exact List.sublist_append_right _ _
  exact ((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))


@[simp] private theorem coefficient0 : (2147483647 : F) = 0 := by decide +kernel
@[simp] private theorem coefficient1 : (2147483648 : F) = 1 := by decide +kernel
@[simp] private theorem coefficient2 : (4294967296 : F) = 2 := by decide +kernel
private def splitTerms : Vector (List (Int × Nat)) 16 := #v[
[(-128,632),(1,482),(-1,631)],
[(-128,639),(1,483),(-1,638)],
[(-128,646),(1,526),(-1,645)],
[(-128,653),(1,527),(-1,652)],
[(-128,660),(1,570),(-1,659)],
[(-128,667),(1,571),(-1,666)],
[(-128,674),(1,614),(-1,673)],
[(-128,681),(1,615),(-1,680)],
[(-256,688),(1,685),(-1,687)],
[(-256,695),(1,692),(-1,694)],
[(-256,702),(1,699),(-1,701)],
[(-256,709),(1,706),(-1,708)],
[(-256,716),(1,713),(-1,715)],
[(-256,723),(1,720),(-1,722)],
[(-256,730),(1,727),(-1,729)],
[(-256,737),(1,734),(-1,736)]]
private theorem split_shape (setup : Table F (fields 4)) (j : Fin 16) :
    (FlatOperation.constraints (constraintsBlock5 setup)).get ⟨16+j.val,by change 16+j.val < 32; have := j.isLt; omega⟩ =
      linearSyntax splitTerms[j] := by
  fin_cases j <;> rfl
private theorem split_equation {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (j : Fin 16) :
    (linearSyntax splitTerms[j]).eval (environment w) = 0 := by
  rw [← split_shape setup j]
  exact assertion_of_holds (Airbender.Blake2Worker.QueryProofs.block5 holds) _
private def first (j : Fin 8) : Fin 16 := ⟨j.val,by have := j.isLt; omega⟩
private def second (j : Fin 8) : Fin 16 := ⟨8+j.val,by have := j.isLt; omega⟩
private def nativeBase (w : Nat → F) (j : Fin 16) : F := w (154+2*j.val)
private def nativeWord (j : Fin 16) (upper : Bool) : Fin 16 :=
  ⟨(if upper then 8 else 0)+j.val/2,by have := j.isLt; cases upper <;> simp <;> omega⟩
private def resultValue (w : Nat → F) (j : Fin 16) (upper : Bool) : F :=
  Airbender.NativeWorkerExtendedOutput.resultLimb w
    (Airbender.NativeWorkerExtendedOutput.diagonalOf (nativeWord j upper))
    (Airbender.NativeWorkerExtendedOutput.componentOf (nativeWord j upper)) ⟨j.val%2,by omega⟩
private def finalValue (w : Nat → F) (j : Fin 16) : F :=
  w (633+7*j.val)+(if j.val < 8 then 128 else 256)*w (634+7*j.val)
private theorem base79 (w : Nat → F) (j : Fin 8) :
    (query w (first j) 0)[0]+128*(query w (first j) 1)[0] = nativeBase w (first j) := by
  rw [value0,value0]
  fin_cases j
  all_goals
    simp [first,nativeBase,sourceData,inputSyntax,linearSyntax,Expression.eval,environment]
    ring_nf
    simp
private theorem c79 (w : Nat → F) (j : Fin 8) :
    (query w (first j) 0)[1]+128*(query w (first j) 1)[1] = resultValue w (first j) true := by
  rw [value1,value1]
  fin_cases j
  all_goals
    simp [first,nativeWord,resultValue,Airbender.NativeWorkerExtendedOutput.diagonalOf,Airbender.NativeWorkerExtendedOutput.componentOf,Airbender.NativeWorkerExtendedOutput.resultLimb,sourceData,inputSyntax,linearSyntax,Expression.eval,environment,Airbender.NativeWorkerDiagonalG.cLimb,Airbender.NativeWorkerDiagonalG.cInput,Airbender.NativeWorkerDiagonalG.dLimb,Airbender.NativeWorkerDiagonalG.dByte,Airbender.NativeWorkerDiagonalG.carry,Airbender.NativeWorkerDiagonalCB.cLimb,Airbender.NativeWorkerDiagonalCB.cInput,Airbender.NativeWorkerDiagonalCB.dLimb,Airbender.NativeWorkerDiagonalCB.dByte,Airbender.NativeWorkerDiagonalCB.carry,Airbender.NativeWorkerDiagonalFirst.inputLimb,Airbender.NativeWorkerDiagonalFirst.columnLimb,Airbender.NativeWorkerDiagonalFirst.sourceColumn,Airbender.NativeWorkerSecondCB.cLimb,Airbender.NativeWorkerSecondCB.cInput,Airbender.NativeWorkerSecondCB.dLimb,Airbender.NativeWorkerSecondCB.dByte,Airbender.NativeWorkerSecondCB.carry,Airbender.NativeWorkerCB.cLimb,Airbender.NativeWorkerCB.cInput,Airbender.NativeWorkerCB.dLimb,Airbender.NativeWorkerCB.dByte,Airbender.NativeWorkerCB.carry,Airbender.NativeWorkerInitial.observed,Airbender.NativeWorkerInitial.initialColumns]
    ring_nf
    simp
private theorem base97 (w : Nat → F) (j : Fin 8) :
    (query w (second j) 0)[1]+512*(query w (second j) 1)[1] = nativeBase w (second j) := by
  rw [value1,value1]
  fin_cases j
  all_goals
    simp [second,nativeBase,sourceData,inputSyntax,linearSyntax,Expression.eval,environment]
    ring_nf
    simp
private theorem b97 (w : Nat → F) (j : Fin 8) :
    (query w (second j) 0)[0]+512*(query w (second j) 1)[0] = resultValue w (second j) false := by
  rw [value0,value0]
  fin_cases j
  all_goals
    simp [second,nativeWord,resultValue,Airbender.NativeWorkerExtendedOutput.diagonalOf,Airbender.NativeWorkerExtendedOutput.componentOf,Airbender.NativeWorkerExtendedOutput.resultLimb,sourceData,inputSyntax,Expression.eval,environment,Airbender.NativeWorkerExtendedOutput.bLimb]
private theorem d88 (w : Nat → F) (j : Fin 8) :
    (query w (second j) 2)[0]+256*(query w (second j) 3)[0] = resultValue w (second j) true := by
  rw [value0,value0]
  fin_cases j
  all_goals
    simp [second,nativeWord,resultValue,Airbender.NativeWorkerExtendedOutput.diagonalOf,Airbender.NativeWorkerExtendedOutput.componentOf,Airbender.NativeWorkerExtendedOutput.resultLimb,sourceData,inputSyntax,Expression.eval,environment,Airbender.NativeWorkerDiagonalG.dLimb,Airbender.NativeWorkerDiagonalG.dByte]
private theorem a79 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (j : Fin 8) :
    (query w (first j) 2)[1]+128*(query w (first j) 3)[1] = resultValue w (first j) false := by
  have eq := split_equation holds (first j)
  rw [value1,value1]
  fin_cases j
  all_goals
    simp [first,linearSyntax,splitTerms,Expression.eval,environment] at eq
    simp [first,nativeWord,resultValue,Airbender.NativeWorkerExtendedOutput.diagonalOf,Airbender.NativeWorkerExtendedOutput.componentOf,Airbender.NativeWorkerExtendedOutput.resultLimb,sourceData,inputSyntax,linearSyntax,Expression.eval,environment,Airbender.NativeWorkerDiagonalAD.sumLimb,Airbender.NativeWorkerDiagonalAD.bInput,Airbender.NativeWorkerDiagonalAD.carry,Airbender.NativeWorkerDiagonalFirst.sumLimb,Airbender.NativeWorkerDiagonalFirst.carry,Airbender.NativeWorkerDiagonalFirst.inputLimb,Airbender.NativeWorkerDiagonalFirst.columnLimb,Airbender.NativeWorkerDiagonalFirst.sourceColumn,Airbender.NativeWorkerDiagonalFirst.bLimb,Airbender.NativeWorkerSecondAD.sumLimb,Airbender.NativeWorkerSecondAD.bInput,Airbender.NativeWorkerSecondAD.carry,Airbender.NativeWorkerFirstG.sumLimb,Airbender.NativeWorkerFirstG.carry,Airbender.NativeWorkerInitial.observed,Airbender.NativeWorkerInitial.initialColumns,Airbender.NativeWorkerSchedule.selected]
    linear_combination (norm := skip) -eq
    ring_nf
    simp
private theorem middle79 (w : Nat → F) (j : Fin 8) :
    (query w (first j) 2)[0]+128*(query w (first j) 3)[0] =
      (query w (first j) 0)[2]+128*(query w (first j) 1)[2] := by
  rw [value0,value0,value2,value2]
  fin_cases j <;> simp [first,sourceData,inputSyntax,Expression.eval,environment]
private theorem middle88 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (j : Fin 8) :
    (query w (second j) 2)[1]+256*(query w (second j) 3)[1] =
      (query w (second j) 0)[2]+512*(query w (second j) 1)[2] := by
  have eq := split_equation holds (second j)
  rw [value1,value1,value2,value2]
  fin_cases j
  all_goals
    simp [second,linearSyntax,splitTerms,Expression.eval,environment] at eq
    simp [second,sourceData,inputSyntax,linearSyntax,Expression.eval,environment]
    linear_combination -eq
private theorem final_value (w : Nat → F) (j : Fin 16) :
    (query w j 2)[2]+(if j.val < 8 then 128 else 256)*(query w j 3)[2] = finalValue w j := by
  rw [value2,value2]
  fin_cases j <;> simp [sourceData,inputSyntax,Expression.eval,environment,finalValue]
private theorem swap_xor (a b c : BitVec 16) : (a ^^^ c) ^^^ b = (a ^^^ b) ^^^ c := by
  rw [BitVec.xor_assoc,BitVec.xor_comm c b,← BitVec.xor_assoc]

private theorem ac_xor {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) (j : Fin 8) :
    BitVec.ofNat 16 (finalValue w (first j)).val =
      (BitVec.ofNat 16 (nativeBase w (first j)).val ^^^ BitVec.ofNat 16 (resultValue w (first j) false).val) ^^^
        BitVec.ofNat 16 (resultValue w (first j) true).val := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  have e0 : PairEffects (query w (first j) 0) 7 := by simpa [width,first,j.isLt] using query_effects effects (first j) 0
  have e1 : PairEffects (query w (first j) 1) 9 := by simpa [width,first,j.isLt] using query_effects effects (first j) 1
  have e2 : PairEffects (query w (first j) 2) 7 := by simpa [width,first,j.isLt] using query_effects effects (first j) 2
  have e3 : PairEffects (query w (first j) 3) 9 := by simpa [width,first,j.isLt] using query_effects effects (first j) 3
  have stage := xor79 _ _ e0 e1
  have finish := xor79 _ _ e2 e3
  have out : (query w (first j) 2)[2]+128*(query w (first j) 3)[2] = finalValue w (first j) := by
    simpa [first,j.isLt] using final_value w (first j)
  rw [out,middle79,stage,base79,c79,a79 holds] at finish
  exact finish.trans (swap_xor _ _ _)

private theorem bd_xor {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) (j : Fin 8) :
    BitVec.ofNat 16 (finalValue w (second j)).val =
      (BitVec.ofNat 16 (nativeBase w (second j)).val ^^^ BitVec.ofNat 16 (resultValue w (second j) false).val) ^^^
        BitVec.ofNat 16 (resultValue w (second j) true).val := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  have large : ¬ (second j).val < 8 := by simp only [second]; omega
  have e0 : PairEffects (query w (second j) 0) 9 := by simpa [width,large] using query_effects effects (second j) 0
  have e1 : PairEffects (query w (second j) 1) 7 := by simpa [width,large] using query_effects effects (second j) 1
  have e2 : PairEffects (query w (second j) 2) 8 := by simpa [width,large] using query_effects effects (second j) 2
  have e3 : PairEffects (query w (second j) 3) 8 := by simpa [width,large] using query_effects effects (second j) 3
  have stage := xor97 _ _ e0 e1
  have finish := xor88 _ _ e2 e3
  have out : (query w (second j) 2)[2]+256*(query w (second j) 3)[2] = finalValue w (second j) := by
    simpa only [if_neg large] using final_value w (second j)
  rw [out,middle88 holds,stage,b97,base97,d88] at finish
  rw [BitVec.xor_comm (BitVec.ofNat 16 (resultValue w (second j) true).val),
    BitVec.xor_comm (BitVec.ofNat 16 (resultValue w (second j) false).val)] at finish
  exact finish

theorem xor_limb {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) (j : Fin 16) :
    BitVec.ofNat 16 (finalValue w j).val =
      (BitVec.ofNat 16 (nativeBase w j).val ^^^ BitVec.ofNat 16 (resultValue w j false).val) ^^^
        BitVec.ofNat 16 (resultValue w j true).val := by
  by_cases small : j.val < 8
  · exact ac_xor holds ⟨j.val,small⟩
  · have same : second ⟨j.val-8,by have := j.isLt; omega⟩ = j := by
      apply Fin.ext
      change 8+(j.val-8) = j.val
      omega
    rw [← same]
    exact bd_xor holds _

private theorem base_value {w : Nat → F} (initial : Airbender.NativeWorkerInitial.RowEffects w)
    (word : Fin 8) (limb : Fin 2) :
    nativeBase w ⟨2*word.val+limb.val,by have := word.isLt; have := limb.isLt; omega⟩ =
      Airbender.NativeWorkerInitial.finalBase w word limb := by
  change w (154+2*(2*word.val+limb.val)) = _
  rw [show 154+2*(2*word.val+limb.val)=154+4*word.val+2*limb.val by omega]
  exact initial.bases word limb

private theorem result_value {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (word : Fin 8) (limb : Fin 2) (upper : Bool) :
    Airbender.NativeWorkerExtendedOutput.writeLimb w ⟨(if upper then 8 else 0)+word.val,by have := word.isLt; cases upper <;> simp <;> omega⟩ limb =
      resultValue w ⟨2*word.val+limb.val,by have := word.isLt; have := limb.isLt; omega⟩ upper := by
  let j : Fin 16 := ⟨2*word.val+limb.val,by have := word.isLt; have := limb.isLt; omega⟩
  have h := Airbender.NativeWorkerExtendedOutputProofs.limbs holds (Airbender.NativeWorkerExtendedOutput.diagonalOf (nativeWord j upper))
    (Airbender.NativeWorkerExtendedOutput.componentOf (nativeWord j upper)) ⟨j.val%2,by omega⟩
  rw [Airbender.NativeWorkerExtendedOutputProofs.destination_inverse] at h
  have coord : nativeWord j upper = (⟨(if upper then 8 else 0)+word.val,by have := word.isLt; cases upper <;> simp <;> omega⟩ : Fin 16) := by
    apply Fin.ext
    dsimp only [nativeWord,j]
    have := limb.isLt
    omega
  have part : (⟨j.val%2,by omega⟩ : Fin 2) = limb := by
    apply Fin.ext
    dsimp only [j]
    have := limb.isLt
    omega
  change _ = resultValue w j upper
  exact (congrArg (fun index => Airbender.NativeWorkerExtendedOutput.writeLimb w index limb) coord).symm.trans (by simpa only [resultValue,part] using h)

private theorem index0 (word : Fin 8) :
    (⟨2*word.val+(0 : Fin 2).val,by have := word.isLt; have := (0 : Fin 2).isLt; omega⟩ : Fin 16) =
      ⟨2*word.val,by have := word.isLt; omega⟩ := by
  apply Fin.ext
  change 2*word.val+(0 : Fin 2).val = 2*word.val
  rw [show (0 : Fin 2).val = 0 from rfl]
  omega
private theorem index1 (word : Fin 8) :
    (⟨2*word.val+(1 : Fin 2).val,by have := word.isLt; have := (1 : Fin 2).isLt; omega⟩ : Fin 16) =
      ⟨2*word.val+1,by have := word.isLt; omega⟩ := by
  apply Fin.ext
  change 2*word.val+(1 : Fin 2).val = 2*word.val+1
  rw [show (1 : Fin 2).val = 1 from rfl]

theorem xor_word {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) (word : Fin 8) :
    pack (finalValue w ⟨2*word.val,by have := word.isLt; omega⟩)
      (finalValue w ⟨2*word.val+1,by have := word.isLt; omega⟩) = xorResult w word := by
  have initial := Airbender.NativeWorkerInitialProofs.row holds
  have low := xor_limb holds (⟨2*word.val,by have := word.isLt; omega⟩ : Fin 16)
  have high := xor_limb holds (⟨2*word.val+1,by have := word.isLt; omega⟩ : Fin 16)
  have b0 := base_value initial word 0
  have b1 := base_value initial word 1
  have r00 := result_value holds word 0 false
  have r01 := result_value holds word 0 true
  have r10 := result_value holds word 1 false
  have r11 := result_value holds word 1 true
  rw [index0 word] at b0 r00 r01
  rw [index1 word] at b1 r10 r11
  simp at r00 r01 r10 r11
  rw [b0,← r00,← r01] at low
  rw [b1,← r10,← r11] at high
  unfold pack
  rw [low,high]
  simp only [xorResult,baseWord,Airbender.NativeWorkerExtendedOutput.writeWord,pack]
  exact word_xor _ _ _ _ _ _
private theorem block2 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock2 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock2 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup) := List.sublist_append_right _ _
  exact ((((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

private def finishSlot (word : Fin 8) : Fin 43 := ⟨1+word.val,by have := word.isLt; omega⟩
private theorem finish_columns (word : Fin 8) :
    (memoryAccess (finishSlot word)).readValue = #v[4+4*word.val,5+4*word.val] ∧
    (memoryAccess (finishSlot word)).writeValue = some #v[6+4*word.val,7+4*word.val] := by
  fin_cases word <;> decide +kernel

private theorem finish_value (w : Nat → F) (word : Fin 8) (write : Bool) (limb : Fin 2) :
    (keyValue w (finishSlot word) write)[limb] = w ((if write then 6 else 4)+4*word.val+limb.val) := by
  have columns := finish_columns word
  cases write <;> fin_cases limb <;> simp [keyValue,columns.1,columns.2,Nat.add_assoc]
  all_goals exact congrArg w (by omega)

theorem write_value (w : Nat → F) (word : Fin 8) (limb : Fin 2) :
    (keyValue w ⟨1+word.val,by have := word.isLt; omega⟩ true)[limb] = writeLimb w word limb :=
  finish_value w word true limb

private def quadraticSyntax (row : List (Int × Nat) × List (Int × Nat × Nat)) : Expression F :=
  row.2.foldl (fun e t => .add e (.mul (.mul (.mul (.const 1) (.const (t.1 : F))) (.var ⟨t.2.1⟩)) (.var ⟨t.2.2⟩)))
    (.add (.const 0) (linearSyntax row.1))
private def gateData : Vector (List (Int × Nat) × List (Int × Nat × Nat)) 18 := #v[
([(-1,151)],[(1,138,147)]),
([(1,150),(1,151),(-1,152)],[(-1,150,151)]),
([(1,4),(-1,6)],[(1,633,152),(128,634,152),(-1,152,4)]),
([(1,5),(-1,7)],[(1,640,152),(128,641,152),(-1,152,5)]),
([(1,8),(-1,10)],[(1,647,152),(128,648,152),(-1,152,8)]),
([(1,9),(-1,11)],[(1,654,152),(128,655,152),(-1,152,9)]),
([(1,12),(-1,14)],[(1,661,152),(128,662,152),(-1,152,12)]),
([(1,13),(-1,15)],[(1,668,152),(128,669,152),(-1,152,13)]),
([(1,16),(-1,18)],[(1,675,152),(128,676,152),(-1,152,16)]),
([(1,17),(-1,19)],[(1,682,152),(128,683,152),(-1,152,17)]),
([(1,20),(-1,22)],[(1,689,152),(256,690,152),(-1,152,20)]),
([(1,21),(-1,23)],[(1,696,152),(256,697,152),(-1,152,21)]),
([(1,24),(-1,26)],[(1,703,152),(256,704,152),(-1,152,24)]),
([(1,25),(-1,27)],[(1,710,152),(256,711,152),(-1,152,25)]),
([(1,28),(-1,30)],[(1,717,152),(256,718,152),(-1,152,28)]),
([(1,29),(-1,31)],[(1,724,152),(256,725,152),(-1,152,29)]),
([(1,32),(-1,34)],[(1,731,152),(256,732,152),(-1,152,32)]),
([(1,33),(-1,35)],[(1,738,152),(256,739,152),(-1,152,33)])]
private theorem selector_shape (setup : Table F (fields 4)) (i : Fin 2) :
    (FlatOperation.constraints (constraintsBlock2 setup)).get ⟨40 + i.val,by change 40 + i.val < 64; have := i.isLt; omega⟩ = quadraticSyntax gateData[(⟨i.val,by have := i.isLt; omega⟩ : Fin 18)] := by
  fin_cases i <;> rfl
private theorem write_shape (setup : Table F (fields 4)) (j : Fin 16) :
    (FlatOperation.constraints (constraintsBlock4 setup)).get ⟨29+j.val,by change 29+j.val < 64; have := j.isLt; omega⟩ = quadraticSyntax gateData[(⟨2+j.val,by have := j.isLt; omega⟩ : Fin 18)] := by
  fin_cases j <;> rfl
private theorem selector_equation {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 2) :
    (quadraticSyntax gateData[(⟨i.val,by have := i.isLt; omega⟩ : Fin 18)]).eval (environment w) = 0 := by
  rw [← selector_shape setup i]
  exact assertion_of_holds (block2 holds) _
private theorem write_equation {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (j : Fin 16) :
    (quadraticSyntax gateData[(⟨2+j.val,by have := j.isLt; omega⟩ : Fin 18)]).eval (environment w) = 0 := by
  rw [← write_shape setup j]
  exact assertion_of_holds (block4 holds) _

private theorem gate_formula {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    w 152 = w 150+w 138*w 147-w 150*(w 138*w 147) := by
  have mul := selector_equation holds 0
  have combine := selector_equation holds 1
  simp [gateData,quadraticSyntax,linearSyntax,Expression.eval,environment] at mul combine
  linear_combination -combine-(1-w 150)*mul
private theorem natural_gate (a b c : Nat) (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) :
    (c : F)+(a : F)*(b : F)-(c : F)*((a : F)*(b : F)) = if c = 1 ∨ (a = 1 ∧ b = 1) then 1 else 0 := by
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;>
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> simp

theorem selector {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    w 152 = if performFinal w then 1 else 0 := by
  have initial := Airbender.NativeWorkerInitialProofs.row holds
  have a : w 138 = (Airbender.NativeWorkerSchedule.inputBit w 0 : F) := by simpa using initial.schedule.flags 0
  have b : w 147 = (Airbender.NativeWorkerSchedule.inputBit w 9 : F) := by simpa using initial.schedule.flags 9
  have c : w 150 = (Airbender.NativeWorkerSchedule.inputBit w 12 : F) := by simpa using initial.schedule.flags 12
  rw [gate_formula holds,a,b,c]
  have bound (slot : Fin 13) : Airbender.NativeWorkerSchedule.inputBit w slot ≤ 1 := by
    unfold Airbender.NativeWorkerSchedule.inputBit
    have := Nat.mod_lt ((w 135).val/2^slot.val) (by decide : 0<2)
    omega
  simpa [performFinal] using natural_gate _ _ _ (bound 0) (bound 9) (bound 12)

private theorem gated_limb {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (word : Fin 8) (limb : Fin 2) :
    writeLimb w word limb = finalValue w ⟨2*word.val+limb.val,by have := word.isLt; have := limb.isLt; omega⟩*w 152 +
      Airbender.NativeWorkerSchedule.state w word limb*(1-w 152) := by
  have eq := write_equation holds ⟨2*word.val+limb.val,by have := word.isLt; have := limb.isLt; omega⟩
  fin_cases word <;> fin_cases limb
  all_goals
    simp [gateData,quadraticSyntax,linearSyntax,Expression.eval,environment] at eq
    simp [writeLimb,finalValue,Airbender.NativeWorkerSchedule.state]
    linear_combination -eq

theorem by_gate {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) (word : Fin 8) :
    writeWord w word = if w 152 = 1 then xorResult w word else readWord w word := by
  have low := gated_limb holds word 0
  have high := gated_limb holds word 1
  rw [index0 word] at low
  rw [index1 word] at high
  rcases Airbender.NativeWorkerWriteSliceProofs.finalization_bit holds with zero | one
  · simp only [zero,mul_zero,sub_zero,mul_one,zero_add] at low high
    simp only [zero,zero_ne_one,if_false,writeWord,readWord,pack]
    rw [low,high]
  · simp only [one,mul_one,sub_self,mul_zero,add_zero] at low high
    simp only [one,ite_true,writeWord]
    rw [low,high]
    exact xor_word holds word

theorem finalization {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    LocalEffects w := by
  have gate := selector holds
  refine ⟨gate,?_⟩
  intro word
  rw [by_gate holds word,gate]
  cases performFinal w <;> simp

theorem row {w : Nat → F} (prior : Airbender.NativeWorkerExtendedOutput.RowEffects w)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    Airbender.NativeWorkerFinalization.RowEffects w := by
  have effects := finalization holds
  exact ⟨prior,effects.selector,effects.finalized⟩
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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerFinalization.RowEffects w := by
  have prior := Airbender.NativeWorkerExtendedOutputProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted.counted.component
  exact ⟨prior.1,fun w member => row (prior.2 w member) (processing w member).body⟩
end Airbender.NativeWorkerFinalizationProofs
