import Airbender.Review.Circuits.ReducedMachine.CallerValidity
import Airbender.Proofs.ReducedMachine.NativeCallerMixedQueries
import Airbender.Proofs.ReducedMachine.NativeRuntimeQueries
import Airbender.Proofs.ReducedMachine.NativeConditionalTable
import Airbender.Proofs.ReducedMachine.NativeRuntimeQueryTransport

namespace Airbender.NativeCallerValidityProofs
open Airbender.NativeCallerRequests (F)
open Airbender.NativeCallerMixedQueries Airbender.ReducedMachine.Native Airbender.Verification Airbender.Trace
open Airbender.ReducedMachine
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
private def tagDomain : List Nat := [0,4,6,7,16,17,18,20,22,23,24,25,37,47]

private theorem tag_facts (n : Nat) (member : n ∈ tagDomain) :
    n ≤ 47 ∧ (37 < n → n = 47) ∧ n ≠ 5 ∧ n ≠ 27 := by
  simp [tagDomain] at member
  omega

private theorem tag_pair (a b : Nat) (ma : a ∈ tagDomain) (mb : b ∈ tagDomain)
    (same : a = b + 25) : b = 0 ∨ b = 22 := by
  simp [tagDomain] at ma mb
  omega

/-- Pure finite-tag arithmetic before field/source instantiation. -/
theorem tag_patterns (a c load shift jump q0 q1 q3 : Nat)
    (ba : a ≤ 1) (bc : c ≤ 1) (bl : load ≤ 1) (bs : shift ≤ 1) (bj : jump ≤ 1)
    (m0 : q0 ∈ tagDomain) (m1 : q1 ∈ tagDomain) (m3 : q3 ∈ tagDomain)
    (first : q0 = q3 + 17*a + 25 + 17*c + 23*load + 27*shift + 18*jump)
    (second : q1 = q3 + 22*a + 24*load + 17*shift + 23*jump) :
    a = 0 ∧ c = 0 ∧ load = 0 ∧ shift = 0 ∧ jump = 0 ∧ (q3 = 0 ∨ q3 = 22) := by
  obtain ⟨upper,large,notFive,_⟩ := tag_facts q0 m0
  have q3NotFive := (tag_facts q3 m3).2.2.1
  have q1Not27 := (tag_facts q1 m1).2.2.2
  have l : load = 0 := by omega
  have s : shift = 0 := by omega
  have aa : a = 0 := by
    by_contra nonzero
    have one : a = 1 := by omega
    have high : 37 < q0 := by omega
    have eq := large high
    have cZero : c = 0 := by omega
    have jZero : jump = 0 := by omega
    omega
  have cc : c = 0 := by
    by_contra nonzero
    have one : c = 1 := by omega
    have high : 37 < q0 := by omega
    have eq := large high
    omega
  have j : jump = 0 := by
    by_contra nonzero
    have one : jump = 1 := by omega
    have high : 37 < q0 := by omega
    have eq := large high
    omega
  exact ⟨aa,cc,l,s,j,tag_pair q0 q3 m0 m3 (by omega)⟩

private theorem bit_of_bound (x : F) (bound : x.val ≤ 1) : x = 0 ∨ x = 1 := by
  have one : (1 : F).val = 1 := by decide +kernel
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp bound with zero | value
  · left; apply ZMod.val_injective; simpa using zero
  · right; apply ZMod.val_injective; simpa only [one] using value

private theorem tag_equations {w : Nat → F} (effect : RowEffects w) :
    w 103 = w 115 + 17*w 23 + 25*w 24 + 17*w 25 + 23*w 27 + 27*w 29 + 18*w 31 ∧
    w 107 = w 115 + 22*w 23 + 24*w 27 + 17*w 29 + 23*w 31 := by
  have a := congrArg (fun q => q[3]) (effect.exact 0)
  have b := congrArg (fun q => q[3]) (effect.exact 1)
  have c := congrArg (fun q => q[3]) (effect.exact 3)
  simp [query,normalized] at a b c
  constructor
  · linear_combination a-c
  · linear_combination b-c

/-- Native finite tag restrictions, retaining free funct3 and all raw fields. -/
theorem selector_patterns {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (csr : w 24 = 1) :
    w 23 = 0 ∧ w 25 = 0 ∧ w 27 = 0 ∧ w 29 = 0 ∧ w 31 = 0 ∧ (w 115 = 0 ∨ w 115 = 22) := by
  have a := NativeSelectorProofs.bit_bounds holds ⟨6,by decide⟩
  have c := NativeSelectorProofs.bit_bounds holds ⟨8,by decide⟩
  have l := NativeSelectorProofs.bit_bounds holds ⟨10,by decide⟩
  have s := NativeSelectorProofs.bit_bounds holds ⟨12,by decide⟩
  have j := NativeSelectorProofs.bit_bounds holds ⟨14,by decide⟩
  change (w 23).val ≤ 1 at a
  change (w 25).val ≤ 1 at c
  change (w 27).val ≤ 1 at l
  change (w 29).val ≤ 1 at s
  change (w 31).val ≤ 1 at j
  have m0 : (w 103).val ∈ tagDomain := NativeRuntimeQueryProofs.dynamic_selectors holds 0
  have m1 : (w 107).val ∈ tagDomain := NativeRuntimeQueryProofs.dynamic_selectors holds 1
  have m3 : (w 115).val ∈ tagDomain := NativeRuntimeQueryProofs.dynamic_selectors holds 3
  have upper := (tag_facts _ m3).1
  obtain ⟨first,second⟩ := tag_equations (Airbender.NativeCallerMixedQueryProofs.body holds)
  have n0 : (w 103).val = (w 115).val + 17*(w 23).val + 25 + 17*(w 25).val +
      23*(w 27).val + 27*(w 29).val + 18*(w 31).val := by
    apply Arithmetic.bounded_nat_eq (F := F) (p := mersenne31Modulus) (ZMod.val_lt _)
      (by change _ < 2147483647; omega)
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val]
    simpa only [csr,mul_one] using first
  have n1 : (w 107).val = (w 115).val + 22*(w 23).val + 24*(w 27).val +
      17*(w 29).val + 23*(w 31).val := by
    apply Arithmetic.bounded_nat_eq (F := F) (p := mersenne31Modulus) (ZMod.val_lt _)
      (by change _ < 2147483647; omega)
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val] using second
  obtain ⟨aa,cc,ll,ss,jj,rest⟩ := tag_patterns _ _ _ _ _ _ _ _ a c l s j m0 m1 m3 n0 n1
  have cast (x : F) (n : Nat) (same : x.val = n) : x = (n : F) := by
    rw [← same,ZMod.natCast_zmod_val]
  exact ⟨cast _ _ aa,cast _ _ cc,cast _ _ ll,cast _ _ ss,cast _ _ jj,
    rest.elim (fun h => Or.inl (cast _ _ h)) (fun h => Or.inr (cast _ _ h))⟩

private theorem zero_columns : NativeFixed.dataT0.columns =
    #v[(⟨#[.dense #[0]]⟩ : Setup.Column),⟨#[.dense #[0]]⟩,⟨#[.dense #[0]]⟩,⟨#[.dense #[0]]⟩] := rfl

/-- Actual zero-region membership fixes the entire tuple, not just its tag. -/
theorem zero_tuple (q : Vector F 4) (member : NativeRuntimePool.table.Contains #[] q)
    (tag : q[3] = 0) : q = #v[0,0,0,0] := by
  obtain ⟨i,same⟩ := NativeRuntimePoolProofs.selected_region q member .zero tag
  have h : i.val = 0 := by have bound := i.isLt; change i.val < 1 at bound; omega
  have index : i = ⟨0,by change 0 < 1; decide⟩ := Fin.ext h
  subst i
  have row : ((NativeRuntimePoolProofs.regionData .zero).row ⟨0,by change 0 < 1; decide⟩ : Vector F 4) = #v[0,0,0,0] := by
    simp [NativeRuntimePoolProofs.regionData,NativePoolProofs.Region.data,Setup.TableData.row,
      Setup.TableData.rowNat,zero_columns,Setup.Column.get?,Setup.getFromBlocks,Setup.Block.get?,Setup.Block.length]
  exact same.trans row

/-- Every tag22 output is Boolean, including inconsistent packed comparison flags. -/
theorem comparison_boolean (q : Vector F 4) (member : NativeRuntimePool.table.Contains #[] q)
    (tag : q[3] = 22) : q[2] = 0 ∨ q[2] = 1 := by
  have other : q[3] ≠ 25 := by rw [tag]; decide +kernel
  have fixed := NativeRuntimeQueryTransportProofs.outside_csr q member other
  obtain ⟨i,same⟩ := NativeConditionalTableProofs.result q fixed tag
  have output := congrArg (fun v : Vector F 4 => v[2]) same
  simp only [conditionalRow,Vector.getElem_map] at output
  split_ifs at output <;> simp_all

/-- Exclude the tag47/tag22 alternative using both actual stored outputs. -/
theorem selector_isolation {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (csr : w 24 = 1) :
    w 23 = 0 ∧ w 25 = 0 ∧ w 27 = 0 ∧ w 29 = 0 ∧ w 31 = 0 ∧ w 115 = 0 := by
  obtain ⟨aa,cc,ll,ss,jj,normal | alternative⟩ := selector_patterns holds csr
  · exact ⟨aa,cc,ll,ss,jj,normal⟩
  · have effect := Airbender.NativeCallerMixedQueryProofs.runtime holds
    have mem (slot : Fin 4) : NativeRuntimePool.table.Contains #[] (query w slot) := by
      rw [effect.queries.exact slot]
      exact effect.membership slot
    have supported : w 64 = 1 := by
      simpa only [csr,one_mul] using (Airbender.NativeCallerRequestProofs.relations holds).1
    have last := congrArg (fun q => q[3]) (effect.queries.exact 3)
    simp [query,normalized,ss,alternative] at last
    have b := bit_of_bound (w 22) (NativeSelectorProofs.bit_bounds holds ⟨5,by decide⟩)
    have binop : w 22 = 1 := by
      rcases b with off | on
      · have impossible : (0 : F) ≠ 22 := by decide +kernel
        exact False.elim (impossible (by simpa only [off,mul_zero] using last.symm))
      · exact on
    have firstTag := (tag_equations effect.queries).1
    have tag47 : (query w 0)[3] = 47 := by
      simp [query]
      have closed : (22 : F) + 25 = 47 := by decide +kernel
      simpa [aa,cc,ll,ss,jj,csr,alternative,closed] using firstTag
    have other : (query w 0)[3] ≠ 25 := by rw [tag47]; decide +kernel
    have fixed := NativeRuntimeQueryTransportProofs.outside_csr (query w 0) (mem 0) other
    have outputZero := (NativeTruncationProofs.result (query w 0) fixed tag47).2.2
    change w 102 = 0 at outputZero
    have output := congrArg (fun q => q[2]) (effect.queries.exact 0)
    simp [query,normalized,csr,aa,cc,ll,ss,jj,supported,binop] at output
    have negative : w 65 = -1 := by linear_combination outputZero-output
    have tag22 : (query w 1)[3] = 22 := by
      have h := (tag_equations effect.queries).2
      simp [query]
      simpa [aa,ll,ss,jj,alternative] using h
    have binary := comparison_boolean (query w 1) (mem 1) tag22
    have next := congrArg (fun q => q[2]) (effect.queries.exact 1)
    simp [query,normalized,aa,ll,ss,jj,binop] at next
    change w 106 = 0 ∨ w 106 = 1 at binary
    have impossible : ¬ ((-1 : F) = 0 ∨ (-1 : F) = 1) := by decide +kernel
    exact False.elim (impossible (by simpa only [next,negative] using binary))

/-- A nonzero actual request forces weight1, raw CSR1991, bounded ABI and
    zero competing lookup flags. No activity or valid full mask is assumed. -/
theorem requested {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (present : (csrRequest w).multiplicity ≠ 0) :
    w 92 = 1 ∧ w 9 = 1991 ∧ w 65 = 1 ∧ (w 36).val < 65536 ∧
      w 22 = 0 ∧ w 23 = 0 ∧ w 25 = 0 ∧ w 27 = 0 ∧ w 29 = 0 ∧ w 31 = 0 := by
  have effect := Airbender.NativeCallerMixedQueryProofs.runtime holds
  obtain ⟨csr,delegate⟩ := effect.queries.caller.requested.mp present
  obtain ⟨_,_,supported,_⟩ := effect.queries.caller.present present
  obtain ⟨aa,cc,ll,ss,jj,last⟩ := selector_isolation holds csr
  have mem (slot : Fin 4) : NativeRuntimePool.table.Contains #[] (query w slot) := by
    rw [effect.queries.exact slot]
    exact effect.membership slot
  have nextTag : (query w 1)[3] = 0 := by
    have h := (tag_equations effect.queries).2
    simp [query]
    simpa [aa,ll,ss,jj,last] using h
  have zero := zero_tuple (query w 1) (mem 1) nextTag
  have outputZero := congrArg (fun q => q[2]) zero
  change w 106 = 0 at outputZero
  have output := congrArg (fun q => q[2]) (effect.queries.exact 1)
  simp [query,normalized,aa,ll,ss,jj] at output
  have product : w 22 * w 65 = 0 := output.symm.trans outputZero
  have binop : w 22 = 0 := (mul_eq_zero.mp product).resolve_right delegate
  have first : query w 0 = #v[w 9,1,w 65,25] := by
    rw [effect.queries.exact 0]
    simp [normalized,csr,aa,cc,ll,ss,jj,binop,supported]
  have membership : NativeRuntimePool.table.Contains #[] #v[w 9,1,w 65,25] := by
    rw [← first]
    exact mem 0
  have values := NativeRuntimeCSRProofs.values (NativeRuntimePoolProofs.csr_member _ membership rfl)
  have key : (w 9).val = 1991 := by
    by_contra different
    have disabled : w 65 = 0 := by simpa [NativeRuntimeCSR.delegated,different] using values.2.2
    exact delegate disabled
  have rawKey : w 9 = (1991 : F) := by
    have h := congrArg (fun n : Nat => (n : F)) key
    simpa only [ZMod.natCast_zmod_val,Nat.cast_ofNat] using h
  have one : w 65 = 1 := by simpa [NativeRuntimeCSR.delegated,key] using values.2.2
  have multiplicity : w 92 = 1 := by
    simpa [csrRequest,NativeCSRFieldProofs.request_columns,csr,one] using effect.queries.caller.multiplicity
  exact ⟨multiplicity,rawKey,one,(NativeRuntimeQueryProofs.results holds).1,binop,aa,cc,ll,ss,jj⟩

/-- Full native BODY derives the complete zero-or-one request shape. -/
theorem body {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table)) :
    Airbender.NativeCallerValidity.RowEffects w := by
  have prior := Airbender.NativeCallerMixedQueryProofs.runtime holds
  have rel := Airbender.NativeCallerRequestProofs.relations holds
  have requests : csrRequest w = ⟨0,0,some 0,3⟩ ∨ csrRequest w = ⟨1,1991,some (w 36),3⟩ := by
    by_cases zero : (csrRequest w).multiplicity = 0
    · have m : w 92 = 0 := by simpa [csrRequest,NativeCSRFieldProofs.request_columns] using zero
      have k : w 94 = 0 := by simpa [m] using rel.2.2.2.1
      have o : w 93 = 0 := by simpa [m] using rel.2.2.1
      left
      simp [csrRequest,NativeCSRFieldProofs.request_columns,m,k,o]
    · obtain ⟨m,key,_,_⟩ := requested holds zero
      have k : w 94 = 1991 := by simpa [m,key] using rel.2.2.2.1
      have o : w 93 = w 36 := by simpa [m] using rel.2.2.1
      right
      simp [csrRequest,NativeCSRFieldProofs.request_columns,m,k,o]
  refine ⟨prior,?_,requests,?_,?_⟩
  · exact requests.elim (fun h => Or.inl (congrArg CSRRequest.multiplicity h))
      (fun h => Or.inr (congrArg CSRRequest.multiplicity h))
  · intro present
    obtain ⟨_,key,delegate,bound,_⟩ := requested holds present
    exact ⟨key,delegate,bound⟩
  · intro present
    obtain ⟨_,_,_,_,a,b,c,d,e,f⟩ := requested holds present
    simp [Airbender.NativeCallerValidity.competing,a,b,c,d,e,f]

theorem all_rows {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    Airbender.NativeCallerValidity.Effects proofs := by
  have source : ∀ proof ∈ Airbender.NativeInitializationBatch.mainProofs proofs, ∀ i < callerAuxiliaryLayout.traceLength-1,
      Airbender.NativeCallerValidity.RowEffects (proof.rows i) := by
    intro proof member i bound
    obtain ⟨origin,present,rfl⟩ := List.mem_map.mp member
    exact body ((accepted.arguments.mainDelegation origin.main (List.mem_map.mpr ⟨origin,present,rfl⟩)).body i bound)
  exact Airbender.NativeActiveWorkerClockProofs.sampled_property
    (Airbender.NativeInitializationBatch.mainProofs proofs) (fun proof => proof.rows)
    (callerAuxiliaryLayout.traceLength-1) Airbender.NativeCallerValidity.RowEffects source


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
      Airbender.NativeCallerMixedQueries.Effects batch.main.proofs ∧
        Airbender.NativeCallerValidity.Effects batch.main.proofs := by
  have prior := Airbender.NativeCallerMixedQueryProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  exact ⟨prior.1,prior.2,all_rows embed memory ch pc gamma config accepted.counted.component⟩
end Airbender.NativeCallerValidityProofs
