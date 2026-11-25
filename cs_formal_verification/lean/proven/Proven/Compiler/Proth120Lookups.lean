module
import all Mathlib.Data.List.Sort
public import Proven.Compiler.Proth120Native
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Compiler.Proth120Native
set_option maxRecDepth 32768

/-- Source order is 15 ranges, 5 pooled vectors and 8 clocks. The native gates interleave
    these groups as rational pairs are materialized in successive layers. Index 20 is the decoder. -/
private def order : Vector (Fin 29) 28 :=
  #v[0,1,2,3,4,5,6,7,8,9,10,11,28,12,21,23,24,25,26,27,13,14,15,16,17,18,19,22]

private noncomputable def nativeAt (i : Fin 29) : Query := nativeQueries[i.val]'(show i.val < 29 from i.isLt)
private theorem inNative (i : Fin 29) : nativeAt i ∈ nativeQueries := List.getElem_mem _
private noncomputable def lookupAt (setup : Table F (fields 10)) (i : Fin 28) :=
  (FlatOperation.lookups (clockConstraints setup))[i.val]'(show i.val < 28 from i.isLt)
private def tableFor (setup : Table F (fields 10)) (group : Nat) : RawTable F :=
  match group with
  | 0 => setup.toRaw | 1 => Verification.range16Table.toRaw
  | _ => Trace.timestampTable.toRaw

private theorem tables (setup : Table F (fields 10)) (i : Fin 28) :
    (lookupAt setup i).table = tableFor setup (nativeAt (order[i])).group := by
  fin_cases i <;> rfl

private theorem bindings (setup : Table F (fields 10)) :
    (List.finRange 28).all (fun i =>
      let q := nativeAt order[i]
      q.enable.isNone && (q.group < 3) &&
        (q.group != 0 || q.fields[8]? == some [(0, [])]) &&
        fieldsCheck nativeCoordinates nativeScalar placements (lookupAt setup i).entry.toList q.fields) = true := by
  kernel_rfl

private def Member (table : RawTable F) (xs : List F) : Prop :=
  ∃ v : Vector F table.arity, xs = v.toList ∧ table.Contains #[] v

private theorem lookupOfMember {l : Lookup F} {w : Nat → F}
    (h : Member l.table (l.entry.toList.map (fun e => e.eval (Verification.environment w)))) :
    l.Contains (Verification.environment w) := by
  obtain ⟨v, same, mem⟩ := h
  have eq := Vector.toList_inj.mp (show (l.entry.map (fun e => e.eval (Verification.environment w))).toList = v.toList by rw [Vector.toList_map]; exact same)
  change l.table.Contains #[] (l.entry.map (fun e => e.eval (Verification.environment w)))
  rw [eq]
  exact mem

private theorem rawMembership {setup : Table F (fields 10)} {decode} {rows : PublicLookupRows setup decode}
    {physical} (matched : NativeLookupsMatched rows.generic physical) (q : Query) (present : q ∈ nativeQueries)
    (on : q.enable.isNone = true) (small : q.group < 3)
    (pad : (q.group != 0 || q.fields[8]? == some [(0, [])]) = true)
    (len : q.fields.length = (tableFor setup q.group).arity) :
    Member (tableFor setup q.group) (q.fields.map (value nativeScalar physical)) := by
  have enabled : (q.enable.map physical).getD 1 ≠ 0 := by rw [Option.isNone_iff_eq_none.mp on]; exact one_ne_zero
  have ok := matched q present enabled
  have groups : q.group = 0 ∨ q.group = 1 ∨ q.group = 2 := by omega
  rcases groups with h | h | h
  · simp only [h] at ok len pad ⊢
    change q.fields.length = 10 at len
    change Member setup.toRaw _
    let v : Vector F 10 := ⟨(q.fields.map (value nativeScalar physical)).toArray, by simpa using len⟩
    have vv : v.toList = q.fields.map (value nativeScalar physical) := by simp [v, Vector.toList]
    refine ⟨v, vv.symm, ?_⟩
    simp only [Table.toRaw, Array.map_empty]
    change setup.Contains #[] v
    apply rows.pooled v (vv.symm ▸ ok)
    have hz : q.fields[8]? = some [(0, [])] := by simpa using pad
    have he : v.toList[8]? = some 0 := by
      rw [vv, List.getElem?_map, hz]; rfl
    exact Option.some.inj ((List.getElem?_eq_getElem (by simp)).symm.trans he)
  · simp only [h] at ok ⊢
    obtain ⟨x, hx⟩ := ok
    exact ⟨#v[(x.val : F)], hx, x, rfl⟩
  · simp only [h] at ok ⊢
    obtain ⟨x, hx⟩ := ok
    exact ⟨#v[(x.val : F)], hx, x, rfl⟩

theorem native_lookup_holds {setup : Table F (fields 10)} {decode} {rows : PublicLookupRows setup decode}
    {physical logical} (native : NativeArithmetic physical logical) (matched : NativeLookupsMatched rows.generic physical) :
    ∀ l ∈ FlatOperation.lookups (clockConstraints setup), l.Contains (Verification.environment logical) := by
  intro l hl
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hl
  let i : Fin 28 := ⟨j.val, j.isLt⟩
  change (lookupAt setup i).Contains _
  let q := nativeAt order[i]
  have hb := List.all_eq_true.mp (bindings setup) i (List.mem_finRange _)
  obtain ⟨⟨⟨on, sz⟩, pad⟩, coeff⟩ :=
    (Bool.and_eq_true_iff.mp hb).imp_left (fun hx => (Bool.and_eq_true_iff.mp hx).imp_left Bool.and_eq_true_iff.mp)
  have eq := fields_value coeff native.2
  apply lookupOfMember
  rw [eq, tables setup i]
  apply rawMembership (rows := rows) matched q (inNative _) on (of_decide_eq_true sz) pad
  have same := congrArg List.length eq
  simpa [q, tables setup i] using same.symm

end Airbender.UnifiedReduced.Proth120
