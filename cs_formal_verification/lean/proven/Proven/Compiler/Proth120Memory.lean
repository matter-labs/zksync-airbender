module
public import Human.Trace.UnifiedReduced.Proth120Permutation
public import Human.Compiler.Proth120Native
public import Proven.GKRProtocol.NativeMemoryBridge
public import Proven.KernelRfl
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120.NativeRAM
open Compiler Trace NativeMemory NativeMemoryBridge
set_option maxRecDepth 32768

/-- Uncompressed native tuple fields. The wrap uses register or mixed address space,
    16-bit address/value limbs and a normal clock with the access offset in its low limb. -/
def token (physical : GKRAddress → F) (r : SpecialMemoryContributionRelation) : Option (MemoryToken proth120Modulus) := do
  let m := fun i => physical (.BaseLayerMemory i)
  let space : F := match r.address_space with
    | .Constant n => n.val | .IsRam i => m i | .IsRegister i => 1 - m i
  let (lo, hi) : F × F ← match r.address with
    | .ConstantU16 n => pure (n.val, 0) | .Constant n => pure (n.val, 0)
    | .U16Space i => pure (m i, 0)
    | .U32Space v => match v.values.toList with | [a,b] => pure (m a, m b) | _ => none
    | _ => none
  let .Normal t := r.timestamp | none
  let [tl, th] := t.values.toList | none
  let .U16Limbs v := r.value | none
  let [vl, vh] := v.values.toList | none
  return ⟨Nat.pair space.val (Nat.pair lo.val hi.val), (m tl + r.timestamp_offset.val, m th),
    Nat.pair (m vl).val (m vh).val⟩

/-- Cache indices are obtained from the product graph at the public read and write outputs. -/
inductive Factor where
  | wire (address : GKRAddress)
  | tuple (address : GKRAddress)
  | product (left right : Factor)
  | masked (execute input : Factor)

def lookup (env : List (GKRAddress × Factor)) (a : GKRAddress) : Factor :=
  (env.lookup a).getD (.wire a)

def gate (env : List (GKRAddress × Factor)) (g : GateArtifacts) : List (GKRAddress × Factor) :=
  let f := lookup env
  let out := match g.enforced_relation with
    | .CopyInBaseField a b | .CopyInExtensionField a b => some (b, f a)
    | .InitialGrandProductFromCaches ins o | .TrivialProduct ins o =>
      match ins.values.toList with | [l,r] => some (o, .product (f l) (f r)) | _ => none
    | .MaskIntoIdentityProduct x m o => some (o, .masked (f m) (f x))
    | _ => none
  out.toList ++ env

noncomputable def factors : List Factor :=
  let c := importedConstraintsLayoutSource
  let env := (layerGates c).foldl gate ((memoryCaches c).map fun a => (a, .tuple a))
  (ramOutputs c).map (lookup env)

def side (a b c d : Nat) : Factor :=
  .masked (.wire (.BaseLayerMemory 21))
    (.product (.product (.tuple (.Cached 0 a)) (.tuple (.Cached 0 b)))
      (.product (.tuple (.Cached 0 c)) (.tuple (.Cached 0 d))))

/-- The exact output order, pairing, copies and execute mask from the cached layers. -/
theorem output_wiring : factors = [side 0 1 4 5, side 2 3 6 7] := by kernel_rfl

/-- Read all actual RAM caches at the given physical assignment. -/
noncomputable def payloads (physical : GKRAddress → F) : List (GKRAddress × Option (MemoryToken proth120Modulus)) :=
  (layerCaches importedConstraintsLayoutSource).filterMap fun (a,r) => match r with
    | .MemoryTuple t => some (a, token physical t) | _ => none

private def pack (space low high tl th vl vh : F) : MemoryToken proth120Modulus :=
  ⟨Nat.pair space.val (Nat.pair low.val high.val), (tl, th), Nat.pair vl.val vh.val⟩

private def cacheRows {V A : Type} [NatCast V] (m : Nat → V)
    (row : V → V → Option V → Nat → Nat → Nat → Nat → Nat → A) : List A :=
  [row (Nat.cast 0) (m 4) none 0 1 2 3 0, row (m 9) (m 10) (some (m 11)) 5 6 7 8 0,
   row (Nat.cast 0) (m 4) none 24 25 2 3 0, row (m 9) (m 10) (some (m 11)) 24 25 7 8 1,
   row (m 16) (m 17) (some (m 18)) 12 13 14 15 0, row (Nat.cast 2) (Nat.cast 0) none 24 25 22 23 0,
   row (m 16) (m 17) (some (m 18)) 24 25 19 20 2, row (Nat.cast 2) (Nat.cast 0) none 28 29 26 27 0]

private def rows (m : Nat → F) : List (MemoryToken proth120Modulus) :=
  cacheRows m fun s a b t u x y k => pack s a (b.getD 0) (m t + k) (m u) (m x) (m y)

private theorem payload_fields (physical : GKRAddress → F) :
    payloads physical = (rows (fun i => physical (.BaseLayerMemory i))).zipIdx.map
      (fun (r,i) => (.Cached 0 i, some r)) := by kernel_rfl

/-- The memory challenge interpretation of the compiler's affine cache recipes. Any
    coefficient outside the RAM vocabulary is left arbitrary in the comparison. -/
def coefficient {E : Type} [CommRing E] (p : InitsTeardowns.Native.Parameters proth120Modulus E)
    (other : CacheCoefficient → E) : CacheCoefficient → E
  | .natural n => n | .memoryPower i => p.weights i | .memoryGamma => p.additive
  | c => other c

noncomputable def encodedCaches {E : Type} [CommRing E] (p : InitsTeardowns.Native.Parameters proth120Modulus E)
    (other : CacheCoefficient → E) (physical : GKRAddress → F) : List (GKRAddress × Option E) :=
  (layerCaches importedConstraintsLayoutSource).filterMap fun (a, r) => match r with
    | .MemoryTuple t => some (a, (tupleProgram t).map fun prog =>
        (prog.mapCoefficients (coefficient p other)).value (p.embed ∘ physical))
    | _ => none

private def weightedRows {E : Type} [CommRing E] (p : InitsTeardowns.Native.Parameters proth120Modulus E)
    (m : Nat → E) : List E :=
  cacheRows m fun s a b t u x y k =>
    let base := p.additive + s + p.weights 0 * a
    (b.map (fun h => base + p.weights 1 * h)).getD base +
      p.weights 2 * (m t + k) + p.weights 3 * m u + p.weights 4 * m x + p.weights 5 * m y

private theorem weighted_fields {E : Type} [CommRing E] (p : InitsTeardowns.Native.Parameters proth120Modulus E)
    (other : CacheCoefficient → E) (physical : GKRAddress → F) :
    encodedCaches p other physical = (weightedRows p (fun i => p.embed (physical (.BaseLayerMemory i)))).zipIdx.map
      (fun (r,i) => (.Cached 0 i, some r)) := by kernel_rfl

/-- The compiler's affine lowering of each physical tuple is exactly the native
    challenge encoding of its raw token, for every ring, embedding and six weights. -/
theorem cache_encodings {E : Type} [CommRing E] (p : InitsTeardowns.Native.Parameters proth120Modulus E)
    (other : CacheCoefficient → E) (physical : GKRAddress → F) :
    encodedCaches p other physical = (payloads physical).map (fun (a,r) => (a, r.map p.encode)) := by
  rw [weighted_fields, payload_fields]
  simp [weightedRows, rows, cacheRows, pack, InitsTeardowns.Native.Parameters.encode, List.zipIdx,
    Nat.unpair_pair, map_ofNat]

private def indices : Vector Nat 30 :=
  #v[34,35,36,37,5,40,41,42,43,28,38,39,46,47,48,49,29,44,45,50,51,4,0,1,2,3,30,31,32,33]

private theorem placed {physical : GKRAddress → F} {logical : Nat → F}
    (agree : ∀ kv ∈ placements, logical kv.1 = physical kv.2) (i : Fin 30) :
    physical (.BaseLayerMemory i) = logical indices[i] := by
  apply Eq.symm
  apply agree (indices[i], .BaseLayerMemory i)
  fin_cases i <;> decide +kernel

/-- At every accepted placement the three port reads/writes and the two PC tokens are
    exactly the physical RAM cache payloads used by the output DAG. -/
theorem cache_tokens {physical : GKRAddress → F} {logical : Nat → F}
    (agree : ∀ kv ∈ placements, logical kv.1 = physical kv.2) :
    let row : Row proth120Modulus Kind := ⟨.machine, logical⟩
    let select := fun (ids : List Nat) => ids.mapM fun i => ((payloads physical).lookup (.Cached 0 i)).join
    select [0,1,4,5] = some (row.reads ++ [stateToken row.start]) ∧
      select [2,3,6,7] = some (row.writes ++ [stateToken row.finish]) := by
  let bank (i : Nat) : F := if hi : i < 30 then logical (indices[(⟨i, hi⟩ : Fin 30)]) else 0
  let norm : GKRAddress → F := fun a => match a with
    | .BaseLayerMemory i => bank i
    | _ => 0
  have mem (i : Nat) (lt : i < 30) : physical (.BaseLayerMemory i) = norm (.BaseLayerMemory i) := by
    simpa [norm, bank, lt] using placed agree ⟨i, lt⟩
  have fixed : payloads physical = payloads norm := by
    rw [payload_fields, payload_fields]
    simp (disch := decide) only [rows, cacheRows, mem]
  dsimp only
  rw [fixed, payload_fields]
  constructor
  · simp only [rows, cacheRows, norm, bank, Nat.cast_zero, add_zero]
    kernel_rfl
  · have writes : (⟨.machine, logical⟩ : Row proth120Modulus Kind).writes =
        [pack 0 (logical 5) 0 (logical 2 + (0 : Nat)) (logical 3) (logical 36) (logical 37),
         pack (logical 28) (logical 38) (logical 39) (logical 2 + 1) (logical 3) (logical 42) (logical 43),
         pack (logical 29) (logical 44) (logical 45) (logical 2 + 2) (logical 3) (logical 50) (logical 51)] := by
      kernel_rfl
    rw [writes]
    simp only [rows, cacheRows, norm, bank, Nat.cast_zero, add_zero]
    rfl

/-- Evaluation of the two source output trees at an arbitrary memory challenge. -/
def Factor.value {E : Type} [CommRing E] (wire : GKRAddress → E) (cache : GKRAddress → Option E) : Factor → Option E
  | .wire a => some (wire a)
  | .tuple a => cache a
  | .product l r => return (← l.value wire cache) * (← r.value wire cache)
  | .masked m x => return PaddingBoundary.mask (← m.value wire cache) (← x.value wire cache)

private theorem side_value {E : Type} [CommRing E] (wire : GKRAddress → E)
    (leaf : GKRAddress → Option (MemoryToken proth120Modulus)) (encode : MemoryToken proth120Modulus → E)
    (a b c d : Nat) :
    (side a b c d).value wire (fun addr => (leaf addr).map encode) =
      ([a,b,c,d].mapM (fun i => leaf (.Cached 0 i))).map
        (fun ts => PaddingBoundary.mask (wire (.BaseLayerMemory 21)) (ts.map encode).prod) := by
  cases ha : leaf (.Cached 0 a) <;> cases hb : leaf (.Cached 0 b) <;>
    cases hc : leaf (.Cached 0 c) <;> cases hd : leaf (.Cached 0 d) <;>
    simp [side, Factor.value, ha, hb, hc, hd, mul_assoc]

private theorem lookup_map {E : Type} (f : MemoryToken proth120Modulus → E)
    (ps : List (GKRAddress × Option (MemoryToken proth120Modulus))) (a : GKRAddress) :
    ((ps.map (fun (k,v) => (k, v.map f))).lookup a).join = ((ps.lookup a).join).map f := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨key, val⟩
    simp only [List.map_cons, List.lookup]
    split <;> simp_all

/-- The public read and write output trees evaluate to exactly the two execute-masked
    products of the logical tokens, using the compiler's lowered physical cache encodings. -/
theorem output_products {E : Type} [CommRing E] (p : InitsTeardowns.Native.Parameters proth120Modulus E)
    (other : CacheCoefficient → E) {physical : GKRAddress → F} {logical : Nat → F}
    (agree : ∀ kv ∈ placements, logical kv.1 = physical kv.2) :
    let row : Row proth120Modulus Kind := ⟨.machine, logical⟩
    factors.mapM (Factor.value (p.embed ∘ physical) (fun a => ((encodedCaches p other physical).lookup a).join)) =
      some ([row.reads ++ [stateToken row.start], row.writes ++ [stateToken row.finish]].map fun ts =>
        PaddingBoundary.mask (p.embed (logical row.columns.execute)) (ts.map p.encode).prod) := by
  dsimp only
  rw [output_wiring, cache_encodings]
  simp only [lookup_map, List.mapM_cons, List.mapM_nil, side_value, (cache_tokens agree).1, (cache_tokens agree).2]
  have execute : physical (.BaseLayerMemory 21) = logical (⟨.machine, logical⟩ : Row proth120Modulus Kind).columns.execute := by
    exact placed agree (21 : Fin 30)
  simp [execute]

end Airbender.UnifiedReduced.Proth120.NativeRAM
