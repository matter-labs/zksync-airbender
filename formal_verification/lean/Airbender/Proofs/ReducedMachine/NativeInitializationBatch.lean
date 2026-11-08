import Airbender.Review.Circuits.ReducedMachine.InitializationBatch
import Airbender.Proofs.ReducedMachine.NativeInitializationWindow
import Airbender.Proofs.ReducedMachine.NativeMainArguments
import Airbender.Proofs.ReducedMachine.NativeMainStateHistory

namespace Airbender.NativeInitializationBatchProofs
open Airbender.NativeInitializationBatch
open Airbender.NativeInitializationOrdering (PaddingRecord)
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem scalar_main {R : Type} [Field R] (proof : Proof R) : proof.scalar.initialization.main = proof.main.memory := rfl

theorem same_list {R : Type} [Field R] (proofs : List (Proof R)) :
    mainProofs proofs = (mainArguments proofs).map (fun proof => proof.memory) := by
  simp only [mainArguments,mainProofs,List.map_map,Function.comp_def]

/-- ENTIRE abstract finite-list calculation before native instantiation. Only
    unused arithmetic/Prop projections outside list bounds use 0/True. No proof
    object, accepted row/history or token ledger is fabricated out of bounds. -/
theorem list_cross {A : Type} (items : List A) {rows : Nat} (value : A → Nat → Nat) (padding : A → Nat → Prop)
    (positive : 0 < rows)
    (adjacent : ∀ c (bound : c + 1 < items.length), ∀ i < rows, ∀ j < rows,
      value (items[c]'(by omega)) i ≤ value (items[c + 1]'bound) j ∧
      (¬ padding (items[c]'(by omega)) i → value (items[c]'(by omega)) i < value (items[c + 1]'bound) j)) :
    ∀ c d (less : c < d) (bound : d < items.length), ∀ i < rows, ∀ j < rows,
      value (items[c]'(by omega)) i ≤ value (items[d]'bound) j ∧
      (¬ padding (items[c]'(by omega)) i → value (items[c]'(by omega)) i < value (items[d]'bound) j) := by
  let values c i := if h : c < items.length then value (items[c]'h) i else 0
  let padded c i := if h : c < items.length then padding (items[c]'h) i else True
  have links : ∀ c, c + 1 < items.length → ∀ i < rows, ∀ j < rows,
      values c i ≤ values (c + 1) j ∧ (¬ padded c i → values c i < values (c + 1) j) := by
    intro c bound i ib j jb
    simpa only [values,padded,dif_pos bound,dif_pos (show c < items.length by omega)] using adjacent c bound i ib j jb
  have result := NativeInitializationWindowProofs.cross_sequence positive links
  intro c d less bound i ib j jb
  simpa only [values,padded,dif_pos bound,dif_pos (show c < items.length by omega)] using result c d less bound i ib j jb

/-- Generic full-domain sampling membership, before concrete native rows. -/
theorem batch_token_member {A B C D : Type} (items : List A) (domain : List B) (observe : A → B → C)
    (tokens : C → List D) {a : A} {i : B} {token : D}
    (member : a ∈ items) (index : i ∈ domain) (rowMember : token ∈ tokens (observe a i)) :
    token ∈ (items.flatMap fun a => domain.map (observe a)).flatMap tokens := by
  exact List.mem_flatMap.mpr ⟨observe a i,List.mem_flatMap.mpr ⟨a,member,List.mem_map.mpr ⟨i,index,rfl⟩⟩,rowMember⟩

private theorem middle_member {A : Type} (left middle right : List A) {token : A} (member : token ∈ middle) :
    token ∈ left ++ middle ++ right := by
  simp only [List.mem_append]
  tauto

theorem token_in_full {Setup R : Type} [Field R] (proofs : List (Proof R)) (batch : WorkerBatch Setup R)
    (inputs : PublicBoundary) {proof : Proof R} (member : proof ∈ proofs)
    (i : Nat) (ordinary : i < scalar16Layout.traceLength-1) (write : Bool) :
    Airbender.NativeTokenLedger.Token.memory (initializationToken proof i write) ∈
      Airbender.NativeTokenLedger.fullTokens (mainProofs proofs) batch inputs write := by
  have object : proof.main.memory ∈ mainProofs proofs := List.mem_map.mpr ⟨proof,member,rfl⟩
  have index : i ∈ List.range (callerAuxiliaryLayout.traceLength-1) := by
    apply List.mem_range.mpr
    have domain : scalar16Layout.traceLength = callerAuxiliaryLayout.traceLength := by decide +kernel
    omega
  have rowMember : Airbender.NativeTokenLedger.Token.memory (initializationToken proof i write) ∈
      Airbender.NativeTokenLedger.rowTokens (proof.main.memory.rows i) write := List.mem_cons_self
  have occurrence := batch_token_member (mainProofs proofs) (List.range (callerAuxiliaryLayout.traceLength-1))
    (fun proof row => proof.rows row) (fun w => Airbender.NativeTokenLedger.rowTokens w write) object index rowMember
  exact middle_member _ _ _ occurrence

theorem initialization_effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Accepted embed memory ch pc gamma config proofs batch inputs inverse) : InitializationEffects proofs := by
  have order := list_cross (rows := scalar16Layout.traceLength-1) proofs
    (fun proof i => Airbender.NativeInitializationSorted.addressValue (proof.main.memory.rows i))
    (fun proof i => PaddingRecord (proof.main.memory.rows i)) (by decide +kernel)
    (fun c bound => NativeInitializationWindowProofs.adjacent_rows embed memory pc gamma
      (previous := (proofs[c]'(by omega)).chunk) (current := (proofs[c + 1]'bound).chunk)
      (accepted.initialization _ (by simp))
      (accepted.initialization _ (by simp)) (accepted.windows c bound))
  refine ⟨?_,order,?_⟩
  · intro proof member i bound
    exact NativeScalar16LookupProofs.initialization_bounds (accepted.initialization proof member).scalar.lookups i bound
  · intro c d i j cb db ib jb ip jp same
    have raw := NativeInitializationOrderingProofs.token_address_binding same
    have value := congrArg (fun v : Vector F 2 => v[0].val+65536*v[1].val) raw
    change Airbender.NativeInitializationSorted.addressValue ((proofs[c]'cb).main.memory.rows i) =
      Airbender.NativeInitializationSorted.addressValue ((proofs[d]'db).main.memory.rows j) at value
    rcases lt_trichotomy c d with less | equal | greater
    · have strict := (order c d less db i ib j jb).2 ip; omega
    · subst d
      exact ⟨rfl,NativeInitializationSortedProofs.token_unique embed memory pc gamma
        (accepted.initialization _ (by simp)).scalar i j ib jb ip jp same⟩
    · have strict := (order d c greater cb j jb i ib).2 jp; omega

theorem joint_effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    Airbender.ReducedMachine.NativeMainArguments.Effects embed memory pc (mainArguments proofs) batch inputs ∧
      Airbender.NativeMainStateHistory.Effects (mainProofs proofs) inputs ∧ InitializationEffects proofs := by
  have components : ∀ proof ∈ mainProofs proofs, Airbender.ReducedMachine.NativeMainAuxiliary.Accepted embed memory pc proof := by
    intro proof member
    obtain ⟨origin,present,rfl⟩ := List.mem_map.mp member
    exact accepted.arguments.mainMemory origin.main (List.mem_map.mpr ⟨origin,present,rfl⟩)
  exact ⟨Airbender.ReducedMachine.NativeMainArgumentProofs.joint_effects embed memory ch pc config accepted.arguments,
    NativeMainStateHistoryProofs.history embed memory pc components accepted.matching,
    initialization_effects embed memory ch pc gamma config accepted⟩

end Airbender.NativeInitializationBatchProofs
