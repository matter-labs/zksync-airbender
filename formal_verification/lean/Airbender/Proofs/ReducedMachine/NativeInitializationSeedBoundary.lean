import Airbender.Review.Circuits.ReducedMachine.InitializationSeedBoundary
import Airbender.Proofs.ReducedMachine.NativeInitializationSeedDomain
import Airbender.Proofs.Trace.Families.ReducedMachine.ShadowImage

namespace Airbender.NativeInitializationSeedBoundaryProofs
open Airbender.NativeInitializationSeedBoundary
open Airbender.NativeInitializationBatch (Proof mainProofs)
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeShadow (architecturalAddress shadowTokens)
open Airbender.NativeTokenLedger (Token memoryProjection publicTokens portTokens workerRowTokens)
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem initial_register (index : Fin 32) :
    Airbender.NativeMemoryTokens.encodeKey (registerInitialKey index) =
      (Trace.Cell.register (BitVec.ofNat 5 index.val)).initialToken 0 := by
  have bounded : index.val < mersenne31Modulus := lt_trans index.isLt (by decide)
  simp [Airbender.NativeMemoryTokens.encodeKey,Airbender.NativeMemoryTokens.encodeAddress,
    registerInitialKey,Trace.Cell.initialToken,Trace.Cell.addressCode,Arithmetic.Word.ofBitVec,
    Arithmetic.limbBase,ZMod.val_natCast_of_lt bounded,BitVec.toNat_ofNat]

theorem register_encoding : initialRegisters = registerCells.map (fun c => c.initialToken (p := mersenne31Modulus) 0) := by
  simp only [initialRegisters,registerCells,List.map_map,Function.comp_def,initial_register]

theorem register_domain : registerCells.Nodup := by
  apply (List.nodup_finRange 32).map
  intro i j same
  have bits := congrArg BitVec.toNat (Trace.Cell.register.inj same)
  apply Fin.ext
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using bits

/-- Generic type separation, not a Boolean/range premise on native accesses. -/
theorem domain_union {R : Type} [Field R] {proofs : List (Proof R)}
    (ram : Airbender.NativeInitializationSeedDomain.Effects proofs) : (cells proofs).Nodup := by
  rw [cells,List.nodup_append]
  refine ⟨register_domain,ram.domain,?_⟩
  intro reg rm memory mm same
  obtain ⟨index,_,rfl⟩ := List.mem_map.mp rm
  obtain ⟨token,_,rfl⟩ := List.mem_map.mp mm
  exact Trace.Cell.noConfusion same

theorem shadow_bounds {domain : List Trace.Cell} {seed : Airbender.ReducedMachine.NativeShadow.ShadowSeed}
    (member : seed ∈ shadowSeeds domain) : seed.1.toNat < 4194304 ∧ seed.2 = 0 := by
  obtain ⟨c,_,found⟩ := List.mem_filterMap.mp member
  cases c with
  | register index => simp [shadowSeed] at found
  | ram address =>
    by_cases small : address.toNat < 4194304
    · simp only [shadowSeed,small,ite_true,Option.some.injEq] at found
      subst seed
      exact ⟨small,rfl⟩
    · simp [shadowSeed,small] at found

private theorem filter_rows {A : Type} (rows : List A) (keep : A → Bool) :
    (rows.flatMap fun row => if keep row then [row] else []) = rows.filter keep := by
  induction rows with
  | nil => rfl
  | cons row rows ih => cases found : keep row <;> simp [found,ih]

private theorem shadow_rows (domain : List Trace.Cell) :
    (domain.flatMap fun c => ((shadowSeed c).toList.map fun seed => Trace.Cell.ram seed.1)) =
      (shadowSeeds domain).map (fun seed => Trace.Cell.ram seed.1) := by
  induction domain with
  | nil => rfl
  | cons c domain ih => cases found : shadowSeed c <;> simp [shadowSeeds,found,ih]

theorem cell_partition (domain : List Trace.Cell) :
    domain.Perm (architecturalCells domain ++ (shadowSeeds domain).map (fun seed => Trace.Cell.ram seed.1)) := by
  have partition := Airbender.NativeInitializationLedgerProofs.split_rows domain (fun c => [c])
    (fun c => if architecturalAddress c.addressCode then [c] else [])
    (fun c => (shadowSeed c).toList.map fun seed => Trace.Cell.ram seed.1) ?_
  · simpa only [List.flatMap_singleton',filter_rows,shadow_rows,architecturalCells] using partition
  · intro c _
    cases c with
    | register index => simp [Airbender.ReducedMachine.NativeShadowProofs.architectural_register,shadowSeed]
    | ram address =>
      by_cases small : address.toNat < 4194304
      · simp [Airbender.ReducedMachine.NativeShadowProofs.architectural_ram,shadowSeed,small,Nat.not_le.mpr small]
      · simp [Airbender.ReducedMachine.NativeShadowProofs.architectural_ram,shadowSeed,small,Nat.le_of_not_gt small]

theorem boundary {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) : Effects proofs := by
  have ram := NativeInitializationSeedDomainProofs.seed_domains embed memory ch pc gamma config accepted
  have domain := domain_union ram
  have encoding : initialTokens proofs = (cells proofs).map (fun c => c.initialToken (p := mersenne31Modulus) 0) := by
    rw [initialTokens,cells,List.map_append,register_encoding,ram.encoding]
  have addresses : ((initialTokens proofs).map Trace.MemoryToken.address).Nodup := by
    rw [encoding,List.map_map]
    exact domain.map Trace.Proofs.cell_address_injective
  have partition := cell_partition (cells proofs)
  refine ⟨domain,encoding,addresses,?_,?_,partition.nodup_iff.mp domain,?_,fun _ member => shadow_bounds member⟩
  · intro token member
    rw [encoding] at member
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp member
    rfl
  · rw [encoding]
    have mapped := partition.map (fun c => c.initialToken (p := mersenne31Modulus) 0)
    rw [List.map_append,List.map_map] at mapped
    convert mapped using 1
    congr 1
    apply List.map_congr_left
    intro seed member
    rw [(shadow_bounds member).2]
    rfl
  · intro c member
    exact (List.mem_filter.mp member).2

private theorem memory_tags (tokens : List (Trace.MemoryToken mersenne31Modulus)) :
    (tokens.map Token.memory).filterMap memoryProjection = tokens := by
  simp [List.filterMap_map,memoryProjection]

theorem public_projection (inputs : PublicBoundary) (write : Bool) :
    (publicTokens inputs write).filterMap memoryProjection = if write then initialRegisters else finalRegisters inputs := by
  cases write <;> simp [publicTokens,initialRegisters,finalRegisters,List.filterMap_append,
    memoryProjection,List.filterMap_map]

theorem port_projection (w : Nat → F) (write : Bool) :
    (portTokens w write).filterMap memoryProjection = Airbender.NativeMemoryTokens.mainTokens w write := by
  simp [portTokens,List.filterMap_append,memoryProjection]

/-- Generic full-domain observation projection before native pool instantiation. -/
theorem main_projection (rows : List (Nat → F)) (write : Bool) :
    ((rows.flatMap fun w => if w Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute = 1
      then portTokens w write else []).filterMap memoryProjection) =
    (Airbender.NativeMainStateHistory.selectAssignments rows).flatMap fun w => Airbender.NativeMemoryTokens.mainTokens w write := by
  induction rows with
  | nil => rfl
  | cons w rows ih =>
    by_cases active : w Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute = 1
    all_goals simp [Airbender.NativeMainStateHistory.selectAssignments,active,List.filterMap_append,port_projection,ih]

theorem access_projection {Setup R : Type} [Field R] (proofs : List (Proof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) (write : Bool) :
    (Airbender.NativeInitializationLedger.accessTokens (mainProofs proofs) batch inputs write).filterMap memoryProjection =
      (if write then initialRegisters else finalRegisters inputs) ++ accessTokens proofs batch write := by
  unfold Airbender.NativeInitializationLedger.accessTokens
  rw [List.filterMap_append,List.filterMap_append,public_projection,main_projection]
  simp only [List.filterMap_flatMap,workerRowTokens,memory_tags,accessTokens,List.append_assoc]

private theorem reorder {A : Type} (a b c : List A) : (a ++ (b ++ c)).Perm ((b ++ a) ++ c) := by
  simpa only [List.append_assoc] using (show (a ++ b).Perm (b ++ a) from List.perm_append_comm).append_right c

/-- ENTIRE projection/cancellation-free permutation algebra on ABSTRACT lists
    before concrete native observations. Projection identities are structural. -/
theorem projection_balance {A B : Type} (tag : B → A) (project : A → Option B)
    (seedsLeft seedsRight registersLeft registersRight stepsLeft stepsRight : List B)
    (accessLeft accessRight : List A)
    (tags : ∀ values : List B, (values.map tag).filterMap project = values)
    (left : accessLeft.filterMap project = registersLeft ++ stepsLeft)
    (right : accessRight.filterMap project = registersRight ++ stepsRight)
    (matching : (seedsLeft.map tag ++ accessLeft).Perm (seedsRight.map tag ++ accessRight)) :
    ((registersLeft ++ seedsLeft) ++ stepsLeft).Perm ((registersRight ++ seedsRight) ++ stepsRight) := by
  have projected := matching.filterMap project
  rw [List.filterMap_append,List.filterMap_append,tags,tags,left,right] at projected
  exact (reorder seedsLeft registersLeft stepsLeft).symm.trans
    (projected.trans (reorder seedsRight registersRight stepsRight))

theorem memory_matching {Setup R : Type} [Field R] {proofs : List (Proof R)}
    {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (matching : Airbender.NativeTokenLedger.LogicalMatching (mainProofs proofs) batch inputs) :
    (initialTokens proofs ++ accessTokens proofs batch true).Perm
      (terminalTokens proofs inputs ++ accessTokens proofs batch false) :=
  projection_balance Token.memory memoryProjection
    (Airbender.NativeInitializationSeedDomain.tokens proofs true) (Airbender.NativeInitializationSeedDomain.tokens proofs false)
    initialRegisters (finalRegisters inputs) (accessTokens proofs batch true) (accessTokens proofs batch false)
    (Airbender.NativeInitializationLedger.accessTokens (mainProofs proofs) batch inputs true)
    (Airbender.NativeInitializationLedger.accessTokens (mainProofs proofs) batch inputs false)
    memory_tags (access_projection proofs batch inputs true) (access_projection proofs batch inputs false)
    ((NativeInitializationSeedDomainProofs.matching proofs batch inputs).mp matching)

end Airbender.NativeInitializationSeedBoundaryProofs
