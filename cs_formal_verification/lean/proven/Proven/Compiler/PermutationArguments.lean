module
public import Human.Compiler.PermutationTargets
public import Proven.Final.Compiler.CertificateMemory
public import Proven.Compiler.MemoryCompositionNative
public import Proven.Trace.PaddingBoundary

@[expose] public section
set_option warningAsError true

/-! The permutation arguments drop to the native certificate premises, and the masked permutation of a padded layout
    is the permutation of its active rows. -/

namespace Airbender.Compiler.NativeMemory
open Trace Trace.Machine PaddingBoundary PaddingBoundary.Proofs

/-- An occurrence count of a present value is its count after erasure. -/
theorem count_some {α : Type} [DecidableEq α] (values : List (Option α)) (value : α) :
    values.count (some value) = (values.filterMap fun option => option).count value := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | none => simp [ih]
    | some other => by_cases same : other = value <;> simp [ih, same]

/-- Two option lists with equal erasures and equal identity counts are permutations. -/
theorem perm_of_erased {α : Type} [DecidableEq α] {first second : List (Option α)}
    (erased : (first.filterMap fun option => option).Perm (second.filterMap fun option => option))
    (nones : first.count none = second.count none) : first.Perm second := by
  rw [List.perm_iff_count]
  intro value
  cases value with
  | none => exact nones
  | some value => rw [count_some, count_some]; exact erased.count_eq value

/-- Masked lists of equal row lengths have equal identity counts. -/
theorem contributions_nones {ρ α : Type} [DecidableEq α] (rows : List ρ) (execute : ρ → ZMod babyBearModulus)
    (first second : ρ → List α) (lengths : ∀ row, (first row).length = (second row).length) :
    (contributions rows execute first).count none = (contributions rows execute second).count none := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    change ((first row).map (contribution (execute row)) ++ contributions rest execute first).count none =
      ((second row).map (contribution (execute row)) ++ contributions rest execute second).count none
    rw [List.count_append, List.count_append, ih]
    congr 1
    by_cases active : execute row = 1
    · have zero (values : List α) : (values.map (contribution (execute row))).count none = 0 :=
        List.count_eq_zero.mpr fun present => by
          obtain ⟨value, _, absent⟩ := List.mem_map.mp present
          simp [contribution, active] at absent
      rw [zero, zero]
    · have full (values : List α) : (values.map (contribution (execute row))).count none = values.length := by
        rw [← List.length_map (f := contribution (execute row)) (as := values)]
        refine List.count_eq_length.mpr fun value present => ?_
        obtain ⟨other, _, rfl⟩ := List.mem_map.mp present
        simp [contribution, active]
      rw [full, full, lengths row]

/-- The masked permutation of a padded layout is the permutation of its active rows. -/
theorem padded_active {Kind : Type} [CircuitLayout Kind] (trace : Data babyBearModulus Kind)
    (workers : WorkerPools babyBearModulus) :
    PaddedRamPermutation trace workers ↔ RamPermutation (active trace) (activeWorkers workers) := by
  have erase (values : List (MemoryToken babyBearModulus)) :
      (values.map some).filterMap (fun option => option) = values := by
    simp [List.filterMap_map]
  constructor
  · intro production
    have matched := production.filterMap (fun option => option)
    simpa only [List.filterMap_append, List.filterMap_cons, erase, erase_contributions, RamPermutation, workerWrites,
      workerReads, active, activeWorkers, List.cons_append, List.append_assoc] using matched
  · intro production
    apply perm_of_erased
    · simpa only [List.filterMap_append, List.filterMap_cons, erase, erase_contributions, RamPermutation, workerWrites,
        workerReads, active, activeWorkers, List.cons_append, List.append_assoc] using production
    · have cpu := contributions_nones trace.rows (fun row => row.assignment row.columns.execute) cpuWrites cpuReads
        fun row => by simp [cpuWrites, cpuReads, Row.writes, Row.reads]
      have standard := contributions_nones workers.standard.rows (fun row => row.assignment row.columns.execute)
        standardWrites standardReads fun row => by simp [standardWrites, standardReads]
      have split := contributions_nones workers.split.rows (fun row => row.assignment row.columns.execute)
        splitWrites splitReads fun row => by simp [splitWrites, splitReads]
      have seeds (values : List (MemoryToken babyBearModulus)) : (values.map some).count none = 0 := by
        simp [List.count_eq_zero]
      simp only [List.count_cons, List.count_append, seeds, cpu, standard, split]
      simp

end Airbender.Compiler.NativeMemory

namespace Airbender.Compiler
open Trace

/-- A list related to its own image under a map. -/
theorem forall₂_map {α β : Type} {relation : α → β → Prop} (values : List α) (image : α → β)
    (each : ∀ value, relation value (image value)) : List.Forall₂ relation values (values.map image) := by
  induction values with
  | nil => exact .nil
  | cons head tail ih => exact .cons (each head) ih

/-- The canonical values of cached CPU certificates are extension values under any challenges. -/
theorem program_extensions {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    {tables : ProgramLookupRows} (certificates : List (ProgramRowCertificate tables)) :
    ProgramExtensions challenges certificates (certificates.map (programCanonical challenges)) :=
  forall₂_map certificates _ (programCanonical_holds challenges)

/-- The canonical values of cached unified certificates are extension values under any challenges. -/
theorem unified_extensions {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    {tables : ProgramLookupRows} (certificates : List (UnifiedRowCertificate tables)) :
    UnifiedExtensions challenges certificates (certificates.map (unifiedCanonical challenges)) :=
  forall₂_map certificates _ (unifiedCanonical_holds challenges)

/-- Native worker certificates have their program values as extension values under any challenges. -/
theorem worker_rows_extended {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    {workers : Machine.WorkerPools babyBearModulus} (certified : WorkerRowsCertified workers) :
    WorkerRowsExtended challenges workers := by
  obtain ⟨certificates, standard, split⟩ := certified
  exact ⟨certificates, certificates.map fun cert => workerProgramValues challenges cert.toWorkerRowCertificate,
    forall₂_map certificates _ fun cert => workerProgramValues_holds challenges cert.toWorkerRowCertificate,
    standard, split⟩

/-- Padded native worker certificates have their program values as extension values under any challenges. -/
theorem padded_rows_extended {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    {workers : Machine.WorkerPools babyBearModulus} (certified : PaddedWorkerRowsCertified workers) :
    PaddedWorkerRowsExtended challenges workers := by
  obtain ⟨certificates, flags, standard, split⟩ := certified
  exact ⟨certificates, certificates.map (workerProgramValues challenges),
    forall₂_map certificates _ (workerProgramValues_holds challenges), flags, standard, split⟩

/-- Extended worker certificates are native worker certificates. -/
theorem worker_rows_certified {E : Type} [CommRing E] {challenges : NativeMemory.Challenges E}
    {workers : Machine.WorkerPools babyBearModulus} (extended : WorkerRowsExtended challenges workers) :
    WorkerRowsCertified workers := by
  obtain ⟨certificates, _, _, standard, split⟩ := extended
  exact ⟨certificates, standard, split⟩

/-- Extended padded worker certificates are padded native worker certificates. -/
theorem padded_rows_certified {E : Type} [CommRing E] {challenges : NativeMemory.Challenges E}
    {workers : Machine.WorkerPools babyBearModulus} (extended : PaddedWorkerRowsExtended challenges workers) :
    PaddedWorkerRowsCertified workers := by
  obtain ⟨certificates, _, _, flags, standard, split⟩ := extended
  exact ⟨certificates, flags, standard, split⟩

end Airbender.Compiler
