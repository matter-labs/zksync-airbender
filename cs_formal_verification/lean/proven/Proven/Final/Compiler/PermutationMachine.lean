module
public import Proven.Compiler.PermutationArguments
public import Proven.Final.Compiler.MemoryComposition
public import Proven.Final.Compiler.PaddedNativeMachine

@[expose] public section
set_option warningAsError true

namespace Airbender.Trace.Machine.Native
open Airbender.Compiler NativeMemory PaddingBoundary Trace.Machine.Proofs

/-- Cached native certificates and the single RAM permutation imply the full unsigned whole-machine run. -/
theorem unrolled_full_from_native_permutation : UnrolledFullFromNativePermutation := by
  intro trace workers initial cells program inits tables boot noSpecial stream bound covers E _ challenges
    certificates values arguments
  obtain ⟨states, requests, memory⟩ := unrolled_memory_composition .unrolledFullUnsigned trace workers initial cells
    program _ inits tables certificates (by decide) boot bound covers arguments.rows arguments.production
  exact unrolled_full_from_native trace workers initial cells program inits tables boot noSpecial stream bound covers
    certificates ⟨worker_rows_certified arguments.workerRows, arguments.rows, states, requests, memory⟩

/-- Cached native certificates and the single RAM permutation imply the reduced whole-machine run. -/
theorem unrolled_reduced_from_native_permutation : UnrolledReducedFromNativePermutation := by
  intro trace workers initial cells program inits tables boot stream bound covers E _ challenges certificates values
    arguments
  obtain ⟨states, requests, memory⟩ := unrolled_memory_composition .unrolledReduced trace workers initial cells
    program _ inits tables certificates (by decide) boot bound covers arguments.rows arguments.production
  exact unrolled_reduced_from_native trace workers initial cells program inits tables boot stream bound covers
    certificates ⟨worker_rows_certified arguments.workerRows, arguments.rows, states, requests, memory⟩

/-- Cached native certificates and the single RAM permutation imply the unified whole-machine run. -/
theorem unified_from_native_permutation : UnifiedFromNativePermutation := by
  intro trace workers initial cells program inits tables boot noSpecial stream bound E _ challenges certificates values
    arguments
  obtain ⟨states, requests, memory⟩ := unified_memory_composition trace workers initial cells program _ inits tables
    certificates boot bound arguments.rows arguments.production
  exact unified_from_native trace workers initial cells program inits tables boot noSpecial stream bound certificates
    ⟨worker_rows_certified arguments.workerRows, arguments.rows, states, requests, memory⟩

/-- The active rows of a padded layout with the masked RAM permutation execute the full unsigned run. -/
theorem padded_unrolled_full_from_native_permutation : PaddedUnrolledFullFromNativePermutation := by
  intro trace workers initial cells program inits tables boot noSpecial stream bound covers E _ challenges
    certificates values arguments
  have rows : (active trace).rows = (activeCertificates certificates).map (·.row) := by
    simp only [active, arguments.rows]
    exact (activeCertificates_rows certificates).symm
  obtain ⟨states, requests, memory⟩ := unrolled_memory_composition .unrolledFullUnsigned (active trace)
    (activeWorkers workers) initial cells program _ inits tables (activeCertificates certificates) (by decide) boot
    bound covers rows ((padded_active trace workers).mp arguments.production)
  exact unrolled_full_from_native (active trace) (activeWorkers workers) initial cells program inits tables boot
    noSpecial stream bound covers (activeCertificates certificates)
    ⟨padded_worker_rows (padded_rows_certified arguments.workerRows), rows, states, requests, memory⟩

/-- The active rows of a padded layout with the masked RAM permutation execute the reduced run. -/
theorem padded_unrolled_reduced_from_native_permutation : PaddedUnrolledReducedFromNativePermutation := by
  intro trace workers initial cells program inits tables boot stream bound covers E _ challenges certificates values
    arguments
  have rows : (active trace).rows = (activeCertificates certificates).map (·.row) := by
    simp only [active, arguments.rows]
    exact (activeCertificates_rows certificates).symm
  obtain ⟨states, requests, memory⟩ := unrolled_memory_composition .unrolledReduced (active trace)
    (activeWorkers workers) initial cells program _ inits tables (activeCertificates certificates) (by decide) boot
    bound covers rows ((padded_active trace workers).mp arguments.production)
  exact unrolled_reduced_from_native (active trace) (activeWorkers workers) initial cells program inits tables boot
    stream bound covers (activeCertificates certificates)
    ⟨padded_worker_rows (padded_rows_certified arguments.workerRows), rows, states, requests, memory⟩

/-- The active rows of a padded layout with the masked RAM permutation execute the unified run. -/
theorem padded_unified_from_native_permutation : PaddedUnifiedFromNativePermutation := by
  intro trace workers initial cells program inits tables boot noSpecial stream bound E _ challenges certificates values
    arguments
  have rows : (active trace).rows = (activeUnifiedCertificates certificates).map (·.row) := by
    simp only [active, arguments.rows]
    exact (activeUnifiedCertificates_rows certificates).symm
  obtain ⟨states, requests, memory⟩ := unified_memory_composition (active trace) (activeWorkers workers) initial cells
    program _ inits tables (activeUnifiedCertificates certificates) boot bound rows
    ((padded_active trace workers).mp arguments.production)
  exact unified_from_native (active trace) (activeWorkers workers) initial cells program inits tables boot noSpecial
    stream bound (activeUnifiedCertificates certificates)
    ⟨padded_worker_rows (padded_rows_certified arguments.workerRows), rows, states, requests, memory⟩

/-- One submitted ADD row meets the full unsigned premises with its extension values and the single RAM
    permutation. -/
theorem unrolled_full_from_native_permutation_satisfiable : UnrolledFullFromNativePermutationSatisfiableClaim := by
  obtain ⟨trace, workers, initial, cells, program, inits, tables, boot, noSpecial, stream, bound, covers, certificates,
    arguments, length, standard, split⟩ := unrolled_full_from_native_satisfiable
  exact ⟨trace, workers, initial, cells, program, inits, tables, boot, noSpecial, stream, bound, covers,
    sampleChallenges, certificates, _, ⟨worker_rows_extended sampleChallenges arguments.workerRows, arguments.rows,
      program_extensions sampleChallenges _, unrolled_native_production (by decide) boot bound covers arguments⟩,
    length, standard, split⟩

/-- One submitted ADD row meets the reduced premises with its extension values and the single RAM permutation. -/
theorem unrolled_reduced_from_native_permutation_satisfiable :
    UnrolledReducedFromNativePermutationSatisfiableClaim := by
  obtain ⟨trace, workers, initial, cells, program, inits, tables, boot, stream, bound, covers, certificates,
    arguments, length, standard, split⟩ := unrolled_reduced_from_native_satisfiable
  exact ⟨trace, workers, initial, cells, program, inits, tables, boot, stream, bound, covers,
    sampleChallenges, certificates, _, ⟨worker_rows_extended sampleChallenges arguments.workerRows, arguments.rows,
      program_extensions sampleChallenges _, unrolled_native_production (by decide) boot bound covers arguments⟩,
    length, standard, split⟩

/-- A loop with sixteen CPU rows and two bigint calls meets the unified premises with their extension values and
    the single RAM permutation. -/
theorem unified_from_native_permutation_satisfiable : UnifiedFromNativePermutationSatisfiableClaim := by
  obtain ⟨trace, workers, initial, cells, program, inits, tables, boot, noSpecial, stream, bound, certificates,
    arguments, length, standard, split⟩ := unified_from_native_satisfiable
  exact ⟨trace, workers, initial, cells, program, inits, tables, boot, noSpecial, stream, bound,
    sampleChallenges, certificates, _, ⟨worker_rows_extended sampleChallenges arguments.workerRows, arguments.rows,
      unified_extensions sampleChallenges _, unified_native_production boot bound arguments⟩,
    length, standard, split⟩

/-- One active ADD row and one padding row meet the padded full unsigned premises with their extension values and
    the masked permutation. -/
theorem padded_unrolled_full_from_native_permutation_satisfiable :
    PaddedUnrolledFullFromNativePermutationSatisfiableClaim := by
  obtain ⟨trace, workers, initial, cells, program, inits, tables, boot, noSpecial, stream, bound, covers, certificates,
    arguments, activeRows, padding⟩ := padded_unrolled_full_from_native_satisfiable
  have production := unrolled_native_production (by decide) boot bound covers (padded_unrolled_arguments arguments)
  obtain ⟨workerRows, rows, flags, _, _, _⟩ := arguments
  exact ⟨trace, workers, initial, cells, program, inits, tables, boot, noSpecial, stream, bound, covers,
    sampleChallenges, certificates, _, ⟨padded_rows_extended sampleChallenges workerRows, rows,
      program_extensions sampleChallenges certificates, flags, (padded_active trace workers).mpr production⟩,
    activeRows, padding⟩

/-- One active ADD row and one padding row meet the padded reduced premises with their extension values and the
    masked permutation. -/
theorem padded_unrolled_reduced_from_native_permutation_satisfiable :
    PaddedUnrolledReducedFromNativePermutationSatisfiableClaim := by
  obtain ⟨trace, workers, initial, cells, program, inits, tables, boot, stream, bound, covers, certificates,
    arguments, activeRows, padding⟩ := padded_unrolled_reduced_from_native_satisfiable
  have production := unrolled_native_production (by decide) boot bound covers (padded_unrolled_arguments arguments)
  obtain ⟨workerRows, rows, flags, _, _, _⟩ := arguments
  exact ⟨trace, workers, initial, cells, program, inits, tables, boot, stream, bound, covers,
    sampleChallenges, certificates, _, ⟨padded_rows_extended sampleChallenges workerRows, rows,
      program_extensions sampleChallenges certificates, flags, (padded_active trace workers).mpr production⟩,
    activeRows, padding⟩

/-- One active unified row and one padding row meet the padded unified premises with their extension values and the
    masked permutation. -/
theorem padded_unified_from_native_permutation_satisfiable : PaddedUnifiedFromNativePermutationSatisfiableClaim := by
  obtain ⟨trace, workers, initial, cells, program, inits, tables, boot, noSpecial, stream, bound, certificates,
    arguments, activeRows, padding⟩ := padded_unified_from_native_satisfiable
  have production := unified_native_production boot bound (padded_unified_arguments arguments)
  obtain ⟨workerRows, rows, flags, _, _, _⟩ := arguments
  exact ⟨trace, workers, initial, cells, program, inits, tables, boot, noSpecial, stream, bound,
    sampleChallenges, certificates, _, ⟨padded_rows_extended sampleChallenges workerRows, rows,
      unified_extensions sampleChallenges certificates, flags, (padded_active trace workers).mpr production⟩,
    activeRows, padding⟩

end Airbender.Trace.Machine.Native
