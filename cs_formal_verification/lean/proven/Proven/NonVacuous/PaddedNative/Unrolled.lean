module
public import Proven.Compiler.CPUWitnesses.AddSub.Padding
public import Proven.NonVacuous.UnrolledNative.Certificates
public import Proven.NonVacuous.PaddedMachines.Model

@[expose] public section
namespace Airbender.NonVacuous.PaddedNative
open Trace Trace.Machine Compiler PaddingBoundary NonVacuous.PaddedMachines
set_option warningAsError true

/-- The padding assignment satisfies every native source equation. -/
theorem padding_source_check : FullArithmeticNative.AddSubCached.native.artifact.source.all
    (fun polynomial => decide (evaluate (NativeExtension.AddSub.inputValues pooledPaddingAssignment) polynomial = 0)) =
      true := by
  kernel_rfl

theorem padding_source_satisfied : Satisfies FullArithmeticNative.AddSubCached.native.artifact.source
    (NativeExtension.AddSub.inputValues pooledPaddingAssignment) := by
  intro polynomial member
  exact of_decide_eq_true (List.all_eq_true.mp padding_source_check polynomial member)

/-- Every range and timestamp tuple of the padding row is a public table row. -/
theorem padding_lookup_check : CPUWitnesses.canonicalCheck (.pooled .addSub) PooledBoot.initial UnrolledNative.program
    (CPUWitnesses.AddSub.paddingTuples pooledPaddingAssignment) = true := by
  kernel_rfl

/-- The padding row has native gates, placement and public lookups with execute zero. -/
noncomputable def paddingCertificate : ProgramRowCertificate UnrolledNative.tables :=
  CPUWitnesses.AddSub.padding_of_checked PooledBoot.initial UnrolledNative.program pooledPaddingAssignment
    padding_source_satisfied padding_lookup_check rfl

/-- The padding certificate and the active certificate describe the padded layout in order. -/
noncomputable def certificates : List (ProgramRowCertificate UnrolledNative.tables) :=
  [paddingCertificate, UnrolledNative.rowCertificate.toProgramRowCertificate]

theorem arguments : PaddedUnrolledNativeArguments UnrolledNative.tables certificates pooled Machine.workers := by
  refine ⟨⟨[], by simp, rfl, rfl⟩, rfl, ?_, pooled_masked.states, pooled_masked.requests,
    pooled_masked.memory⟩
  intro entry member
  simp only [certificates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr UnrolledNative.rowCertificate.active

/-- One active ADD row and one padding row meet the padded full unsigned native premises. -/
theorem full_witness : Native.PaddedUnrolledFullFromNativeSatisfiableClaim := by
  refine ⟨pooled, Machine.workers, PooledBoot.initial, PooledBoot.cells, UnrolledNative.program, PooledBoot.inits,
    UnrolledNative.tables, ?_, UnrolledNative.no_special, ?_,
    UnrolledNative.tables_bound, UnrolledNative.covers_rom, certificates, arguments, pooled_sizes.2.2.1,
    pooled_sizes.2.2.2⟩
  · simpa only [pooled_active] using UnrolledNative.boot .unrolledFullUnsigned (Or.inl rfl)
  · simpa only [pooled_active] using UnrolledNative.stream_ports

/-- One active ADD row and one padding row meet the padded reduced native premises. -/
theorem reduced_witness : Native.PaddedUnrolledReducedFromNativeSatisfiableClaim := by
  refine ⟨pooled, Machine.workers, PooledBoot.initial, PooledBoot.cells, UnrolledNative.program, PooledBoot.inits,
    UnrolledNative.tables, ?_, ?_,
    UnrolledNative.tables_bound, UnrolledNative.covers_rom, certificates, arguments, pooled_sizes.2.2.1,
    pooled_sizes.2.2.2⟩
  · simpa only [pooled_active] using UnrolledNative.boot .unrolledReduced (Or.inr rfl)
  · simpa only [pooled_active] using UnrolledNative.stream_ports

end Airbender.NonVacuous.PaddedNative
