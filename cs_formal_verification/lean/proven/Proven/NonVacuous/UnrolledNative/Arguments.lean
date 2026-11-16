module
public import Proven.NonVacuous.UnrolledNative.Premises

@[expose] public section
namespace Airbender.NonVacuous.UnrolledNative
open Trace Trace.Machine Arithmetic Compiler NativeArithmetic
set_option warningAsError true

/-- One cached ADD certificate describes the complete submitted CPU trace. -/
theorem arguments (entry : ProgramLogicalRowCertificate tables)
    (represented : entry.row = PooledBoot.row) :
    UnrolledNativeArguments tables [entry] trace Machine.workers := by
  refine ⟨⟨[], rfl, rfl⟩, ?_, states, requests, memory⟩
  change [PooledBoot.row] = [entry.row]
  rw [represented]

/-- One native ADD row meets every premise of the full unsigned target. -/
theorem full_of_certificate (entry : ProgramLogicalRowCertificate tables)
    (represented : entry.row = PooledBoot.row) : Native.UnrolledFullFromNativeSatisfiableClaim := by
  refine ⟨trace, Machine.workers, PooledBoot.initial, PooledBoot.cells, program, PooledBoot.inits,
    tables, rfl, rfl, rfl, boot _ (Or.inl rfl), rfl, rfl, rfl, no_special, stream_ports,
    tables_bound, covers_rom, [entry], arguments entry represented⟩

/-- One native ADD row meets every premise of the reduced target. -/
theorem reduced_of_certificate (entry : ProgramLogicalRowCertificate tables)
    (represented : entry.row = PooledBoot.row) : Native.UnrolledReducedFromNativeSatisfiableClaim := by
  refine ⟨trace, Machine.workers, PooledBoot.initial, PooledBoot.cells, program, PooledBoot.inits,
    tables, rfl, rfl, rfl, boot _ (Or.inr rfl), rfl, rfl, rfl, stream_ports,
    tables_bound, covers_rom, [entry], arguments entry represented⟩

end Airbender.NonVacuous.UnrolledNative
