module
public import Proven.NonVacuous.UnrolledNative.Arguments
public import Proven.NonVacuous.UnrolledNative.LookupCheck
public import Proven.Compiler.CPUWitnesses.AddSub

@[expose] public section
namespace Airbender.NonVacuous.UnrolledNative
open Trace Trace.Machine Compiler
set_option warningAsError true

/-- The submitted ADD row has all native gates, placements, public lookups and participation. -/
noncomputable def rowCertificate : ProgramLogicalRowCertificate tables :=
  CPUWitnesses.AddSub.of_checked PooledBoot.initial program PooledBoot.assignment
    source_satisfied lookup_check (by kernel_rfl)

/-- The cached certificate retains the complete submitted ADD assignment. -/
theorem certificate_row : rowCertificate.row = PooledBoot.row := rfl

end Airbender.NonVacuous.UnrolledNative

namespace Airbender.NonVacuous.Machine
open Trace Trace.Machine

/-- One native ADD row meets the complete full unsigned target premises. -/
theorem full_native : Native.UnrolledFullFromNativeSatisfiableClaim :=
  UnrolledNative.full_of_certificate UnrolledNative.rowCertificate UnrolledNative.certificate_row

/-- One native ADD row meets the complete reduced target premises. -/
theorem reduced_native : Native.UnrolledReducedFromNativeSatisfiableClaim :=
  UnrolledNative.reduced_of_certificate UnrolledNative.rowCertificate UnrolledNative.certificate_row

end Airbender.NonVacuous.Machine
