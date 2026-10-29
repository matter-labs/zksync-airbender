import Airbender.Review.Circuits.Keccak.SplitColumnParity
import Airbender.Review.Circuits.Keccak.SplitThetaRho
import Airbender.Review.Circuits.Keccak.SplitChi5
import Airbender.Review.Circuits.Keccak.SplitColumnParityCached
import Airbender.Review.Circuits.Keccak.SplitThetaRhoCached
import Airbender.Review.Circuits.Keccak.SplitChi5Cached
import Airbender.Review.Trace.Workers.Keccak.SplitNative

namespace Airbender.Keccak.Split.Proofs

/-- The emitted native timestamp query arrays and grouped metadata retain
the exact sizes of the three split compiled artifacts. -/
theorem column_parity_timestamp_queries {p : Nat} [Fact p.Prime] :
    (ColumnParity.importedConstraintsTimestampLookups (p := p)).length = 30 := by rfl

theorem theta_rho_timestamp_queries {p : Nat} [Fact p.Prime] :
    (ThetaRho.importedConstraintsTimestampLookups (p := p)).length = 2 := by rfl

theorem chi5_timestamp_queries {p : Nat} [Fact p.Prime] :
    (Chi5.importedConstraintsTimestampLookups (p := p)).length = 2 := by rfl

theorem theta_rho_timestamp_groups :
    ThetaRho.importedConstraintsTimestampGroups.size = 4 := by rfl

theorem chi5_timestamp_groups :
    Chi5.importedConstraintsTimestampGroups.size = 6 := by rfl

theorem column_parity_cached_timestamp_queries {p : Nat} [Fact p.Prime] :
    (ColumnParityCached.importedConstraintsTimestampLookups (p := p)).length = 30 := by rfl

theorem theta_rho_cached_timestamp_queries {p : Nat} [Fact p.Prime] :
    (ThetaRhoCached.importedConstraintsTimestampLookups (p := p)).length = 2 := by rfl

theorem chi5_cached_timestamp_queries {p : Nat} [Fact p.Prime] :
    (Chi5Cached.importedConstraintsTimestampLookups (p := p)).length = 2 := by rfl

theorem theta_rho_cached_timestamp_groups :
    ThetaRhoCached.importedConstraintsTimestampGroups.size = 4 := by rfl

theorem chi5_cached_timestamp_groups :
    Chi5Cached.importedConstraintsTimestampGroups.size = 6 := by rfl

/-- The importer retains every physical split-worker memory port in the
compiled layout, in both cache modes. The grouped timestamp parser checks that
the theta/rho and chi5 ports each have one native group owner. -/
theorem column_parity_memory_ports :
    ColumnParity.importedConstraintsMemoryPorts.size = 14 := by rfl

theorem theta_rho_memory_ports :
    ThetaRho.importedConstraintsMemoryPorts.size = 16 := by rfl

theorem chi5_memory_ports :
    Chi5.importedConstraintsMemoryPorts.size = 12 := by rfl

theorem column_parity_cached_memory_ports :
    ColumnParityCached.importedConstraintsMemoryPorts.size = 14 := by rfl

theorem theta_rho_cached_memory_ports :
    ThetaRhoCached.importedConstraintsMemoryPorts.size = 16 := by rfl

theorem chi5_cached_memory_ports :
    Chi5Cached.importedConstraintsMemoryPorts.size = 12 := by rfl

/-- Both independently emitted metadata arrays select the same native
previous-time and write-offset descriptor for every physical memory port. -/
theorem split_port_clocks_match {p : Nat} (cached : Bool) (row : Native.Row p) :
    (row.ports cached).map Airbender.Trace.MemoryPort.clock =
      (row.columns cached).ports := by
  cases row with
  | mk kind assignment =>
    cases cached <;> cases kind <;>
      simp only [Native.Row.ports, Native.Row.columns] <;>
      decide +kernel

end Airbender.Keccak.Split.Proofs
