import Airbender.Review.Sail

namespace Airbender.Reference.RiscV.Sail

/-- One native PMA region covering RV32. Its permissions remain actual public
    Sail configuration data; this does not define instruction behavior. -/
def rv32Region (attributes : SailRV32.PMA) : SailRV32.PMA_Region :=
  ⟨0, 4294967296, attributes, false⟩

/-- The ordinary-memory domain excludes the pinned platform's CLINT and
    signature windows. HTIF is disabled separately by its initialized CSR. -/
def OrdinaryWordAddress (address : BitVec 32) : Prop :=
  (address.toNat < SailRV32.Functions.plat_clint_base.toNat ∨
    SailRV32.Functions.plat_clint_base.toNat + SailRV32.Functions.plat_clint_size.toNat ≤
      address.toNat) ∧
  (address.toNat < SailRV32.Functions.plat_sig_base.toNat ∨
    SailRV32.Functions.plat_sig_base.toNat + SailRV32.Functions.plat_sig_size.toNat ≤
      address.toNat)

/-- Public CSR data for the selected Machine-mode ordinary-memory execution.
    These conditions specify configuration, not successful accesses or values. -/
structure FlatMemoryConfiguration (state : State) : Prop where
  privilege : state.regs.get? .cur_privilege = some .Machine
  status : state.regs.get? .mstatus = some 0
  isa : ∃ value : BitVec 32, state.regs.get? .misa = some value
  supervisorEnvironment : ∃ value : BitVec 64, state.regs.get? .senvcfg = some value
  machineEnvironment : ∃ value : BitVec 64, state.regs.get? .menvcfg = some value
  pmpOff : state.regs.get? .pmpcfg_n = some (Vector.replicate 64 0)
  pmpAddresses : ∃ values : Vector (BitVec 32) 64, state.regs.get? .pmpaddr_n = some values
  pma : ∃ attributes : SailRV32.PMA,
    state.regs.get? .pma_regions = some [rv32Region attributes] ∧
      attributes.readable = true ∧ attributes.writable = true ∧ attributes.executable = true
  hart : ∃ value : BitVec 32, state.regs.get? .mhartid = some value
  htifDisabled : state.regs.get? .htif_tohost_base = some none

end Airbender.Reference.RiscV.Sail
