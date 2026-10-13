import Airbender.Review.Helpers.Sail

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
  /-- Execute the selected path in Machine mode. -/
  privilege : state.regs.get? .cur_privilege = some .Machine
  /-- Zero mstatus selects the reviewed direct Machine memory path. -/
  status : state.regs.get? .mstatus = some 0
  /-- The public misa register exists; actual decoding checks required extensions. -/
  isa : ∃ value : BitVec 32, state.regs.get? .misa = some value
  /-- Provide the environment CSR read by the original Sail memory path. -/
  supervisorEnvironment : ∃ value : BitVec 64, state.regs.get? .senvcfg = some value
  /-- Provide the Machine environment CSR; its value remains public configuration. -/
  machineEnvironment : ∃ value : BitVec 64, state.regs.get? .menvcfg = some value
  /-- All PMP configuration entries are zero, disabling PMP restrictions for this path. -/
  pmpOff : state.regs.get? .pmpcfg_n = some (Vector.replicate 64 0)
  /-- Provide PMP address registers even though PMP entries are disabled. -/
  pmpAddresses : ∃ values : Vector (BitVec 32) 64, state.regs.get? .pmpaddr_n = some values
  /-- One RV32 PMA region permits reads, writes and instruction execution. -/
  pma : ∃ attributes : SailRV32.PMA,
    state.regs.get? .pma_regions = some [rv32Region attributes] ∧
      attributes.readable = true ∧ attributes.writable = true ∧ attributes.executable = true
  /-- Provide the hart ID required by the platform memory helpers. -/
  hart : ∃ value : BitVec 32, state.regs.get? .mhartid = some value
  /-- Disable the platform HTIF special-memory path. -/
  htifDisabled : state.regs.get? .htif_tohost_base = some none

end Airbender.Reference.RiscV.Sail
