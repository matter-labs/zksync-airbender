import Human.Helpers.Core.Configuration

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

end Airbender.Reference.RiscV.Sail
