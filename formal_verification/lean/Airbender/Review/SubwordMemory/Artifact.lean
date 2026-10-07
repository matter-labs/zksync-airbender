import Airbender.Import.Embed

namespace Airbender.SubwordMemory

-- All retained equations, five ranges and both non-decoder lookup sets.
-- The tagged setup table is caller-supplied; its fixed/ROM semantics and
-- program/setup binding are separate obligations. RAM load/store claims are in Theorems.
import_clean importedConstraints from "../../cs/compiled_circuits/mem_subword_only_layout_no_caches_gkr.json" subword_memory_lookups

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 43 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 7 := rfl

namespace Variables
abbrev initialPCLo := 0
abbrev initialPCHi := 1
abbrev execute := 4
abbrev storeSelector := 10
abbrev byteSelector := 11
abbrev signedSelector := 12
abbrev finalPCLo := 13
abbrev finalPCHi := 14
end Variables

-- Every named logical column used by the supporting equation proofs.
theorem variable_roles :
    importedConstraintsVariableNames.lookup 0 = some "initial_pc[0]" ∧
    importedConstraintsVariableNames.lookup 1 = some "initial_pc[1]" ∧
    importedConstraintsVariableNames.lookup 4 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 5 = some "rs1 index from decoder" ∧
    importedConstraintsVariableNames.lookup 6 = some "rs2 index from decoder" ∧
    importedConstraintsVariableNames.lookup 7 = some "rd index from decoder" ∧
    importedConstraintsVariableNames.lookup 8 = some "imm[0] from decoder" ∧
    importedConstraintsVariableNames.lookup 9 = some "imm[1] from decoder" ∧
    importedConstraintsVariableNames.lookup 10 = some "family_bit[0]" ∧
    importedConstraintsVariableNames.lookup 11 = some "family_bit[1]" ∧
    importedConstraintsVariableNames.lookup 12 = some "family_bit[2]" ∧
    importedConstraintsVariableNames.lookup 13 = some "final_pc[0]" ∧
    importedConstraintsVariableNames.lookup 14 = some "final_pc[1]" ∧
    importedConstraintsVariableNames.lookup 19 = some "rs1 read_value[0]" ∧
    importedConstraintsVariableNames.lookup 20 = some "rs1 read_value[1]" ∧
    importedConstraintsVariableNames.lookup 21 = some "memread_addr[0]" ∧
    importedConstraintsVariableNames.lookup 22 = some "memread_addr[1]" ∧
    importedConstraintsVariableNames.lookup 25 = some "mem/rs2 read read_value[0]" ∧
    importedConstraintsVariableNames.lookup 26 = some "mem/rs2 read read_value[1]" ∧
    importedConstraintsVariableNames.lookup 27 = some "memwrite_addr[0]" ∧
    importedConstraintsVariableNames.lookup 28 = some "memwrite_addr[1]" ∧
    importedConstraintsVariableNames.lookup 31 = some "mem/rd write read_value[0]" ∧
    importedConstraintsVariableNames.lookup 32 = some "mem/rd write read_value[1]" ∧
    importedConstraintsVariableNames.lookup 33 = some "mem/rd write write_value[0]" ∧
    importedConstraintsVariableNames.lookup 34 = some "mem/rd write write_value[1]" ∧
    importedConstraintsVariableNames.lookup 35 = some "address bit0" ∧
    importedConstraintsVariableNames.lookup 36 = some "address bit1" ∧
    importedConstraintsVariableNames.lookup 37 = some "addr ofL (L2)" ∧
    importedConstraintsVariableNames.lookup 38 = some "addr ofH (L2)" ∧
    importedConstraintsVariableNames.lookup 39 = some "cleanaddr_lo (canonical 16-bit)" ∧
    importedConstraintsVariableNames.lookup 40 = some "cleanaddr_lo >> 2 (word cell index low)" ∧
    importedConstraintsVariableNames.lookup 41 = some "flag: are we in rom addr range?" ∧
    importedConstraintsVariableNames.lookup 42 = some "residue (L2)" ∧
    importedConstraintsVariableNames.lookup 43 = some "clear (SB: mem[addr] halfword byte gets set to 0)" ∧
    importedConstraintsVariableNames.lookup 44 = some "STORE*B: clear's table input: SEL(b1, OLDH, OLDL) || b0 (L2)" ∧
    importedConstraintsVariableNames.lookup 45 = some "clear (L2)" ∧
    importedConstraintsVariableNames.lookup 46 = some "rom (L2)" ∧
    importedConstraintsVariableNames.lookup 47 = some "ram (L2)" ∧
    importedConstraintsVariableNames.lookup 48 = some "store (L2)" ∧
    importedConstraintsVariableNames.lookup 49 = some "rom_input (L2)" ∧
    importedConstraintsVariableNames.lookup 50 = some "ram_input (L2)" ∧
    importedConstraintsVariableNames.lookup 51 = some "store_bytemasked_input (L2)" ∧
    importedConstraintsVariableNames.lookup 52 = some "final lookup input (L3)" ∧
    importedConstraintsVariableNames.lookup 53 = some "memwrite_lo (L2)" ∧
    importedConstraintsVariableNames.lookup 54 = some "keep (L2)" ∧
    importedConstraintsVariableNames.lookup 55 = some "final lookup output1 (L3)" ∧
    importedConstraintsVariableNames.lookup 56 = some "memwrite_hi (L2)" ∧
    importedConstraintsVariableNames.lookup 57 = some "constrained_memwrite_halfword (L2)" ∧
    importedConstraintsVariableNames.lookup 58 = some "final lookup output2 (L3)" ∧
    importedConstraintsVariableNames.lookup 59 = some "table_id (L2)" ∧
    importedConstraintsVariableNames.lookup 60 = some "execute (L2)" ∧
    importedConstraintsVariableNames.lookup 61 = some "final lookup table_id (L3)" ∧
    importedConstraintsVariableNames.lookup 62 = some "query 0, interim ts borrow" ∧
    importedConstraintsVariableNames.lookup 63 = some "query 1, interim ts borrow" ∧
    importedConstraintsVariableNames.lookup 64 = some "query 2, interim ts borrow" := by
  repeat' apply And.intro
  all_goals decide

end Airbender.SubwordMemory
