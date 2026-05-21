use super::*;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit_trait::*;
use crate::types::*;
use field::PrimeField;

use super::mem_word_only_lw_sw::apply_unified_mem_word_only_lw_sw_data_path;

/// Memory-access constraints for the unified circuit.
///
/// This entry point owns the *shared* register/RAM dispatch — the constraints
/// that fire for every family, gated on the per-family bits:
///   - `(NOT is_lw) * (readaddr  - rs2_index) = 0`,  `(NOT is_lw) * readaddr_hi  = 0`
///   - `(NOT is_sw) * (writeaddr - rd_index)  = 0`,  `(NOT is_sw) * writeaddr_hi = 0`
///   - `is_fam4 = is_lw + is_sw` (deg 1, ungated)
/// then hands off to [`apply_unified_mem_word_only_lw_sw_data_path`] for the
/// Family-4-only data path (rs1+imm RAM address, ROM check, ROM-or-data
/// lookup, SW alignment trap).
///
/// Gating Booleans threaded out of this function:
/// - `is_lw` = 1 iff Family 4 LW fires (memread = RAM, memwrite = rd register).
/// - `is_sw` = 1 iff Family 4 SW fires (memread = rs2 register, memwrite = RAM).
/// - `is_fam4` = `is_lw + is_sw`, a 1-bit summary used by Family-4-only blocks.
///
/// Caller (unified body) owns the `memread_addr` / `memwrite_addr` witness
/// vars and passes them inside the access objects.
#[allow(non_snake_case)]
pub fn apply_unified_mem_word_only_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    is_lw: Boolean,
    is_sw: Boolean,
    rs1_limbs: [Variable; REGISTER_SIZE * 2],
    memread_access: RegisterOrRamAccess,
    memwrite_access: RegisterOrRamAccess,
) {
    // LW: rd                          <- mem[addr] || rom[addr]  with +0 offset accepted
    // SW: mem[addr] || trap rom[addr] <- rs2                     with +0 offset accepted
    // NOTE: by preprocessing (decoder lookup) we have rd == 0 for loads not possible

    let WordRepresentation::U8Limbs(memread_u8) = memread_access.read_value else {
        unreachable!("memread access must be allocated as U8Limbs")
    };
    let WordRepresentation::U16Limbs(memwrite_u16) = memwrite_access.write_value else {
        unreachable!("memwrite access must be allocated with U16 write limbs")
    };
    let memread_addr = memread_access.address;
    let memwrite_addr = memwrite_access.address;

    // memread_addr / memwrite_addr are U16 limbs of RAM addresses. The
    // RAM-permutation argument bounds them transitively, but pinning the RC
    // here makes the alignment-trap and ROM-dispatch algebra in the data path
    // below clearly sound without a non-local dependency.
    cs.require_invariant(memread_addr[0], Invariant::RangeChecked { width: 16 });
    cs.require_invariant(memread_addr[1], Invariant::RangeChecked { width: 16 });
    cs.require_invariant(memwrite_addr[0], Invariant::RangeChecked { width: 16 });
    cs.require_invariant(memwrite_addr[1], Invariant::RangeChecked { width: 16 });

    let load = Constraint::from(is_lw);
    let store = Constraint::from(is_sw);

    // is_fam4 = is_lw + is_sw. Booleanity of is_fam4 plus this linear sum
    // enforces mutual exclusivity of LW/SW (a row with both bits set would
    // force is_fam4 = 2, failing Booleanity). The decoder lookup also binds
    // the bitmask atomically
    let is_fam4 = cs.add_named_boolean_variable("is_fam4");
    cs.add_constraint_allow_explicit_linear(
        Constraint::from(is_fam4) - load.clone() - store.clone(),
    );

    let [readaddr_lo, readaddr_hi] = memread_addr.map(Term::from);
    let [writeaddr_lo, writeaddr_hi] = memwrite_addr.map(Term::from);

    // memread_addr is a register slot for Families 1-3 (rs2) and Family 4 SW.
    let memread_is_reg: Constraint<F> = Constraint::from(is_lw.toggle());
    cs.add_constraint(
        memread_is_reg.clone() * (readaddr_lo - Term::from(inputs.decoder_data.rs2_index)),
    );
    cs.add_constraint(memread_is_reg * readaddr_hi);

    // memwrite_addr is a register slot for Families 1-3 (rd) and Family 4 LW.
    let memwrite_is_reg: Constraint<F> = Constraint::from(is_sw.toggle());
    cs.add_constraint(
        memwrite_is_reg.clone() * (writeaddr_lo - Term::from(inputs.decoder_data.rd_index)),
    );
    cs.add_constraint(memwrite_is_reg * writeaddr_hi);

    apply_unified_mem_word_only_lw_sw_data_path(
        cs,
        &inputs,
        is_lw,
        is_sw,
        is_fam4,
        rs1_limbs,
        memread_u8,
        memwrite_u16,
        memread_addr,
        memwrite_addr,
    );
}
