//! Challenge-bank classification by TRANSFER CHANNEL (spec §5). All forward
//! challenges are per-proof Fiat-Shamir outputs; the axis is where the value
//! is materialized: α/γ are device-squeezed (`ConstChallenge`, __constant__),
//! perm/additive are host-drawn at schedule time (`ArgChallenge`, kernel-arg).
//! α enters as a COLUMN-INDEXED power bank (acc = Σ α^k·col_k), never raised
//! per-step; γ as [γ, γ², 2γ].

use crate::isa_v2::LdcSub;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChallengeFamily {
    Alpha,
    Gamma,
    PermLinearization,
    AdditiveSeed,
}

pub fn bank_for_family(f: ChallengeFamily) -> LdcSub {
    match f {
        ChallengeFamily::Alpha | ChallengeFamily::Gamma => LdcSub::ConstChallenge,
        ChallengeFamily::PermLinearization | ChallengeFamily::AdditiveSeed => LdcSub::ArgChallenge,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AlphaSlot {
    /// col_0: α^0 = 1, multiply-free lift — no bank read needed.
    OneLift,
    /// col_k (k > 0): read bank entry k for α^k.
    Power(u16),
}

pub fn alpha_power_bank_index(col_k: u16) -> AlphaSlot {
    if col_k == 0 {
        AlphaSlot::OneLift
    } else {
        AlphaSlot::Power(col_k)
    }
}

/// Reuse v1's bf-const dedup verbatim (compiler::build_const_table): sorted,
/// deduped, excludes 0/1/NEG_ONE_U32, asserts <= 256. NOTE (F4): the v1 fn is
/// `pub(crate)`, so `pub use` is a hard compile error (E0364, "only public
/// within the crate, cannot be re-exported outside"). Use `pub(crate) use` —
/// every consumer (challenges.rs tests, macros.rs lowering) is in-crate.
/// Same hazard for any other `pub(crate)` v1 item Task 2.0 exposes
/// (slots/pinning/enumerate_sources): reference by path or `pub(crate) use`,
/// never `pub use`.
pub(crate) use crate::compiler::build_const_table;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn challenge_channel_by_family() {
        assert_eq!(bank_for_family(ChallengeFamily::Alpha), LdcSub::ConstChallenge);
        assert_eq!(bank_for_family(ChallengeFamily::Gamma), LdcSub::ConstChallenge);
        assert_eq!(bank_for_family(ChallengeFamily::PermLinearization), LdcSub::ArgChallenge);
        assert_eq!(bank_for_family(ChallengeFamily::AdditiveSeed), LdcSub::ArgChallenge);
    }

    #[test]
    fn alpha_powers_are_column_indexed() {
        // col_0 = α^0 = 1 (multiply-free lift); col_k reads bank entry k.
        assert_eq!(alpha_power_bank_index(0), AlphaSlot::OneLift);
        assert_eq!(alpha_power_bank_index(5), AlphaSlot::Power(5));
    }
}
