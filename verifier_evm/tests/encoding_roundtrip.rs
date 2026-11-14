//! F1 round factorization, including its degenerate points.
use field::{Field, Proth120};
use verifier_evm::encoding::*;
fn fe(v: u128) -> Proth120 {
    Proth120::new(v)
}

#[test]
fn e1_factorization_including_degenerate_points() {
    let p = Proth120::ORDER;
    let u = [fe(5), fe(p - 7), fe(11)];
    let half = fe(2).inverse().unwrap();
    let mut halves = u;
    for v in &mut halves {
        v.mul_assign(&half);
    }
    for (z, coefficients) in [
        (half, [halves[0], halves[1], halves[2], Proth120::ZERO]),
        (Proth120::ONE, [fe(0), fe(5), fe(p - 7), fe(11)]),
        (Proth120::ZERO, [fe(5), fe(p - 12), fe(18), fe(p - 11)]),
        (fe(3), [fe(p - 10), fe(39), fe(p - 57), fe(55)]),
    ] {
        assert_eq!(split_round(&coefficients, z), u);
    }
    for (z, bad) in [
        (half, [fe(0), fe(1), fe(2), fe(3)]),
        (Proth120::ONE, [fe(1), fe(1), fe(2), fe(3)]),
    ] {
        assert!(std::panic::catch_unwind(|| split_round(&bad, z)).is_err());
    }
}
