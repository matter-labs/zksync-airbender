use field::{Field, Mersenne31Complex, Mersenne31Field};

#[inline(always)]
fn schoolbook(a: Mersenne31Complex, b: Mersenne31Complex) -> Mersenne31Complex {
    let mut ac = a.c0;
    ac.mul_assign(&b.c0);

    let mut bd = a.c1;
    bd.mul_assign(&b.c1);

    let mut ad = a.c0;
    ad.mul_assign(&b.c1);

    let mut bc = a.c1;
    bc.mul_assign(&b.c0);

    ac.sub_assign(&bd);
    ad.add_assign(&bc);

    Mersenne31Complex { c0: ac, c1: ad }
}

#[test]
fn complex_mul_matches_schoolbook_reference() {
    let edges = [
        0,
        1,
        2,
        (1 << 30) - 1,
        1 << 30,
        Mersenne31Field::ORDER - 1,
        Mersenne31Field::ORDER,
    ];

    for &a0 in &edges {
        for &a1 in &edges {
            for &b0 in &edges {
                for &b1 in &edges {
                    let a = Mersenne31Complex {
                        c0: Mersenne31Field(a0),
                        c1: Mersenne31Field(a1),
                    };
                    let b = Mersenne31Complex {
                        c0: Mersenne31Field(b0),
                        c1: Mersenne31Field(b1),
                    };

                    let mut got = a;
                    got.mul_assign(&b);

                    assert_eq!(got, schoolbook(a, b));
                }
            }
        }
    }

    let mut x = 0x1234_5678u32;
    for _ in 0..250_000 {
        let mut next = || {
            x = x.wrapping_mul(1664525).wrapping_add(1013904223) & Mersenne31Field::ORDER;
            Mersenne31Field(x)
        };

        let a = Mersenne31Complex {
            c0: next(),
            c1: next(),
        };
        let b = Mersenne31Complex {
            c0: next(),
            c1: next(),
        };

        let mut got = a;
        got.mul_assign(&b);

        assert_eq!(got, schoolbook(a, b));
    }
}
