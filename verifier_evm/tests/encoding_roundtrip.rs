//! F1 encoder: primitive vectors, the E1 factorization, the transcript replay, and the
//! structural roundtrip `decode(encode(proof)) == v0` on the committed proof.

mod common;

use field::{Field, Proth120};
use verifier_evm::encoding::*;

const P: u128 = Proth120::ORDER;
fn fe(v: u128) -> Proth120 {
    Proth120::new(v)
}

/// One 123-bit lane as a 16-byte `FE-run(1)`, the 5 pad bits set to `pad`.
fn lane(v: u128, pad: u128) -> Vec<u8> {
    ((v << 5) | pad).to_be_bytes().to_vec()
}

#[test]
fn fe_run_sizes_and_lane_boundaries() {
    for n in [0usize, 1, 2, 7, 8, 160] {
        let els: Vec<Proth120> = (0..n as u128)
            .map(|i| match i % 4 {
                0 => fe(P - 1),
                1 => fe(0),
                2 => fe(1),
                _ => fe((i * 0x9e37_79b9_7f4a_7c15) % P),
            })
            .collect();
        let bytes = write_fe_run(&els);
        assert_eq!(bytes.len(), (123 * n).div_ceil(8));
        assert_eq!(bytes.len(), fe_run_len(n));
        assert_eq!(read_fe_run(&bytes, n), els);
        // Element j starts at bit 123·j: one 32-byte word load at byte (123·j) >> 3 holds it.
        for (j, e) in els.iter().enumerate() {
            let bit = 123 * j;
            let mut word = [0u8; 32];
            let tail = &bytes[bit / 8..(bit / 8 + 32).min(bytes.len())];
            word[..tail.len()].copy_from_slice(tail);
            let hi = u128::from_be_bytes(word[..16].try_into().unwrap());
            let lo = u128::from_be_bytes(word[16..].try_into().unwrap());
            let shift = 256 - 123 - bit % 8;
            let v = if shift >= 128 {
                hi >> (shift - 128)
            } else {
                (hi << (128 - shift)) | (lo >> shift)
            } & ((1u128 << 123) - 1);
            assert_eq!(v, e.to_u128(), "lane {j} of FE-run({n})");
        }
    }
    assert_eq!(read_fe_run(&lane(P - 1, 0), 1), vec![fe(P - 1)]);
    for bad in [P, (1u128 << 123) - 1] {
        common::assert_panics_with("non-canonical field element", || {
            read_fe_run(&lane(bad, 0), 1)
        });
    }
    common::assert_panics_with("run padding bits must be zero", || {
        read_fe_run(&lane(1, 1), 1)
    });
    common::assert_panics_with("run length mismatch", || read_fe_run(&lane(1, 0)[..15], 1));
}

#[test]
fn ts_run_roundtrip_and_bounds() {
    let max = (1u32 << 19) - 1;
    let pairs: Vec<(u32, u32)> = (0..33u32).map(|i| (max - i, i % 16)).collect();
    let bytes = write_ts_run(&pairs);
    assert_eq!(bytes.len(), 157);
    assert_eq!(bytes.len(), ts_run_len(33));
    assert_eq!(read_ts_run(&bytes, 33), pairs);
    common::assert_panics_with("value exceeds 19 bits", || write_ts_run(&[(1 << 19, 0)]));
    let mut padded = bytes.clone();
    *padded.last_mut().unwrap() |= 1;
    common::assert_panics_with("run padding bits must be zero", || read_ts_run(&padded, 33));
}

#[test]
fn digest_wire_truncates_only_zero_tails() {
    let d: [u32; 8] = std::array::from_fn(|i| 0x0101_0101 * (i as u32 + 1));
    assert_eq!(digest_from_wire(&digest_wire(&d, 32)), d);
    common::assert_panics_with("digest has nonzero bytes past digest_bytes = 25", || {
        digest_wire(&d, 25)
    });
    let mut t = d;
    t[6] &= 0xff00_0000;
    t[7] = 0;
    let wire = digest_wire(&t, 25);
    assert_eq!(wire.len(), 25);
    assert_eq!(digest_from_wire(&wire), t);
}

#[test]
fn e1_factorization_including_degenerate_points() {
    let half = fe(2).inverse().unwrap();
    let u = [fe(5), fe(P - 7), fe(123_456_789)];
    for z in [fe(3), fe(P - 2), half, Proth120::ONE, Proth120::ZERO] {
        let p = join_round(u, z);
        assert_eq!(split_round(&p, z), u, "z = {z:?}");
        // p(0) + p(1) = a + z·(b + c) = K, so a is recovered from K and (b, c).
        let mut k = p[0];
        k.double();
        for c in &p[1..] {
            k.add_assign(c);
        }
        assert_eq!(round_constant(k, z, u[1], u[2]), u[0]);
        // u(r) = p(r) / e_z(r)
        let r = fe(0xdead_beef);
        let mut p_r = Proth120::ZERO;
        for c in p.iter().rev() {
            p_r.mul_assign(&r);
            p_r.add_assign(c);
        }
        let mut e_r = Proth120::ONE;
        e_r.sub_assign(&z);
        let mut s = z;
        s.double();
        s.sub_assign(&Proth120::ONE);
        s.mul_assign(&r);
        e_r.add_assign(&s);
        let mut lhs = eval_quadratic(u, r);
        lhs.mul_assign(&e_r);
        assert_eq!(lhs, p_r);
    }
    let mut bad = join_round(u, fe(3));
    bad[1].add_assign(&Proth120::ONE);
    common::assert_panics_with("round polynomial is not e_z(X) times a quadratic", || {
        split_round(&bad, fe(3))
    });
    common::assert_panics_with("round polynomial is not e_z(X) times a quadratic", || {
        split_round(&[fe(0), fe(1), fe(2), fe(3)], half)
    });
    common::assert_panics_with("round polynomial is not e_z(X) times a quadratic", || {
        split_round(&[fe(1), fe(1), fe(2), fe(3)], Proth120::ONE)
    });
}

#[test]
fn committed_f1_calldata_is_current() {
    for version in common::available_versions("F1 calldata drift") {
        let (circuit, proof, aux) = version.load();
        let f1 = encode_single_tx(&circuit, &proof, &aux, &version.f1_params());
        let read = |name: &str| {
            std::fs::read_to_string(version.data_path(name)).unwrap_or_else(|_| {
                panic!(
                    "missing {name}: rerun `AB_EVM_VERSION={} cargo test -p verifier_evm --test flatten_calldata -- --ignored`",
                    version.name
                )
            })
        };
        assert!(
            read(common::F1_CALLDATA).trim() == hex::encode(&f1.bytes),
            "{} is stale",
            common::F1_CALLDATA
        );
        let stored: serde_json::Value = serde_json::from_str(&read(common::F1_FIELDS)).unwrap();
        assert_eq!(
            stored,
            common::f1_field_metadata(&f1, &version.f1_params()),
            "{} is stale",
            common::F1_FIELDS
        );
    }
}

#[test]
fn replay_reaches_the_recorded_handoff_seed() {
    for version in common::available_versions("F1 transcript replay") {
        let (circuit, proof, aux) = version.load();
        let replay = replay_gkr_points(&circuit, &proof, &aux);
        assert_eq!(
            Some(replay.handoff_seed),
            proof.intermediate_transcript_seed
        );
        // dimension-reducing layers bind e..t−1 variables, the circuit layers t each
        let params = version.f1_params();
        let (e, t) = (params.explicit_output_log2, params.trace_log2);
        let rounds: usize = replay.layers.iter().map(|l| l.r.len()).sum();
        assert_eq!(rounds, (e..t).sum::<usize>() + circuit.layers.len() * t);
    }
}

#[test]
fn f1_roundtrip_reproduces_v0() {
    for version in common::available_versions("F1 roundtrip") {
        let (circuit, proof, aux) = version.load();
        let params = version.f1_params();
        let f1 = encode_single_tx(&circuit, &proof, &aux, &params);
        let frontier = version.setup_frontier().map(|(_, nodes)| nodes);
        let hints = DecodeHints::from_proof(&circuit, &proof, &aux, &params, frontier.as_deref());
        let (gkr, whir) = decode_structural(&f1.bytes, &params, &hints);
        assert_eq!(
            gkr,
            verifier_evm::gkr_calldata(&circuit, &proof, &aux),
            "GKR v0"
        );
        let whir_v0 =
            verifier_evm::whir_stream(&circuit, &proof, &aux, &params.folds, &params.queries);
        assert_eq!(whir, whir_v0, "WHIR v0 stream");
        assert_eq!(
            f1.fields.values().map(|(_, len)| len).sum::<usize>(),
            f1.bytes.len()
        );

        let digests: usize = f1
            .fields
            .iter()
            .filter(|(name, _)| name.ends_with("cap") || name.ends_with("path"))
            .map(|(_, (_, len))| len / params.digest_bytes)
            .sum();
        let profile = (
            params.digest_bytes,
            params.explicit_output_log2,
            params.setup_frontier_level,
        );
        let (_, pinned) = INDEPENDENT_LAYOUT_COUNTS
            .iter()
            .find(|(p, _)| *p == profile)
            .unwrap_or_else(|| {
                panic!(
                    "no independent layout-model counts for profile {profile:?}: rerun the w7ba C1 \
                     model on the new fixtures and add its row"
                )
            });
        assert_eq!((f1.gkr_bytes, f1.bytes.len(), digests), *pinned);
    }
}

/// F1 byte counts of the committed proof from the independent layout model (pair w7ba, C1:
/// orange/.agents/plans/2026-10-15-w7b-impl/w7ba/f1-layout-codex.md; C12 and C13 for the later rows),
/// per profile `(digest_bytes, explicit_output_log2, setup_frontier_level)`:
/// `(gkr_bytes, total bytes, wire digests)`.
const INDEPENDENT_LAYOUT_COUNTS: &[((usize, usize, usize), (usize, usize, usize))] = &[
    ((32, 4, 3), (21_523, 88_043, 1_597)),
    ((32, 4, 9), (21_523, 85_355, 1_513)),
    ((25, 2, 3), (20_393, 75_790, 1_597)),
    ((25, 2, 9), (20_393, 73_690, 1_513)),
];

#[test]
fn f1_decoder_rejects_malformed_streams() {
    for version in common::available_versions("F1 malformed streams") {
        let (circuit, proof, aux) = version.load();
        let params = version.f1_params();
        let f1 = encode_single_tx(&circuit, &proof, &aux, &params);
        let frontier = version.setup_frontier().map(|(_, nodes)| nodes);
        let hints = DecodeHints::from_proof(&circuit, &proof, &aux, &params, frontier.as_deref());
        let decode = |bytes: Vec<u8>| decode_structural(&bytes, &params, &hints);
        common::assert_panics_with("F1 stream truncated", || {
            decode(f1.bytes[..f1.bytes.len() - 1].to_vec())
        });
        common::assert_panics_with("trailing bytes after the F1 stream", || {
            decode([f1.bytes.clone(), vec![0]].concat())
        });
        // 114 base-layer at-point evals: 14,022 bits in 1,753 bytes, two pad bits.
        let (offset, len) = f1.fields["gkr_layer_0_evals"];
        assert_eq!(len, fe_run_len(114));
        let mut padded = f1.bytes.clone();
        padded[offset + len - 1] |= 1;
        common::assert_panics_with("run padding bits must be zero", || decode(padded));
        let (offset, _) = f1.fields["gkr_output_evals"];
        let mut non_canonical = f1.bytes.clone();
        non_canonical[offset..offset + 2].copy_from_slice(&[0xff, 0xff]);
        common::assert_panics_with("non-canonical field element", || decode(non_canonical));
        let (offset, _) = f1.fields["whir_0_ood"];
        let mut ood = f1.bytes.clone();
        ood[offset..offset + 16].copy_from_slice(&Proth120::ORDER.to_be_bytes());
        common::assert_panics_with("non-canonical field element", || decode(ood));
    }
}

#[test]
fn encoder_rejects_a_profile_the_proof_does_not_fit() {
    for version in common::available_versions("F1 profile preflight") {
        let (circuit, proof, aux) = version.load();
        let params = version.f1_params();
        let encode = |p: FormatParams| encode_single_tx(&circuit, &proof, &aux, &p);
        let mut p = params.clone();
        p.pack_log2 -= 1;
        common::assert_panics_with("profile packing differs from the proof aux", || encode(p));
        let mut p = params.clone();
        p.folds[0] += 1;
        p.folds[1] -= 1;
        common::assert_panics_with("profile folds differ from the proof", || encode(p));
        let mut p = params.clone();
        p.queries[0] -= 1;
        common::assert_panics_with("profile queries differ from the proof", || encode(p));
        let mut p = params.clone();
        p.explicit_output_log2 -= 1;
        common::assert_panics_with("profile explicit output log differs from the proof", || {
            encode(p)
        });
        let mut p = params.clone();
        p.trace_log2 += 1;
        common::assert_panics_with("profile trace log differs from the circuit", || encode(p));
        let mut p = params.clone();
        p.cap_log2 += 1;
        common::assert_panics_with("profile cap differs from the proof", || encode(p));
    }
}

#[test]
fn decoder_derives_omitted_setup_siblings_from_the_frontier() {
    for version in common::available_versions("F1 setup frontier tails") {
        let params = version.f1_params();
        if params.setup_frontier_skip() == 0 {
            continue;
        }
        let (circuit, proof, aux) = version.load();
        let (_, mut frontier) = version.setup_frontier().unwrap();
        let f1 = encode_single_tx(&circuit, &proof, &aux, &params);
        // the tails come from the frontier: another frontier decodes to other setup siblings
        let index = proof.whir_proof.setup_commitment.queries[0].index;
        let height =
            proof.whir_proof.setup_commitment.queries[0].path.len() - params.setup_frontier_skip();
        frontier[(index >> height) ^ 1][0] ^= 1;
        let hints = DecodeHints::from_proof(&circuit, &proof, &aux, &params, Some(&frontier));
        let (_, whir) = decode_structural(&f1.bytes, &params, &hints);
        let whir_v0 =
            verifier_evm::whir_stream(&circuit, &proof, &aux, &params.folds, &params.queries);
        assert_ne!(whir, whir_v0);
    }
}
