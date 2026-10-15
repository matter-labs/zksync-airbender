//! `DIGEST`: the first `digest_bytes` of a Keccak Merkle digest's big-endian bytes.

/// Wire bytes of `d`. Panics when a byte past `digest_bytes` is nonzero (a digest of
/// another commitment profile).
pub fn digest_wire(d: &[u32; 8], digest_bytes: usize) -> Vec<u8> {
    assert!(
        (1..=32).contains(&digest_bytes),
        "digest_bytes must be in 1..=32"
    );
    let be: Vec<u8> = d.iter().flat_map(|w| w.to_be_bytes()).collect();
    assert!(
        be[digest_bytes..].iter().all(|b| *b == 0),
        "digest has nonzero bytes past digest_bytes = {digest_bytes}"
    );
    be[..digest_bytes].to_vec()
}

/// Inverse of [`digest_wire`]: the zero-padded `[u32; 8]` digest.
pub fn digest_from_wire(bytes: &[u8]) -> [u32; 8] {
    assert!(bytes.len() <= 32, "digest wider than 32 bytes");
    let mut be = [0u8; 32];
    be[..bytes.len()].copy_from_slice(bytes);
    std::array::from_fn(|i| u32::from_be_bytes(be[4 * i..4 * i + 4].try_into().unwrap()))
}
