// The native input producer and interpreted verifier share this byte format.
#![allow(dead_code)]

const MAGIC: u32 = u32::from_le_bytes(*b"AFSV");
const VERSION: u32 = 1;
const HEADER_WORDS: usize = 3 + 16;

pub fn encode(expected: &[u32; 16], nds: &[u32]) -> Vec<u8> {
    let mut input = Vec::with_capacity(4 * (HEADER_WORDS + nds.len()));
    let header = [
        MAGIC,
        VERSION,
        u32::try_from(nds.len()).expect("NDS too large"),
    ];
    for word in header.iter().chain(expected).chain(nds) {
        input.extend_from_slice(&word.to_le_bytes());
    }
    input
}

pub fn decode(input: &[u8]) -> ([u32; 16], impl Iterator<Item = u32> + '_) {
    let (bytes, remainder) = input.as_chunks::<4>();
    assert!(remainder.is_empty(), "partial input word");
    // Byte arrays have alignment one; value conversion makes endianness explicit.
    let mut words = bytes.iter().map(|b| u32::from_le_bytes(*b));
    assert_eq!(words.next(), Some(MAGIC), "input magic");
    assert_eq!(words.next(), Some(VERSION), "input version");
    let nds_len = words.next().expect("missing NDS length") as usize;
    assert_eq!(bytes.len(), HEADER_WORDS + nds_len, "input length");
    let expected = core::array::from_fn(|_| words.next().expect("missing output word"));
    (expected, words)
}
