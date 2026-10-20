//! Zlib-compressed JSON for local calibration fixtures, not the proof wire format.

use std::io::{Read, Write};

/// Encode a fixture and return the finished writer so files can be synced before publication.
pub fn encode<T: serde::Serialize, W: Write>(value: &T, output: W) -> W {
    let mut encoder = flate2::write::ZlibEncoder::new(output, flate2::Compression::default());
    serde_json::to_writer(&mut encoder, value).expect("serialize fixture");
    encoder.finish().expect("finish fixture compression")
}

/// Decode a fixture written by [`encode`].
pub fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> T {
    let mut decoder = flate2::read::ZlibDecoder::new(bytes);
    let mut unpacked = Vec::new();
    decoder
        .read_to_end(&mut unpacked)
        .expect("decompress fixture");
    serde_json::from_slice(&unpacked).expect("deserialize fixture")
}
