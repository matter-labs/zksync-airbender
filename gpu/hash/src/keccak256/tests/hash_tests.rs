use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::stream::CudaStream;
use sha3::{Digest as _, Keccak256};

use super::super::{hash_bytes, Digest};

#[test]
fn keccak256_hash_known_vectors() {
    let lengths = [
        0, 1, 3, 31, 32, 40, 64, 135, 136, 137, 255, 256, 271, 272, 273, 448, 1000,
    ];
    let stream = CudaStream::default();
    let mut state = 0x4c2c_1ff0_b069_c15du64;
    for len in lengths {
        let input: Vec<u8> = (0..len)
            .map(|_| {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                state as u8
            })
            .collect();
        for offset in [1, 7] {
            check_hash(&input, offset, &stream);
        }
    }
    for (input, vector) in [
        (
            &b""[..],
            "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
        ),
        (
            &b"abc"[..],
            "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45",
        ),
    ] {
        let expected: Vec<u8> = (0..32)
            .map(|i| u8::from_str_radix(&vector[2 * i..2 * i + 2], 16).unwrap())
            .collect();
        assert_eq!(Keccak256::digest(input).as_slice(), expected);
        assert_eq!(check_hash(input, 1, &stream), expected.as_slice());
    }
}

fn check_hash(input: &[u8], offset: usize, stream: &CudaStream) -> [u8; 32] {
    let mut staged = vec![0x5c; offset + input.len() + 7];
    staged[offset..offset + input.len()].copy_from_slice(input);
    let mut d_input = DeviceAllocation::alloc(staged.len()).unwrap();
    let mut d_out = DeviceAllocation::alloc(48).unwrap();
    memory_copy_async(&mut d_input, &staged, stream).unwrap();
    memory_copy_async(&mut d_out, &[0xaa; 48], stream).unwrap();
    hash_bytes(
        &d_input[offset..offset + input.len()],
        &mut d_out[7..39],
        stream,
    )
    .unwrap();
    let mut output = [0u8; 48];
    memory_copy_async(&mut output, &d_out, stream).unwrap();
    stream.synchronize().unwrap();
    let expected = Keccak256::digest(input);
    assert_eq!(
        &output[7..39],
        expected.as_slice(),
        "len={}, offset={offset}",
        input.len()
    );
    assert_eq!(&output[..7], &[0xaa; 7]);
    assert_eq!(&output[39..], &[0xaa; 9]);
    let digest: Digest = std::array::from_fn(|i| {
        u32::from_be_bytes(output[7 + 4 * i..11 + 4 * i].try_into().unwrap())
    });
    for (word, bytes) in digest.iter().zip(expected.as_chunks::<4>().0) {
        assert_eq!(*word, u32::from_be_bytes(*bytes));
    }
    output[7..39].try_into().unwrap()
}
