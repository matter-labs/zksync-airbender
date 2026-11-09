use era_cudart::memory::DeviceAllocation;
use era_cudart::stream::CudaStream;

use super::super::{
    transcript_commit_fields, transcript_commit_initial_u32, transcript_commit_u32,
    transcript_draw_fields, transcript_draw_u32, Digest, Seed,
};
use super::{download, upload, TestRng, EDGE_VALUES};
use crate::upstream::{
    Keccak256Seed, Keccak256Transcript, MerkleTreeCapVarLength, Proth120, Transcript,
};

type HostTranscript = Keccak256Transcript;

const SEED_OFFSET: usize = 1;
const GUARD: u8 = 0x5c;

struct DeviceSeed {
    buffer: DeviceAllocation<u8>,
}

impl DeviceSeed {
    fn new(seed: &Seed, stream: &CudaStream) -> Self {
        let mut host = vec![GUARD; SEED_OFFSET + 32 + 7];
        host[SEED_OFFSET..SEED_OFFSET + 32].copy_from_slice(seed);
        Self {
            buffer: upload(&host, stream),
        }
    }

    fn slice(&mut self) -> &mut era_cudart::slice::DeviceSlice<u8> {
        &mut self.buffer[SEED_OFFSET..SEED_OFFSET + 32]
    }

    fn read(&self, stream: &CudaStream) -> Seed {
        let host = download(&self.buffer, 0, stream);
        assert!(host[..SEED_OFFSET].iter().all(|b| *b == GUARD));
        assert!(host[SEED_OFFSET + 32..].iter().all(|b| *b == GUARD));
        host[SEED_OFFSET..SEED_OFFSET + 32].try_into().unwrap()
    }
}

fn random_words(rng: &mut TestRng, count: usize) -> Vec<u32> {
    (0..count).map(|_| rng.next_u64() as u32).collect()
}

fn random_fields(rng: &mut TestRng, count: usize) -> Vec<Proth120> {
    (0..count)
        .map(|i| match i % 5 {
            1 => Proth120::new(EDGE_VALUES[(i / 5) % EDGE_VALUES.len()]),
            _ => rng.field(),
        })
        .collect()
}

#[test]
fn keccak256_transcript_sequence_parity() {
    let stream = CudaStream::default();
    let mut rng = TestRng::new(0x7365_7175);
    let mut device = DeviceSeed::new(&[0; 32], &stream);
    let caps: Vec<Vec<Digest>> = (0..3)
        .map(|_| {
            (0..8)
                .map(|_| std::array::from_fn(|_| rng.next_u64() as u32))
                .collect()
        })
        .collect();
    let mut initial = random_words(&mut rng, 35);
    for cap in &caps[..2] {
        MerkleTreeCapVarLength { cap: cap.clone() }.add_into_buffer(&mut initial);
    }
    assert_eq!(initial.len(), 163);
    let input = upload(&initial, &stream);
    transcript_commit_initial_u32(&input, device.slice(), &stream).unwrap();
    let mut host = <HostTranscript as Transcript<Proth120, Proth120>>::commit_initial_u32(&initial);
    assert_eq!(device.read(&stream), host.0, "initial");
    let draw_fields =
        |count: usize, device: &mut DeviceSeed, host: &mut Keccak256Seed, step: &str| {
            let mut out = upload(&vec![Proth120::new(0); count], &stream);
            transcript_draw_fields(device.slice(), &mut out, &stream).unwrap();
            let gpu = download(&out, Proth120::new(0), &stream);
            let mut expected = vec![Proth120::new(0); count];
            <HostTranscript as Transcript<Proth120, Proth120>>::draw_random_field_elements(
                host,
                &mut expected,
            );
            assert_eq!(gpu, expected, "{step}");
            assert_eq!(device.read(&stream), host.0, "{step} seed");
        };
    draw_fields(9, &mut device, &mut host, "draw 9 fields");
    for (count, step) in [(4usize, "commit 4 fields"), (3, "commit 3 fields")] {
        let fields = random_fields(&mut rng, count);
        let input = upload(&fields, &stream);
        transcript_commit_fields(device.slice(), &input, &stream).unwrap();
        <HostTranscript as Transcript<Proth120, Proth120>>::commit_base_field_elements(
            &mut host, &fields,
        );
        assert_eq!(device.read(&stream), host.0, "{step}");
    }
    let mut cap_words = Vec::new();
    MerkleTreeCapVarLength {
        cap: caps[2].clone(),
    }
    .add_into_buffer(&mut cap_words);
    let device_cap = upload(&caps[2], &stream);
    transcript_commit_u32(
        device.slice(),
        unsafe { device_cap.transmute::<u32>() },
        &stream,
    )
    .unwrap();
    <HostTranscript as Transcript<Proth120, Proth120>>::commit_u32_with_seed(&mut host, &cap_words);
    assert_eq!(device.read(&stream), host.0, "commit cap");
    draw_fields(1, &mut device, &mut host, "draw 1 field");
    let mut out = upload(&[0u32; 24], &stream);
    transcript_draw_u32(device.slice(), &mut out, &stream).unwrap();
    let gpu = download(&out, 0, &stream);
    let mut expected = [0u32; 24];
    <HostTranscript as Transcript<Proth120, Proth120>>::draw_randomness(&mut host, &mut expected);
    assert_eq!(gpu, expected, "draw 24 words");
    assert_eq!(device.read(&stream), host.0, "draw 24 words seed");
    draw_fields(1, &mut device, &mut host, "final draw 1 field");
}
