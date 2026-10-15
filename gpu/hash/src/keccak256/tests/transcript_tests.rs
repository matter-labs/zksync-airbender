use era_cudart::memory::DeviceAllocation;
use era_cudart::stream::CudaStream;
use sha3::{Digest as _, Keccak256};

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

fn random_seed(rng: &mut TestRng) -> Seed {
    std::array::from_fn(|_| rng.next_u64() as u8)
}

fn gpu_commit_u32(seed: &Seed, words: &[u32], stream: &CudaStream) -> Seed {
    let mut device = DeviceSeed::new(seed, stream);
    let input = upload(words, stream);
    transcript_commit_u32(device.slice(), &input, stream).unwrap();
    device.read(stream)
}

fn gpu_commit_fields(seed: &Seed, fields: &[Proth120], stream: &CudaStream) -> Seed {
    let mut device = DeviceSeed::new(seed, stream);
    let input = upload(fields, stream);
    transcript_commit_fields(device.slice(), &input, stream).unwrap();
    device.read(stream)
}

fn host_commit_u32(seed: &Seed, words: &[u32]) -> Seed {
    let mut seed = Keccak256Seed(*seed);
    <HostTranscript as Transcript<Proth120, Proth120>>::commit_u32_with_seed(&mut seed, words);
    seed.0
}

fn host_commit_fields(seed: &Seed, fields: &[Proth120]) -> Seed {
    let mut base = Keccak256Seed(*seed);
    <HostTranscript as Transcript<Proth120, Proth120>>::commit_base_field_elements(
        &mut base, fields,
    );
    let mut extension = Keccak256Seed(*seed);
    <HostTranscript as Transcript<Proth120, Proth120>>::commit_extension_field_elements(
        &mut extension,
        fields,
    );
    assert_eq!(base, extension);
    base.0
}

#[test]
fn keccak256_transcript_absorb_parity() {
    let stream = CudaStream::default();
    let mut rng = TestRng::new(0x6162_736f);
    let word_counts = [0usize, 1, 8, 9, 25, 26, 27, 33, 34, 35, 64, 67, 68, 69, 163];
    for count in word_counts {
        let words = random_words(&mut rng, count);
        let mut device = DeviceSeed::new(&[0xa5; 32], &stream);
        let input = upload(&words, &stream);
        transcript_commit_initial_u32(&input, device.slice(), &stream).unwrap();
        let expected =
            <HostTranscript as Transcript<Proth120, Proth120>>::commit_initial_u32(&words);
        assert_eq!(device.read(&stream), expected.0, "initial count={count}");
        let seed = random_seed(&mut rng);
        assert_eq!(
            gpu_commit_u32(&seed, &words, &stream),
            host_commit_u32(&seed, &words),
            "seeded count={count}"
        );
    }
    for count in [0usize, 1, 3, 4, 6, 7, 8, 14, 15, 16, 17, 28] {
        let fields = random_fields(&mut rng, count);
        let seed = random_seed(&mut rng);
        assert_eq!(
            gpu_commit_fields(&seed, &fields, &stream),
            host_commit_fields(&seed, &fields),
            "fields count={count}"
        );
    }
    let cap: Vec<Digest> = (0..8)
        .map(|_| std::array::from_fn(|_| rng.next_u64() as u32))
        .collect();
    let seed = random_seed(&mut rng);
    let device_cap = upload(&cap, &stream);
    let mut device = DeviceSeed::new(&seed, &stream);
    transcript_commit_u32(
        device.slice(),
        unsafe { device_cap.transmute::<u32>() },
        &stream,
    )
    .unwrap();
    let gpu = device.read(&stream);
    let mut words = Vec::new();
    MerkleTreeCapVarLength { cap: cap.clone() }.add_into_buffer(&mut words);
    assert_eq!(words.len(), 64);
    assert_eq!(gpu, host_commit_u32(&seed, &words), "cap");
    let mut raw = seed.to_vec();
    for digest in cap.iter() {
        for word in digest {
            raw.extend_from_slice(&word.to_be_bytes());
        }
    }
    let raw_digest: Seed = Keccak256::digest(&raw).into();
    assert_ne!(gpu, raw_digest, "cap words must be absorbed little-endian");
}

#[test]
fn keccak256_transcript_draw_parity() {
    let stream = CudaStream::default();
    let mut rng = TestRng::new(0x6472_6177);
    for count in [0usize, 1, 7, 8, 9, 16, 17, 24] {
        let seed = random_seed(&mut rng);
        let mut device = DeviceSeed::new(&seed, &stream);
        let mut out = upload(&vec![0xdead_beefu32; count + 2], &stream);
        transcript_draw_u32(device.slice(), &mut out[..count], &stream).unwrap();
        let gpu = download(&out, 0, &stream);
        let mut host_seed = Keccak256Seed(seed);
        let mut expected = vec![0u32; count];
        <HostTranscript as Transcript<Proth120, Proth120>>::draw_randomness(
            &mut host_seed,
            &mut expected,
        );
        assert_eq!(&gpu[..count], &expected[..], "u32 count={count}");
        assert_eq!(&gpu[count..], &[0xdead_beef; 2], "u32 count={count}");
        assert_eq!(device.read(&stream), host_seed.0, "u32 seed count={count}");
    }
    for count in [0usize, 1, 2, 9] {
        let seed = random_seed(&mut rng);
        let mut device = DeviceSeed::new(&seed, &stream);
        let mut out = upload(&vec![Proth120::new(7); count + 1], &stream);
        transcript_draw_fields(device.slice(), &mut out[..count], &stream).unwrap();
        let gpu = download(&out, Proth120::new(0), &stream);
        let mut host_seed = Keccak256Seed(seed);
        let mut expected = vec![Proth120::new(0); count];
        <HostTranscript as Transcript<Proth120, Proth120>>::draw_random_field_elements(
            &mut host_seed,
            &mut expected,
        );
        assert_eq!(&gpu[..count], &expected[..], "fields count={count}");
        assert_eq!(gpu[count], Proth120::new(7), "fields count={count}");
        assert_eq!(
            device.read(&stream),
            host_seed.0,
            "fields seed count={count}"
        );
    }
    let seed = random_seed(&mut rng);
    let mut device = DeviceSeed::new(&seed, &stream);
    let mut out = upload(&[Proth120::new(0); 2], &stream);
    transcript_draw_fields(device.slice(), &mut out[..1], &stream).unwrap();
    transcript_draw_fields(device.slice(), &mut out[1..], &stream).unwrap();
    let gpu = download(&out, Proth120::new(0), &stream);
    let mut host_seed = Keccak256Seed(seed);
    let mut expected = [Proth120::new(0); 2];
    <HostTranscript as Transcript<Proth120, Proth120>>::draw_random_field_elements(
        &mut host_seed,
        &mut expected,
    );
    assert_eq!(gpu, expected, "draw1 twice == draw2");
    assert_eq!(device.read(&stream), host_seed.0);
    let mut device = DeviceSeed::new(&seed, &stream);
    let mut out = upload(&[0u32; 8], &stream);
    transcript_draw_u32(device.slice(), &mut out[..4], &stream).unwrap();
    transcript_draw_u32(device.slice(), &mut out[4..], &stream).unwrap();
    let gpu = download(&out, 0, &stream);
    let mut host_seed = Keccak256Seed(seed);
    let mut expected = [0u32; 8];
    for half in expected.chunks_mut(4) {
        <HostTranscript as Transcript<Proth120, Proth120>>::draw_randomness(&mut host_seed, half);
    }
    assert_eq!(gpu, expected, "two draw_u32(4) calls");
    assert_eq!(device.read(&stream), host_seed.0);
    let mut single = [0u32; 8];
    let mut single_seed = Keccak256Seed(seed);
    <HostTranscript as Transcript<Proth120, Proth120>>::draw_randomness(
        &mut single_seed,
        &mut single,
    );
    assert_ne!(gpu, single, "no cursor across calls");
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
