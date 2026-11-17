// Shared by the native producer and the static-input Miri tests.
#![allow(dead_code)]
use verifier::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use verifier::field::{FieldExtension, PrimeField};
use verifier::verifier_common::{self, errors::DebugErrorCreator, VerifierOutput};

fn push_ext(words: &mut Vec<u32>, value: BabyBearExt4) {
    words.extend(
        <BabyBearExt4 as FieldExtension<BabyBearField>>::into_coeffs(value)
            .map(|f| f.as_u32_reduced()),
    );
}

fn flatten_output<const IT: usize, const CAP: usize, const MEMORY: usize, const SETUPS: usize>(
    output: VerifierOutput<BabyBearExt4, IT, CAP, MEMORY, SETUPS>,
) -> Vec<u32> {
    let mut words = Vec::new();
    words.extend(output.inits_and_teardowns_top_bits);
    words.extend(output.memory_caps.into_iter().flatten().flatten());
    words.extend(output.setup_caps.into_iter().flatten().flatten());
    push_ext(&mut words, output.grand_product_read_set_accumulator);
    push_ext(&mut words, output.grand_product_write_set_accumulator);
    words.push(u32::from(output.inits_and_teardowns.is_some()));
    if let Some(products) = output.inits_and_teardowns {
        push_ext(&mut words, products.read_product);
        push_ext(&mut words, products.write_product);
    }
    words
}

pub fn verify(
    name: &str,
    mode: u32,
    payload: &mut (impl Iterator<Item = u32> + Send + Sync),
) -> Vec<u32> {
    let challenges =
        verifier_common::read_external_challenges::<BabyBearField, BabyBearExt4, _>(payload);
    macro_rules! dispatch {
        ($($name:ident; $path:expr),* $(,)?) => {
            match (name, mode) {
                $((stringify!($name), 0) => flatten_output(
                    verifier::$name::pessimistic_conjecture::verify::<_, DebugErrorCreator>(
                        &challenges, payload,
                    ).expect("canonical circuit verification failed"),
                ),
                (stringify!($name), 1) => flatten_output(
                    verifier::$name::ethproofs_soundcalc::verify::<_, DebugErrorCreator>(
                        &challenges, payload,
                    ).expect("canonical circuit verification failed"),
                ),)*
                _ => panic!("unknown canonical circuit/mode: {name}/{mode}"),
            }
        };
    }
    #[cfg(feature = "miri_compression")]
    let output = if name == "compression" {
        assert_eq!(mode, 0, "compression is pessimistic only");
        flatten_output(
            verifier::compression::verify::<_, DebugErrorCreator>(&challenges, payload)
                .expect("final compression circuit verification failed"),
        )
    } else {
        verifier_common::gkr_fixture_circuits!(dispatch)
    };
    #[cfg(not(feature = "miri_compression"))]
    let output = verifier_common::gkr_fixture_circuits!(dispatch);
    assert!(
        payload.next().is_none(),
        "generated verifier left input words"
    );
    output
}

pub fn encode(expected: &[u32], payload: &[u32]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(4 * (1 + expected.len() + payload.len()));
    let expected_len = u32::try_from(expected.len()).unwrap();
    for word in core::iter::once(&expected_len)
        .chain(expected)
        .chain(payload)
    {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    bytes
}

pub fn decode(input: &[u8]) -> (Vec<u32>, impl Iterator<Item = u32> + '_) {
    let (bytes, tail) = input.as_chunks::<4>();
    assert!(tail.is_empty(), "partial static input word");
    let mut words = bytes.iter().map(|b| u32::from_le_bytes(*b));
    let expected_len = words.next().expect("output length") as usize;
    assert!(bytes.len() > expected_len, "missing output words");
    let expected = words.by_ref().take(expected_len).collect();
    (expected, words)
}

pub fn check(name: &str, mode: u32, input: &[u8]) {
    let (expected, mut payload) = decode(input);
    let actual = verify(name, mode, &mut payload);
    assert_eq!(actual, expected, "native/generated verifier outputs differ");
}
