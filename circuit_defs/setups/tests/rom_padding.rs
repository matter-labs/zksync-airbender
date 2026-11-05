use common_constants::rom::L1_WRAP_ROM;
use setups::pad_bytecode_for_proving_with_rom;

#[test]
fn oversized_wrap_image_is_rejected_without_truncation() {
    let mut words = vec![7; L1_WRAP_ROM.word_size() + 1];
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        pad_bytecode_for_proving_with_rom(&mut words, L1_WRAP_ROM);
    }))
    .is_err());
    assert_eq!(words, vec![7; L1_WRAP_ROM.word_size() + 1]);
}
