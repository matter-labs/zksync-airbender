use common_constants::{L1_WRAP_ROM, REGULAR_ROM};
use setups::{
    pad_bytecode_bytes_for_proving, pad_bytecode_bytes_for_proving_with_rom,
    pad_bytecode_for_proving, pad_bytecode_for_proving_with_rom,
};

#[test]
fn padding_preserves_image_and_uses_selected_rom() {
    for rom in [REGULAR_ROM, L1_WRAP_ROM] {
        let mut bytes = vec![1, 2, 3];
        pad_bytecode_bytes_for_proving_with_rom(&mut bytes, rom);
        assert_eq!(bytes.len(), rom.byte_size());
        assert_eq!(&bytes[..3], &[1, 2, 3]);
        assert!(bytes[3..].iter().all(|&byte| byte == 0));
        let mut words = vec![0x01020304];
        pad_bytecode_for_proving_with_rom(&mut words, rom);
        assert_eq!(words.len(), rom.word_size());
        assert_eq!(words[0], 0x01020304);
        assert!(words[1..].iter().all(|&word| word == 0));
        pad_bytecode_bytes_for_proving_with_rom(&mut bytes, rom);
        pad_bytecode_for_proving_with_rom(&mut words, rom);
    }
}

#[test]
fn legacy_padding_is_regular_rom_padding() {
    let mut bytes = vec![7];
    let mut words = vec![7];
    pad_bytecode_bytes_for_proving(&mut bytes);
    pad_bytecode_for_proving(&mut words);
    assert_eq!(bytes.len(), REGULAR_ROM.byte_size());
    assert_eq!(words.len(), REGULAR_ROM.word_size());
}

#[test]
fn oversized_images_are_rejected_without_truncation() {
    for rom in [REGULAR_ROM, L1_WRAP_ROM] {
        let mut bytes = vec![7; rom.byte_size() + 1];
        let mut words = vec![7; rom.word_size() + 1];
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            pad_bytecode_bytes_for_proving_with_rom(&mut bytes, rom);
        }))
        .is_err());
        assert_eq!(bytes.len(), rom.byte_size() + 1);
        assert!(bytes.iter().all(|&byte| byte == 7));
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            pad_bytecode_for_proving_with_rom(&mut words, rom);
        }))
        .is_err());
        assert_eq!(words.len(), rom.word_size() + 1);
        assert!(words.iter().all(|&word| word == 7));
    }
}

#[test]
fn regular_padded_image_cannot_be_reinterpreted_as_wrap() {
    let mut bytes = vec![1];
    let mut words = vec![1];
    pad_bytecode_bytes_for_proving(&mut bytes);
    pad_bytecode_for_proving(&mut words);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        pad_bytecode_bytes_for_proving_with_rom(&mut bytes, L1_WRAP_ROM);
    }))
    .is_err());
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        pad_bytecode_for_proving_with_rom(&mut words, L1_WRAP_ROM);
    }))
    .is_err());
}
