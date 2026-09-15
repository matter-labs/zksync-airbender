use rand::Rng;

#[test]
fn test_memset() {
    const MAX_SIZE: usize = 1024;
    let mut rng = rand::rng();

    let mut input = vec![0u8; 2 * MAX_SIZE];
    for i in 0..2 * MAX_SIZE {
        input[i] = rng.random();
    }

    let fill_value = 0xffu8 as u32;

    for size in 0..MAX_SIZE {
        for dst_unalignment in 0..4 {
            let mut output_buffer = input.clone();

            let dst_offset = 4 - (output_buffer[..].as_ptr().addr() % 4);
            let dst_offset = dst_offset % 4;
            let dst_offset = dst_offset + dst_unalignment;

            let output = &mut output_buffer[dst_offset..][..size];

            assert_eq!(output[..].as_ptr().addr() % 4, dst_unalignment);

            let ret_value =
                unsafe { crate::memset::memset_impl(output.as_mut_ptr(), fill_value, size) };

            assert_eq!(ret_value, output[..].as_mut_ptr());

            if output.iter().all(|el| *el == fill_value as u8) == false {
                // dbg!(source);
                // dbg!(output);
                panic!(
                    "Failed for size {}, dest unalignment {}",
                    size, dst_unalignment
                );
            }

            if output_buffer[..dst_offset] != input[..dst_offset] {
                // dbg!(&output_buffer[..dst_offset]);
                panic!(
                    "Failed for size {}, dest unalignment {}: output before destination is touched",
                    size, dst_unalignment
                );
            }

            if output_buffer[dst_offset..][size..] != input[dst_offset..][size..] {
                // dbg!(&output_buffer[dst_offset..][size..]);
                panic!(
                    "Failed for size {}, dest unalignment {}: output after destination is touched",
                    size, dst_unalignment
                );
            }
        }
    }
}
