use rand::Rng;

#[test]
fn test_memcopy() {
    const MAX_SIZE: usize = 1024;
    let mut rng = rand::rng();

    let mut input = vec![0u8; 2 * MAX_SIZE];
    for i in 0..2 * MAX_SIZE {
        input[i] = rng.random();
    }

    for size in 0..MAX_SIZE {
        for src_unalignment in 0..4 {
            for dst_unalignment in 0..4 {
                let mut output_buffer = vec![0u8; 2 * MAX_SIZE];

                let src_offset = 4 - (input[..].as_ptr().addr() % 4);
                let src_offset = src_offset % 4;
                let src_offset = src_offset + src_unalignment;

                let dst_offset = 4 - (output_buffer[..].as_ptr().addr() % 4);
                let dst_offset = dst_offset % 4;
                let dst_offset = dst_offset + dst_unalignment;

                let source = &input[src_offset..][..size];
                let output = &mut output_buffer[dst_offset..][..size];

                assert_eq!(source[..].as_ptr().addr() % 4, src_unalignment);
                assert_eq!(output[..].as_ptr().addr() % 4, dst_unalignment);

                // if size == 2 && src_unalignment == 0 && dst_unalignment == 0 {
                //     println!("DEBUG");
                // }

                let ret_value = unsafe {
                    crate::memcpy::memcpy_impl(output.as_mut_ptr(), source.as_ptr(), size)
                };

                assert_eq!(ret_value, output[..].as_mut_ptr());

                if source != output {
                    // dbg!(source);
                    // dbg!(output);
                    panic!(
                        "Failed for size {}, with source unalignmnet {}, dest unalignment {}",
                        size, src_unalignment, dst_unalignment
                    );
                }

                if output_buffer[..dst_offset].iter().all(|el| *el == 0) == false {
                    // dbg!(&output_buffer[..dst_offset]);
                    panic!(
                        "Failed for size {}, with source unalignmnet {}, dest unalignment {}: output before destination is touched",
                        size, src_unalignment, dst_unalignment
                    );
                }

                if output_buffer[dst_offset..][size..]
                    .iter()
                    .all(|el| *el == 0)
                    == false
                {
                    // dbg!(&output_buffer[dst_offset..][size..]);
                    panic!(
                        "Failed for size {}, with source unalignmnet {}, dest unalignment {}: output after destination is touched",
                        size, src_unalignment, dst_unalignment
                    );
                }
            }
        }
    }
}
