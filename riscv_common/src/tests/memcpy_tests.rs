use rand::Rng;

#[test]
fn test_memcopy() {
    const MAX_SIZE: usize = 1024;
    let mut rng = rand::rng();

    for size in 0..MAX_SIZE {
        let mut input = vec![0u8; 2 * MAX_SIZE];

        for i in 0..MAX_SIZE {
            input[i] = rng.random();
        }

        for src_unalignment in 0..4 {
            for dst_unalignment in 0..4 {
                let mut output = vec![0u8; 2 * MAX_SIZE];

                let src_offset = 4 - (input[..].as_ptr().addr() % 4);
                let src_offset = src_offset % 4;
                let src_offset = src_offset + src_unalignment;

                let dst_offset = 4 - (output[..].as_ptr().addr() % 4);
                let dst_offset = dst_offset % 4;
                let dst_offset = dst_offset + dst_unalignment;

                let source = &input[src_offset..][..size];
                let output = &mut output[dst_offset..][..size];

                assert_eq!(source[..].as_ptr().addr() % 4, src_unalignment);
                assert_eq!(output[..].as_ptr().addr() % 4, dst_unalignment);

                let ret_value = unsafe {
                    crate::memcpy::memcpy_impl(output.as_mut_ptr(), source.as_ptr(), size)
                };

                assert_eq!(ret_value, output[..].as_mut_ptr());

                if source != output {
                    dbg!(source);
                    dbg!(output);
                    panic!(
                        "Failed for size {}, with source unalignmnet {}, dest unalignment {}",
                        size, src_unalignment, dst_unalignment
                    );
                }
            }
        }
    }
}
