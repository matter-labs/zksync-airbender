pub struct BitSource<'a> {
    u32_values: &'a [u32],
    index: usize,
}

impl<'a> BitSource<'a> {
    pub fn new(u32_values: &'a [u32]) -> Self {
        Self {
            u32_values,
            index: 0,
        }
    }
}

impl<'a> Iterator for BitSource<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.u32_values.len() * (u32::BITS as usize) {
            return None;
        }

        let word_index = self.index / (u32::BITS as usize);
        let bit_index = self.index % (u32::BITS as usize);
        // Use read_volatile to force a full 32-bit load and prevent the
        // compiler from optimizing into a subword (lhu/lbu) load, which
        // the reduced RISC-V transpiler does not support.
        let word = unsafe { core::ptr::read_volatile(&self.u32_values[word_index]) };
        let bit = (word >> bit_index) & 1;
        self.index += 1;

        Some(bit as usize)
    }
}

pub fn assemble_query_index(
    num_bits: usize,
    bit_source: &mut impl Iterator<Item = usize>,
) -> usize {
    // assemble as LE
    debug_assert!(num_bits <= usize::BITS as usize);
    let mut result = 0usize;
    for i in 0..num_bits {
        result |= unsafe { bit_source.next().unwrap_unchecked() } << i;
    }

    result
}

pub fn bitreverse_for_bitlength(num: u32, bitlength: u32) -> u32 {
    let shift = u32::BITS - bitlength;
    num.reverse_bits() >> shift
}
