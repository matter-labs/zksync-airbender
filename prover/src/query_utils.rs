pub struct BitSource {
    u32_values: Vec<u32>,
    index: usize,
}

impl BitSource {
    pub fn new(u32_values: Vec<u32>) -> Self {
        Self {
            u32_values,
            index: 0,
        }
    }
}

impl Iterator for BitSource {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.u32_values.len() * (u32::BITS as usize) {
            return None;
        }

        let word_index = self.index / (u32::BITS as usize);
        let bit_index = self.index % (u32::BITS as usize);
        let bit = self.u32_values[word_index] & (1 << bit_index) != 0;
        self.index += 1;

        Some(bit)
    }
}

pub fn assemble_query_index(num_bits: usize, bit_source: &mut impl Iterator<Item = bool>) -> usize {
    // assemble as LE
    assert!(num_bits <= usize::BITS as usize);
    let mut result = 0usize;
    for i in 0..num_bits {
        result |= (bit_source.next().expect("must have enough bits") as usize) << i;
    }

    result
}
