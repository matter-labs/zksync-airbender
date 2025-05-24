use crate::definitions::TIMESTAMP_COLUMNS_NUM_BITS;

pub const WORD_SIZE: usize = core::mem::size_of::<u32>();

pub fn setbits(x: u8) -> u32 {
    u32::MAX >> (32 - x)
}

pub fn sign_extend(x: i32, bits: u32) -> i32 {
    let remain = WORD_SIZE as u32 * 8 - bits;
    x.wrapping_shl(remain).wrapping_shr(remain)
}

pub fn sign_extend_u32(x: u32) -> i64 {
    (x as i32) as i64
}

pub fn round_up(x: usize, factor: usize) -> usize {
    let rem = x % factor;
    if rem > 0 {
        x + factor - rem
    } else {
        x
    }
}

pub fn log2_n(n: usize) -> usize {
    debug_assert!(n.is_power_of_two());
    let res = n.trailing_zeros();
    res as usize
}

pub fn u64_from_lsb_bits(bits: &[bool]) -> u64 {
    let mut result = 0u64;
    for (shift, bit) in bits.iter().enumerate() {
        result |= (*bit as u64) << shift;
    }

    result
}

pub use crate::definitions::split_timestamp;

pub fn split_u32_into_pair_u16(num: u32) -> (u16, u16) {
    let high_word = (num >> 16) as u16;
    let low_word = (num & 0xffff) as u16;
    (low_word, high_word)
}

pub fn u32_split_sub(a: u32, b: u32) -> (((u16, u16), bool), bool) {
    let (a_low, a_high) = split_u32_into_pair_u16(a);
    let (b_low, b_high) = split_u32_into_pair_u16(b);
    let (low, intermediate_borrow) = a_low.overflowing_sub(b_low);

    let (t, of0) = a_high.overflowing_sub(b_high);
    let (high, of1) = t.overflowing_sub(intermediate_borrow as u16);

    let final_borrow = of0 || of1;

    (((low, high), intermediate_borrow), final_borrow)
}

pub fn timestamp_sub(a: (u32, u32), b: (u32, u32)) -> (((u32, u32), bool), bool) {
    // a - b, but we are interested in the intermediate borrow
    let t = (1 << TIMESTAMP_COLUMNS_NUM_BITS) + a.0 - b.0;
    let intermediate_borrow = t < (1 << TIMESTAMP_COLUMNS_NUM_BITS);
    let low = t & ((1 << TIMESTAMP_COLUMNS_NUM_BITS) - 1);
    // same for high
    let t = (1 << TIMESTAMP_COLUMNS_NUM_BITS) + a.1 - b.1 - (intermediate_borrow as u32);
    let final_borrow = t < (1 << TIMESTAMP_COLUMNS_NUM_BITS);
    let high = t & ((1 << TIMESTAMP_COLUMNS_NUM_BITS) - 1);

    (((low, high), intermediate_borrow), final_borrow)
}

pub fn bitreverse_for_bitlength(num: usize, bitlength: usize) -> usize {
    let shift = std::mem::size_of::<usize>() * 8 - bitlength;
    num.reverse_bits() >> shift
}

#[derive(Clone, Debug)]
pub struct LSBIterator<'a> {
    over: &'a [u64],
    n: usize,
}

impl<'a> LSBIterator<'a> {
    pub const fn new(source: &'a [u64]) -> Self {
        Self { over: source, n: 0 }
    }
}

impl<'a> Iterator for LSBIterator<'a> {
    type Item = bool;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.n >= self.over.len() * 64 {
            return None;
        }

        let word_idx = self.n / 64;
        let bit_idx = self.n % 64;

        self.n += 1;

        Some(self.over[word_idx] & (1u64 << bit_idx) != 0)
    }
}

impl<'a> ExactSizeIterator for LSBIterator<'a> {
    fn len(&self) -> usize {
        self.over.len() * 64 - self.n
    }
}

pub struct Multizip<T>(pub Vec<T>);

impl<T> Multizip<T> {
    pub fn new(data: Vec<T>) -> Self {
        Multizip(data)
    }
}

impl<T> Iterator for Multizip<T>
where
    T: Iterator,
{
    type Item = Vec<T::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.iter_mut().map(Iterator::next).collect()
    }
}

impl<T> Multizip<&mut [T]> {
    pub fn get_row_slice(&mut self, idx: usize) -> Vec<&mut T> {
        self.0.iter_mut().map(|slice| &mut slice[idx]).collect()
    }
}

pub trait IdentifyFirstLast: Iterator + Sized {
    fn identify_first_last(self) -> Iter<Self>;
}

impl<I> IdentifyFirstLast for I
where
    I: Iterator,
{
    fn identify_first_last(self) -> Iter<Self> {
        Iter(true, self.peekable())
    }
}

pub struct Iter<I>(bool, std::iter::Peekable<I>)
where
    I: Iterator;

impl<I> Iterator for Iter<I>
where
    I: Iterator,
{
    type Item = (bool, bool, I::Item);

    fn next(&mut self) -> Option<Self::Item> {
        let first = std::mem::replace(&mut self.0, false);
        self.1.next().map(|e| (first, self.1.peek().is_none(), e))
    }
}

#[allow(dead_code)]
pub(crate) fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

#[allow(dead_code)]
pub(crate) fn bincode_serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    bincode::serialize_into(&mut dst, el).unwrap();
}
