use std::borrow::Cow;

use riscv_transpiler::ir::preprocess_bytecode;
use riscv_transpiler::ir::Instruction;

use crate::rv32im::types::DecoderConfig;

pub struct Binary<'d> {
    data: Cow<'d, [u8]>,
    text: Option<Cow<'d, [u8]>>,
}

impl<'d> Binary<'d> {
    pub fn new(data: &'d [u8], text: Option<&'d [u8]>) -> Self {
        if let Some(text) = text {
            assert_text_is_beginning_of_data(data, text);
        }
        let data = align(data);
        let text = text.map(align);
        Self { data, text }
    }

    pub fn data(&self) -> &[u8] {
        self.data.as_ref()
    }

    pub fn text(&self) -> Option<&[u8]> {
        self.text.as_deref()
    }

    pub fn data_chunks(&self) -> Vec<u32> {
        into_chunks(self.data())
    }

    pub fn text_chunks(&self) -> Option<Vec<u32>> {
        self.text().map(into_chunks)
    }

    pub fn instructions(&self) -> Vec<Instruction> {
        let chunks = self.text_chunks().unwrap_or_else(|| self.data_chunks());
        preprocess_bytecode::<DecoderConfig>(&chunks)
    }
}

fn align<'d>(data: &'d [u8]) -> Cow<'d, [u8]> {
    let mult = data.len().next_multiple_of(4);

    if mult != data.len() {
        // Pad the data with 0 to keep alignment.
        let mut vec = Vec::with_capacity(mult);
        vec.extend_from_slice(data);
        vec.extend(std::iter::repeat_n(0u8, mult - data.len()));
        assert_eq!(vec.len() % 4, 0);
        Cow::Owned(vec)
    } else {
        Cow::Borrowed(data)
    }
}

fn assert_text_is_beginning_of_data(data: &[u8], text: &[u8]) {
    assert!(data.len() >= text.len());
    assert_eq!(&data[0..text.len()], text);
}

fn into_chunks(data: &[u8]) -> Vec<u32> {
    let (chunks, tail) = data.as_chunks::<4>();
    assert_eq!(tail.len(), 0);
    chunks.iter().copied().map(u32::from_le_bytes).collect()
}
