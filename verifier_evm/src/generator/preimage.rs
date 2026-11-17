//! Transcript preimage shared by the decoder, template constants and layout documentation.

use super::{Lit, NUM_REGISTERS, PREIMAGE_FINAL_PC_TS_BYTES, PREIMAGE_REGISTER_STRIDE};

pub(super) struct PreimageLayout {
    pub final_pc: Lit,
    pub timestamp_low: Lit,
    pub timestamp_high: Lit,
    pub top_bits: Lit,
    pub top_bits_bytes: Lit,
    pub setup_cap: Lit,
    pub memory_cap: Lit,
    pub cap_bytes: Lit,
    pub wire_cap_bytes: Lit,
    pub total: Lit,
}

impl PreimageLayout {
    pub fn new(top_bits_count: usize, cap: usize, wire_digest_bytes: usize) -> Self {
        // The transcript image uses eight LE u32s per digest; compressed calldata carries
        // wire_digest_bytes per digest. The decoder expands them into full image words.
        let final_pc =
            Lit::num(NUM_REGISTERS as u128).mul(&Lit::num(PREIMAGE_REGISTER_STRIDE as u128));
        let timestamp_low = final_pc.add(&Lit::num(4));
        let timestamp_high = final_pc.add(&Lit::num(8));
        let top_bits = final_pc.add(&Lit::num(PREIMAGE_FINAL_PC_TS_BYTES as u128));
        let top_bits_bytes = Lit::num(4).mul(&Lit::num(top_bits_count as u128));
        let setup_cap = top_bits.add(&top_bits_bytes);
        let cap_bytes = Lit::num(cap as u128).mul(&Lit::num(8)).mul(&Lit::num(4));
        let memory_cap = setup_cap.add(&cap_bytes);
        let total = memory_cap.add(&cap_bytes);
        Self {
            final_pc,
            timestamp_low,
            timestamp_high,
            top_bits,
            top_bits_bytes,
            setup_cap,
            memory_cap,
            cap_bytes,
            wire_cap_bytes: Lit::num(cap as u128).mul(&Lit::num(wire_digest_bytes as u128)),
            total,
        }
    }

    pub fn constants(&self) -> [(&'static str, &Lit); 9] {
        [
            ("__TEMPLATE_PREIMAGE_FINAL_PC_OFFSET", &self.final_pc),
            (
                "__TEMPLATE_PREIMAGE_TIMESTAMP_LOW_OFFSET",
                &self.timestamp_low,
            ),
            (
                "__TEMPLATE_PREIMAGE_TIMESTAMP_HIGH_OFFSET",
                &self.timestamp_high,
            ),
            ("__TEMPLATE_PREIMAGE_TOP_BITS_OFFSET", &self.top_bits),
            ("__TEMPLATE_PREIMAGE_TOP_BITS_BYTES", &self.top_bits_bytes),
            ("__TEMPLATE_PREIMAGE_SETUP_CAP_OFFSET", &self.setup_cap),
            ("__TEMPLATE_PREIMAGE_MEMORY_CAP_OFFSET", &self.memory_cap),
            ("__TEMPLATE_PREIMAGE_CAP_BYTES", &self.cap_bytes),
            ("__TEMPLATE_GKR_INIT_PREIMAGE_BYTES", &self.total),
        ]
    }

    pub fn markdown(&self, image_start: u128) -> String {
        use std::fmt::Write;
        let mut out = String::from("\n## Transcript preimage in IMAGE\n\n`decode_calldata()` builds this prefix of IMAGE before `transcript_init(IMAGE_PTR())` hashes it. Registers, timestamps and the memory cap come from calldata; final PC and top bits are pinned, and the setup cap is copied from the appended setup with `codecopy`. The digest image is eight LE u32s per cap entry; calldata uses the compressed digest width. Offsets are relative to IMAGE.\n\n| Field | Offset (decimal / hex) | Size (decimal / hex) | End (decimal / hex) |\n| --- | ---: | ---: | ---: |\n");
        for (name, offset, size) in [
            (
                "Registers (value, timestamp low, timestamp high)",
                0,
                self.final_pc.value,
            ),
            ("Final PC", self.final_pc.value, 4),
            ("Final timestamp low", self.timestamp_low.value, 4),
            ("Final timestamp high", self.timestamp_high.value, 4),
            (
                "Inits/teardowns top bits",
                self.top_bits.value,
                self.top_bits_bytes.value,
            ),
            (
                "Setup cap (from code)",
                self.setup_cap.value,
                self.cap_bytes.value,
            ),
            (
                "Memory cap (from calldata)",
                self.memory_cap.value,
                self.cap_bytes.value,
            ),
        ] {
            let end = offset + size;
            writeln!(
                out,
                "| {name} | {offset} / `{offset:#x}` | {size} / `{size:#x}` | {end} / `{end:#x}` |"
            )
            .unwrap();
        }
        let total = self.total.value;
        let end = image_start + total;
        writeln!(out, "\nPreimage length: {total} / `{total:#x}` bytes (`__TEMPLATE_GKR_INIT_PREIMAGE_BYTES`), checked against the decoder layout. Absolute range: {image_start} / `{image_start:#x}` .. {end} / `{end:#x}`.\n").unwrap();
        out
    }
}
