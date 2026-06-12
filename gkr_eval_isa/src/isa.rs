//! ISA types and 16-bit lane encoding (spec §5).

pub const NEG_ONE_U32: u32 = 2013265920; // BabyBear p - 1

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    SumK = 0,
    ProdK = 1,
    DotK = 2,
    /// Native op (GateK or CacheK — discriminated by the payload record).
    /// Carries a payload lane and an explicit operand-count lane.
    NativeK = 3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dst {
    /// bf-cell index into the smem slot file (e4 = 4 consecutive cells).
    Slot(u16),
    /// bf-cell index into the decode-selected fixed-register file.
    FixedReg(u16),
    /// Output slot index (original layer output order; native-stored slots
    /// are skipped, so indices may be sparse).
    Output(u16),
    /// Gate-input staging index — computed gate/cache input values handed to
    /// native gate logic (cone programs only; forward programs never use it).
    GateIn(u16),
    /// No interpreter-visible destination: a GateK's stores are native,
    /// driven by its payload. NativeK-only; shares dst-class code 3 with
    /// GateIn (disambiguated by op).
    Native,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operand {
    /// Staged post-fold value (Place column or native GateOutput); per-domain
    /// id namespaces — the e4 flag disambiguates (spec §9.8 decision).
    Source { id: u16, e4: bool },
    Slot { cell: u16, e4: bool },
    FixedReg { cell: u16, e4: bool },
    /// Index into the deduplicated bf constant table.
    Const { idx: u8 },
    Zero,
    One,
    NegOne,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Instr {
    pub op: Op,
    pub e4_result: bool,
    pub dst: Dst,
    /// SumK/ProdK: k operands. DotK: 2k operands, consecutive pairs.
    /// NativeK: canonical payload-shape operand lanes.
    pub operands: Vec<Operand>,
    /// NativeK only: index into the program's payload table.
    pub payload: Option<u16>,
}

/// Interpreter-facing payload metadata (the full IR records live in
/// `CompiledForward::payloads`; the Program only needs what execution uses).
#[derive(Clone, Debug, PartialEq)]
pub struct PayloadMeta {
    /// `Some(cache_index)` for CacheK (index into the layer's cache list,
    /// = the sentinel index); `None` for GateK.
    pub cache: Option<u16>,
    /// CacheK result domain (drives the sentinel cell write width).
    pub e4: bool,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Program {
    pub instrs: Vec<Instr>,
    /// Deduplicated canonical u32 constants; never contains 0, 1, NEG_ONE_U32.
    pub consts: Vec<u32>,
    pub n_slot_cells: u16,
    pub n_fixed_cells: u16,
    pub n_sources_bf: u16,
    pub n_sources_e4: u16,
    /// Size of the ORIGINAL layer output-slot list (sparse writes).
    pub n_outputs: u16,
    /// Number of gate-input staging values the program produces (cone
    /// programs; 0 for forward programs).
    pub n_gate_ins: u16,
    /// NativeK payload metadata, indexed by the instruction payload lane.
    /// Empty for cone programs.
    pub payloads: Vec<PayloadMeta>,
}

impl Instr {
    /// Arity as encoded: operand count for SumK/ProdK, PAIR count for DotK.
    pub fn arity(&self) -> usize {
        match self.op {
            Op::DotK => self.operands.len() / 2,
            _ => self.operands.len(),
        }
    }
}

pub const MAX_ARITY: usize = 31;
const DST_SENTINEL: u16 = 63;

pub fn encode(p: &Program) -> Vec<u16> {
    let mut lanes = Vec::new();
    for ins in &p.instrs {
        let native = ins.op == Op::NativeK;
        assert_eq!(native, ins.payload.is_some(), "payload iff NativeK");
        if !native {
            assert!(ins.arity() <= MAX_ARITY, "compiler must split wide nodes");
            assert!(!matches!(ins.dst, Dst::Native), "Dst::Native is NativeK-only");
        } else {
            assert!(
                matches!(ins.dst, Dst::Native | Dst::Slot(_)),
                "NativeK dst is Native (gate) or Slot (cache cell)"
            );
        }
        let (dst_class, dst_idx) = match ins.dst {
            Dst::Slot(i) => (0u16, i),
            Dst::FixedReg(i) => (1, i),
            Dst::Output(i) => (2, i),
            Dst::GateIn(i) => (3, i),
            Dst::Native => (3, 0),
        };
        let dst_lo = if dst_idx < DST_SENTINEL { dst_idx } else { DST_SENTINEL };
        // NativeK leaves the 5-bit arity field 0 and spends a count lane.
        let arity_bits = if native { 0 } else { ins.arity() as u16 };
        lanes.push(
            (ins.op as u16)
                | ((ins.e4_result as u16) << 2)
                | (dst_class << 3)
                | (arity_bits << 5)
                | (dst_lo << 10),
        );
        if dst_lo == DST_SENTINEL {
            lanes.push(dst_idx);
        }
        if native {
            lanes.push(ins.payload.unwrap());
            lanes.push(ins.operands.len() as u16);
        }
        for o in &ins.operands {
            let (kind, e4, idx) = match *o {
                Operand::Source { id, e4 } => (0u16, e4, id),
                Operand::Slot { cell, e4 } => (1, e4, cell),
                Operand::FixedReg { cell, e4 } => (2, e4, cell),
                Operand::Const { idx } => (3, false, idx as u16),
                Operand::Zero => (4, false, 0),
                Operand::One => (5, false, 0),
                Operand::NegOne => (6, false, 0),
            };
            assert!(idx < (1 << 12));
            lanes.push(kind | ((e4 as u16) << 3) | (idx << 4));
        }
    }
    lanes
}

/// Decode `n_instr` instructions. Meta fields (`consts`, cell counts) are not
/// part of the lane stream; the caller carries them.
pub fn decode(lanes: &[u16], n_instr: usize) -> Vec<Instr> {
    let mut out = Vec::with_capacity(n_instr);
    let mut i = 0;
    for _ in 0..n_instr {
        let h = lanes[i];
        i += 1;
        let op = match h & 0b11 {
            0 => Op::SumK,
            1 => Op::ProdK,
            2 => Op::DotK,
            _ => Op::NativeK,
        };
        let e4_result = (h >> 2) & 1 == 1;
        let dst_class = (h >> 3) & 0b11;
        let arity = ((h >> 5) & 0b11111) as usize;
        let dst_lo = (h >> 10) & 0x3F;
        let dst_idx = if dst_lo == DST_SENTINEL {
            let v = lanes[i];
            i += 1;
            v
        } else {
            dst_lo
        };
        let dst = match (dst_class, op) {
            (0, _) => Dst::Slot(dst_idx),
            (1, _) => Dst::FixedReg(dst_idx),
            (2, _) => Dst::Output(dst_idx),
            (3, Op::NativeK) => Dst::Native,
            _ => Dst::GateIn(dst_idx),
        };
        let (payload, n_operands) = if op == Op::NativeK {
            let pl = lanes[i];
            i += 1;
            let cnt = lanes[i] as usize;
            i += 1;
            (Some(pl), cnt)
        } else {
            (None, if matches!(op, Op::DotK) { arity * 2 } else { arity })
        };
        let mut operands = Vec::with_capacity(n_operands);
        for _ in 0..n_operands {
            let l = lanes[i];
            i += 1;
            let e4 = (l >> 3) & 1 == 1;
            let idx = l >> 4;
            operands.push(match l & 0b111 {
                0 => Operand::Source { id: idx, e4 },
                1 => Operand::Slot { cell: idx, e4 },
                2 => Operand::FixedReg { cell: idx, e4 },
                3 => Operand::Const { idx: idx as u8 },
                4 => Operand::Zero,
                5 => Operand::One,
                _ => Operand::NegOne,
            });
        }
        out.push(Instr { op, e4_result, dst, operands, payload });
    }
    assert_eq!(i, lanes.len(), "trailing lanes");
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_decode_roundtrip() {
        let instrs = vec![
            Instr {
                op: Op::SumK,
                e4_result: false,
                dst: Dst::GateIn(2),
                operands: vec![
                    Operand::Source { id: 7, e4: false },
                    Operand::Const { idx: 2 },
                    Operand::NegOne,
                ],
                payload: None,
            },
            Instr {
                op: Op::DotK,
                e4_result: true,
                dst: Dst::Output(700), // forces the extra dst lane
                operands: vec![
                    Operand::Slot { cell: 12, e4: true },
                    Operand::Source { id: 3, e4: false },
                    Operand::FixedReg { cell: 0, e4: false },
                    Operand::One,
                ],
                payload: None,
            },
            Instr {
                op: Op::NativeK,
                e4_result: true,
                dst: Dst::Slot(4), // CacheK: e4 cache result cell
                operands: vec![
                    Operand::Source { id: 9, e4: false },
                    Operand::Slot { cell: 0, e4: false },
                ],
                payload: Some(1),
            },
            Instr {
                op: Op::NativeK,
                e4_result: false,
                dst: Dst::Native, // GateK: no interpreter dst
                operands: vec![Operand::Slot { cell: 4, e4: true }],
                payload: Some(7),
            },
        ];
        let p = Program { instrs: instrs.clone(), ..Default::default() };
        let lanes = encode(&p);
        // instr0: 1 header + 3 operands = 4
        // instr1: 1 header + 1 dst + 4 operands = 6
        // NativeK-cache: 1 header + 1 payload + 1 count + 2 operands = 5
        // NativeK-gate: 1 header + 1 payload + 1 count + 1 operand = 4
        assert_eq!(lanes.len(), 4 + 6 + 5 + 4);
        assert_eq!(decode(&lanes, 4), instrs);
    }
}
