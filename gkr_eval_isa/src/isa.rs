//! ISA types and 16-bit lane encoding (spec §5).

pub const NEG_ONE_U32: u32 = 2013265920; // BabyBear p - 1

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    SumK = 0,
    ProdK = 1,
    DotK = 2,
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
    /// native gate logic.
    GateIn(u16),
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
    pub operands: Vec<Operand>,
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
    /// Number of gate-input staging values the program produces.
    pub n_gate_ins: u16,
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
        assert!(ins.arity() <= MAX_ARITY, "compiler must split wide nodes");
        let (dst_class, dst_idx) = match ins.dst {
            Dst::Slot(i) => (0u16, i),
            Dst::FixedReg(i) => (1, i),
            Dst::Output(i) => (2, i),
            Dst::GateIn(i) => (3, i),
        };
        let dst_lo = if dst_idx < DST_SENTINEL { dst_idx } else { DST_SENTINEL };
        lanes.push(
            (ins.op as u16)
                | ((ins.e4_result as u16) << 2)
                | (dst_class << 3)
                | ((ins.arity() as u16) << 5)
                | (dst_lo << 10),
        );
        if dst_lo == DST_SENTINEL {
            lanes.push(dst_idx);
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
            _ => Op::DotK,
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
        let dst = match dst_class {
            0 => Dst::Slot(dst_idx),
            1 => Dst::FixedReg(dst_idx),
            2 => Dst::Output(dst_idx),
            _ => Dst::GateIn(dst_idx),
        };
        let n_operands = if matches!(op, Op::DotK) { arity * 2 } else { arity };
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
        out.push(Instr { op, e4_result, dst, operands });
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
            },
        ];
        let p = Program { instrs: instrs.clone(), ..Default::default() };
        let lanes = encode(&p);
        // instr0: 1 header + 3 operands; instr1: 1 header + 1 dst + 4 operands.
        assert_eq!(lanes.len(), 4 + 6);
        assert_eq!(decode(&lanes, 2), instrs);
    }
}
