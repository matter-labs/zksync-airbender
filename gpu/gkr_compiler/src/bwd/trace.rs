use gkr_eval_ir::ExprId;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BwdServeKind {
    RootOutput,
    Operand,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BwdFingerprint {
    pub term: u32,
    pub kind: BwdServeKind,
    pub value: ExprId,
    pub consumer: Option<ExprId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BwdServedFrom {
    Recomputed,
    Resident,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BwdEvent {
    Serve {
        fp: BwdFingerprint,
        from: BwdServedFrom,
    },
    TrafficRead {
        value: ExprId,
        cells: u32,
    },
    Admit {
        value: ExprId,
        width: u8,
    },
    Evict {
        value: ExprId,
        expired: bool,
    },
    Refuse {
        value: ExprId,
        need: u32,
    },
    Diverge {
        at_entry: usize,
    },
}

#[derive(Clone, Debug)]
pub struct BwdCompileTrace {
    pub events: Vec<BwdEvent>,
}
