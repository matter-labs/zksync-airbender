use gkr_eval_ir::{ReadPlace, VirtualSetupKind};

/// The canonical identity of a backward coefficient source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OriginLeaf {
    Read(ReadPlace),
    VirtualSetup { kind: VirtualSetupKind },
}

impl OriginLeaf {
    pub fn is_vs(&self) -> bool {
        matches!(self, Self::VirtualSetup { .. })
    }
}
