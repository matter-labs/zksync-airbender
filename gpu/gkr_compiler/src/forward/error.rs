//! Centralized error types for the forward-eval VM. `From` conversions let the
//! compiler bubble encode/bind failures into `CompileError` cleanly.

use gkr_eval_ir::ChallengeRef;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EncodeError {
    SlotOutOfRange(u8),
    ColOutOfRange(u16),
    CellOutOfRange(u16),
    SourceWindowOutOfRange(u8),
    SourceColumnOutOfRange(u8),
    UnboundLogicalSource {
        slot: u8,
        col: u16,
    },
    LdcIdxOutOfRange(u16),
    DescOutOfRange(u16),
    ArityOutOfRange(usize),
    /// FMA with `field_lhs=Ext, field_rhs=Base` (EB order) is non-canonical;
    /// the compiler must emit the canonical `BE` form instead.
    NonCanonicalFmaOrder,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BindError {
    SlotOverflow,
    ColOverflow(usize),
    SourceWindowOverflow,
    UnknownLogicalSource { slot: u8, col: u16 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileError {
    UncoveredLookupLeaf(u32), // ExprId.0
    UnsupportedChallenge(ChallengeRef),
    FieldMismatch(String),
    /// A global operand's field disagrees with its storage slot.
    FieldStorageMismatch {
        slot: u8,
        col: u16,
    },
    ExtCellMisaligned(u16),
    /// The required live width exceeds the shared-memory budget.
    BudgetBelowFloor {
        floor: usize,
        budget: usize,
    },
    /// Structural schedule validation failed.
    InvalidSchedule(String),
    Bind(BindError),
    Encode(EncodeError),
}
impl From<BindError> for CompileError {
    fn from(e: BindError) -> Self {
        CompileError::Bind(e)
    }
}
impl From<EncodeError> for CompileError {
    fn from(e: EncodeError) -> Self {
        CompileError::Encode(e)
    }
}
