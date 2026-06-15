//! ISA-v2 compiler (spec §5). New sibling module to the v1 `compiler`; reuses
//! v1 infrastructure but does not change v1 behaviour. Sub-passes are added by
//! later tasks; Task 2.1 seeds the joint matrix-slot table.

pub mod matrix_table;
pub mod challenges;
pub mod gather;
