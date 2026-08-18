use super::{CircuitId, CostTable};
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

pub static TABLES: &[(FsvProgram, BlakeMode, CostTable)] = &[
    (
        FsvProgram::UnrolledBaseLayer,
        BlakeMode::Compression,
        CostTable {
            c0: 829388,
            v: &[
                (CircuitId::Riscv(1), 836806),
                (CircuitId::Riscv(2), 860392),
                (CircuitId::Riscv(3), 871878),
                (CircuitId::Riscv(4), 859852),
                (CircuitId::Riscv(16), 828582),
                (CircuitId::Riscv(17), 844210),
                (CircuitId::Delegation(1991), 2328581),
                (CircuitId::Delegation(1994), 1263472),
                (CircuitId::Delegation(1995), 1240848),
            ],
        },
    ),
    (
        FsvProgram::UnrolledRecursionLayer,
        BlakeMode::Compression,
        CostTable {
            c0: 817362,
            v: &[
                (CircuitId::Riscv(1), 836806),
                (CircuitId::Riscv(2), 860392),
                (CircuitId::Riscv(3), 871878),
                (CircuitId::Riscv(16), 828582),
                (CircuitId::Delegation(1991), 2328581),
                (CircuitId::Delegation(1994), 1263472),
                (CircuitId::Delegation(1995), 1240848),
            ],
        },
    ),
];
