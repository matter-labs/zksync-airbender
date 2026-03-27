use super::*;
use crate::types::Boolean;
use field::PrimeField;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ShuffleRamQueryType {
    RegisterOnly {
        register_index: Variable,
    },
    RegisterOrRam {
        is_register: Boolean,
        address: [Variable; REGISTER_SIZE],
    },
}

// impl ShuffleRamQueryType {
//     pub fn get_address<F: PrimeField, CS: Circuit<F>>(&self, cs: &CS) -> Option<u32> {
//         match *self {
//             Self::RegisterOnly { .. } => None,
//             Self::RegisterOrRam {
//                 is_register,
//                 address,
//             } => {
//                 let addr =
//                     cs.get_value(address[0])
//                         .zip_with(cs.get_value(address[1]), |low, high| {
//                             (low.as_u32_reduced() | (high.as_u32_reduced() << 16))
//                                 .try_into()
//                                 .unwrap()
//                         });
//                 let flag = cs
//                     .get_value(is_register.get_variable().unwrap())
//                     .filter(|&b| b == F::ZERO);
//                 flag.and(addr)
//             }
//         }
//     }
//     pub fn get_register_id<F: PrimeField, CS: Circuit<F>>(&self, cs: &CS) -> Option<u8> {
//         match *self {
//             Self::RegisterOnly { register_index } => cs
//                 .get_value(register_index)
//                 .map(|f| f.as_u32_reduced().try_into().unwrap()),
//             Self::RegisterOrRam {
//                 is_register,
//                 address,
//             } => {
//                 let flag = cs
//                     .get_value(is_register.get_variable().unwrap())
//                     .filter(|&b| b == F::ONE);
//                 flag.and_then(|_| {
//                     cs.get_value(address[0])
//                         .zip_with(cs.get_value(address[1]), |low, high| {
//                             (low.as_u32_reduced() | (high.as_u32_reduced() << 16))
//                                 .try_into()
//                                 .unwrap()
//                         })
//                 })
//             }
//         }
//     }
// }

// // Prover would have to substitute global timestamp here
// // but itself, and ensure that eventually global read timestamp
// // is < global write timestamp + local offset
// #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
// pub struct ShuffleRamMemQuery {
//     pub query_type: ShuffleRamQueryType,
//     pub local_timestamp_in_cycle: usize,
//     pub read_value: [Variable; REGISTER_SIZE],
//     pub write_value: [Variable; REGISTER_SIZE],
// }

// impl ShuffleRamMemQuery {
//     pub fn is_readonly(&self) -> bool {
//         if self.read_value == self.write_value {
//             true
//         } else {
//             for (a, b) in self.read_value.iter().zip(self.write_value.iter()) {
//                 assert!(a != b);
//             }

//             false
//         }
//     }
//     pub fn get_write_value<F: PrimeField, CS: Circuit<F>>(&self, cs: &CS) -> u32 {
//         cs.get_value(self.write_value[0])
//             .zip_with(cs.get_value(self.write_value[1]), |low, high| {
//                 (low.as_u32_reduced() | (high.as_u32_reduced() << 16))
//                     .try_into()
//                     .unwrap()
//             })
//             .unwrap()
//     }
//     pub fn get_read_value<F: PrimeField, CS: Circuit<F>>(&self, cs: &CS) -> u32 {
//         cs.get_value(self.read_value[0])
//             .zip_with(cs.get_value(self.read_value[1]), |low, high| {
//                 (low.as_u32_reduced() | (high.as_u32_reduced() << 16))
//                     .try_into()
//                     .unwrap()
//             })
//             .unwrap()
//     }
// }

#[derive(Clone, Debug)]
pub struct LookupQuery<F: PrimeField> {
    pub row: Vec<LookupInput<F>>,
    pub table: LookupQueryTableType<F>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LookupQueryTableType<F: PrimeField> {
    Variable(Variable),
    Constant(TableType),
    Expression(LookupInput<F>),
}

#[derive(Clone, Debug)]
pub struct RangeCheckQuery<F: PrimeField> {
    pub input: LookupInput<F>,
    pub width: usize,
}

impl<F: PrimeField> RangeCheckQuery<F> {
    pub fn new(variable: Variable, width: usize) -> Self {
        RangeCheckQuery {
            input: LookupInput::Variable(variable),
            width,
        }
    }

    pub fn new_for_input(input: LookupInput<F>, width: usize) -> Self {
        RangeCheckQuery { input, width }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct IndirectAccessOffset {
    pub variable_dependent: Option<(u32, Variable)>,
    pub offset_constant: u32,
    pub assume_no_alignment_overflow: bool,
    pub is_write_access: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct RegisterAccessRequest {
    pub register_index: u32,
    pub register_write: bool,
    pub indirects_alignment_log2: u32,
    pub indirect_accesses: Vec<IndirectAccessOffset>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RegisterAccessType {
    Read {
        read_value: [Variable; REGISTER_SIZE],
    },
    Write {
        read_value: [Variable; REGISTER_SIZE],
        write_value: [Variable; REGISTER_SIZE],
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IndirectAccessType {
    Read {
        read_value: [Variable; REGISTER_SIZE],
        variable_dependent: Option<(u32, Variable, usize)>,
        offset_constant: u32,
        assume_no_alignment_overflow: bool,
    },
    Write {
        read_value: [Variable; REGISTER_SIZE],
        write_value: [Variable; REGISTER_SIZE],
        variable_dependent: Option<(u32, Variable, usize)>,
        offset_constant: u32,
        assume_no_alignment_overflow: bool,
    },
}

impl IndirectAccessType {
    pub const fn consider_aligned(&self) -> bool {
        match self {
            Self::Read {
                assume_no_alignment_overflow,
                ..
            } => *assume_no_alignment_overflow,
            Self::Write {
                assume_no_alignment_overflow,
                ..
            } => *assume_no_alignment_overflow,
        }
    }

    pub const fn offset_constant(&self) -> u32 {
        match self {
            Self::Read {
                offset_constant, ..
            } => *offset_constant,
            Self::Write {
                offset_constant, ..
            } => *offset_constant,
        }
    }

    pub const fn variable_dependent(&self) -> Option<(u32, Variable, usize)> {
        match self {
            Self::Read {
                variable_dependent, ..
            } => *variable_dependent,
            Self::Write {
                variable_dependent, ..
            } => *variable_dependent,
        }
    }

    pub const fn read_value(&self) -> [Variable; 2] {
        match self {
            Self::Read { read_value, .. } => *read_value,
            Self::Write { read_value, .. } => *read_value,
        }
    }

    pub const fn write_value(&self) -> Option<[Variable; 2]> {
        match self {
            Self::Read { .. } => None,
            Self::Write { write_value, .. } => Some(*write_value),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RegisterAndIndirectAccesses {
    pub register_index: u32,
    pub register_access: RegisterAccessType,
    pub indirects_alignment_log2: u32,
    pub indirect_accesses: Vec<IndirectAccessType>,
}
