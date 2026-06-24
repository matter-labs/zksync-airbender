---
[dependencies]
cs = { path = "../cs", features = ["compiler"] }
field = { path = "../field" }
prover = { path = "../prover" }
serde_json = "1"
indoc = "2"
---

use cs::{
    definitions::{GKRAddress::{self, InnerLayer}, VirtualSetupPoly, gkr::{AddressSpaceType, NoFieldLinearRelation, NoFieldSingleColumnLookupRelation, NoFieldVectorLookupRelation, RamWordRepresentation}},
    gkr_compiler::{CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp, GKRCircuitArtifact, GKRLayerDescription, GateArtifacts, InitsOrTeardownsTimestampAndValue, NoFieldGKRCacheRelation, NoFieldGKRRelation, NoFieldMaxQuadraticGKRRelation, NoFieldSpecialMemoryContributionRelation}
};
// use cs::gkr_compiler::NoFieldStructuredExpression;
use field::{PrimeField, baby_bear::base::BabyBearField};

trait EachRefRev<T, const N: usize> {
    fn each_ref_rev(&self) -> [&T; N];
    fn each_ref_revmap<U>(&self, f: impl FnMut(&T) -> U) -> [U; N];
}

impl<T, const N: usize> EachRefRev<T, N> for [T; N] {
    fn each_ref_rev(&self) -> [&T; N] {
        std::array::from_fn(|i| &self[N - 1 - i])
    }

    fn each_ref_revmap<U>(&self, mut f: impl FnMut(&T) -> U) -> [U; N] {
        let mut out = self.each_ref_rev().map(|x| f(x));
        out.reverse();
        out
    }
}

struct Yul(String);
struct Dual(String, Yul);
impl std::fmt::Display for Dual {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
impl std::fmt::LowerHex for Dual {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Display;
        self.1.0.fmt(f) // yul
    }
}

impl std::fmt::LowerHex for Yul {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Display;
        self.0.fmt(f)
    }
}
macro_rules! yul_format {
    ($($arg:tt)*) => {
        Yul(indoc::formatdoc!($($arg)*).replace('\t', "    "))
    };
}
static YUL_OUTPUT_FILE: std::sync::OnceLock<std::sync::Mutex<std::fs::File>> =
    std::sync::OnceLock::new();
macro_rules! yul_println {
    ($($arg:tt)*) => {
        {
            let yul = yul_format!($($arg)*).0;
            println!("{yul}");
            let file = YUL_OUTPUT_FILE.get_or_init(|| {
                std::sync::Mutex::new(
                    std::fs::OpenOptions::new()
                        .create(true)
                        .truncate(true)
                        .write(true)
                        .open("circuit.yul")
                        .unwrap(),
                )
            });
            use std::io::Write as _;
            writeln!(file.lock().unwrap(), "{yul}").unwrap();
        }
    };
}
impl Yul {
    fn calldataload(idx: &usize) -> Self {
        Self(format!("shr(128, calldataload(add(ptr, mul(16, {idx}))))"))
    }
    fn mload(idx: &usize) -> Self {
        Self(format!("mload(add(CIRCUIT_CACHE_PTR, mul(32, {idx})))"))
    }
    fn logup_gamma() -> Self {
        yul_format!("mload(add(LOGUP_CHALLS_PTR, 32))")
    }
    fn logup_alpha() -> Self {
        yul_format!("mload(LOGUP_CHALLS_PTR)")
    }
    fn memory_gamma() -> Self {
        yul_format!("mload(add(MEMORY_CHALLS_PTR, mul(32, 6)))")
    }
    fn memory_alpha(idx: usize) -> Self {
        match idx {
            0..6 => yul_format!("mload(add(MEMORY_CHALLS_PTR, mul(32, {idx})))"),
            _ => unreachable!("we do not have memory linearisation challenge alpha_{idx}")
        }
    }
}
fn superscript(idx: usize) -> String {
    idx.to_string()
        .chars()
        .map(|c| match c {
            '0' => '⁰',
            '1' => '¹',
            '2' => '²',
            '3' => '³',
            '4' => '⁴',
            '5' => '⁵',
            '6' => '⁶',
            '7' => '⁷',
            '8' => '⁸',
            '9' => '⁹',
            _ => unreachable!(),
        })
        .collect()
}
fn const_to_evm(c: &u32) -> Dual {
    assert!(*c < BabyBearField::ORDER, "we don't expect circuits with unreduced constants");
    // first check if negative
    let (sign, modc, yul) = if *c > BabyBearField::ORDER / 2 {
        let modc = BabyBearField::ORDER - c;
        ("-", modc, yul_format!("sub(P, {modc})"))
    } else { 
        ("", *c, yul_format!("{c}"))
    };
    let normal = match modc {
        modc if modc.is_power_of_two() && !(0..=2).contains(&modc) => {
            let power = modc.trailing_zeros();
            format!("{sign}2^{power}")
        }
        _ => format!("{sign}{modc}")
    };
    Dual(normal, yul)
}
fn u128_to_neg(Dual(input, yul): &Dual) -> Dual {
    Dual(format!("-{input}"), yul_format!("sub(mul(2, P), {yul:x})"))
}

fn main() {
    let json = std::fs::read_to_string(
        // "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
        // "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json",
        "../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json",
        // "../cs/compiled_circuits/unified_reduced_machine_layout_gkr.json",
    )
    .unwrap();
    let circuit: GKRCircuitArtifact<BabyBearField> = serde_json::from_str(&json).unwrap();
    let layer0_group_widths = (circuit.memory_layout.total_width, circuit.witness_layout.total_width, circuit.generic_lookup_tables_width, circuit.layers[0].cached_relations.len());
    // let mut previous_input_count = 8;
    let mut previous_input_count = 10; // TEMPORARY: unified adds another product pair for inits/teardowns
    let mut collected_previous_input_counts = vec![];
    for (i, layer) in circuit.layers.iter().enumerate().rev() {
        let GKRLayerDescription { layer, gates_with_external_connections, cached_relations, gates, intermediate_layer_width } = layer;
        assert!(*layer == i);
        let gates = if i == circuit.layers.len() - 1 {
            assert!(gates.is_empty());
            gates_with_external_connections
        } else {
            assert!(gates_with_external_connections.is_empty());
            gates
        };

        // println!("{i}:");
        const DEBUG_ENABLE_DUMMY_CHECKS: bool = true;
        let check = if DEBUG_ENABLE_DUMMY_CHECKS {
            yul_format!("
            let dummy_check := mod(add(claim, sub(P, g0g1_scaled)), P)
            \t\tmstore(CIRCUIT_CACHE_PTR, dummy_check)
            ")
        } else {
            yul_format!("
            if mod(add(claim, sub(P, g0g1_scaled)), P) {{ revert(0, 0) }}
            ")
        };
        yul_println!("
        function sumcheck_circuit_layer{i}(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {{
            // SUMCHECK ROUNDS
            let eq_scale := 1
            for {{ let i := 0 }} lt(i, CIRCUIT_LAYER_ROUNDS) {{ i := add(i, 1) }} {{
                let w0 := calldataload(ptr)
                let w1 := calldataload(add(ptr, 32))
                let c0 := shr(128, w0)
                let c1 := and(w0, MASK)
                let c2 := shr(128, w1)
                let c3 := and(w1, MASK)
                let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, P)
                let r := transcript_4to1_dual(w0, w1) // before check is optimal
                // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
                {check:x}
                claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
                let z := mload(add(POINT_PTR, mul(i, 32)))
                let zr := mulmod(z, r, P)
                eq_scale := add(add(add(zr, zr), 1), sub(mul(4, P), add(z, r)))
                mstore(add(POINT_PTR, mul(i, 32)), r)
                ptr := add(ptr, 64)
            }}
            
            // POINT CHECK
            let acc");
        let mut running_max_group_offsets = (0, 0, 0, 0);
        let mut running_cachedoutput_counter = 0;
        for (cached_address, cached_relation) in cached_relations {
            let output = gkraddress_to_outputvar(cached_address, i, &mut running_cachedoutput_counter);
            let relation_name = serde_json::to_value(cached_relation).unwrap().as_object().unwrap().keys().next().unwrap().clone();

            fn gkraddress_to_calldata(address: &GKRAddress, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize)) -> String {
                let (l0_memvars, l0_witvars, _l0_setupvars, _l0_cachevars) = layer0_group_widths;
                let (_running_max_memvar, _running_max_witvar, running_max_setupvar, _running_max_cachevar) = running_max_group_offsets;
                match address {
                    // InnerLayer { layer, offset } if *layer==expected_layer && expected_layer > 0 => format!("[{offset}]"),
                    // GKRAddress::BaseLayerMemory(offset) if expected_layer == 0 => {
                    //     *running_max_memvar = *offset.max(running_max_memvar);
                    //     let calldata_offset = offset; // memory is first in calldata
                    //     format!("[{calldata_offset}]")
                    // },
                    // GKRAddress::BaseLayerWitness(offset) if expected_layer == 0 => {
                    //     *running_max_witvar = *offset.max(running_max_witvar);
                    //     let calldata_offset = l0_memvars + offset; // witness is second in calldata
                    //     format!("[{calldata_offset}]")
                    // },
                    GKRAddress::Setup(offset) if expected_layer == 0 => {
                        *running_max_setupvar = *offset.max(running_max_setupvar);
                        let calldata_offset = l0_memvars + l0_witvars + offset; // setup is third in calldata
                        format!("[{calldata_offset}]")
                    },
                    // GKRAddress::Cached { layer, offset } if *layer==expected_layer && expected_layer == 0 => format!("c[{offset}]"),
                    // GKRAddress::VirtualSetup(setup) => format!("VirtualSetup{setup:?}(0)"),
                    _ => todo!("unexpected address {address:?} for layer {expected_layer}")
                }
            }
            fn gkraddress_to_outputvar(address: &GKRAddress, expected_layer: usize, running_cachedoutput_counter: &mut usize) -> String {
                match address {
                    GKRAddress::Cached { layer, offset } if *layer==expected_layer && expected_layer == 0 && *running_cachedoutput_counter == *offset => {
                        *running_cachedoutput_counter += 1;
                        format!("Cache({offset})")
                    }
                    _ => todo!("unexpected address {address:?} for layer {expected_layer}")
                }
            }
            // fn linrel_to_calldata(inputs: &NoFieldLinearRelation, expected_layer: usize) -> String {
            //     let NoFieldLinearRelation { linear_terms, constant } = inputs;
            //     let linear = linear_terms.iter().map(|(c, addr)| {
            //         let input = gkraddress_to_calldata(addr, expected_layer);
            //         format!("{c}{input}")
            //     }).collect::<Vec<_>>().join(" + ");
            //     format!("({constant} + {linear})")
            // }

            match cached_relation {
                // NoFieldGKRCacheRelation::VectorizedLookup(NoFieldVectorLookupRelation{ columns, lookup_set_index: _}) => {
                //     let term = columns.iter().enumerate().map(|(j, column)| {
                //         let linear = linrel_to_calldata(column, i);
                //         let beta_j = "β".to_string() + &superscript(j);
                //         format!("{beta_j}{linear}")
                //     }).collect::<Vec<_>>().join(" + ");
                //     println!("{relation_name}: {term} = {output}");
                // }
                NoFieldGKRCacheRelation::VectorizedLookupSetup(terms) => {
                    let term = terms.iter().enumerate().map(|(j, addr)| {
                        let input = gkraddress_to_calldata(addr, i, layer0_group_widths, &mut running_max_group_offsets);
                        let beta_j = "β".to_string() + &superscript(j);
                        format!("{beta_j}{input}")
                    }).collect::<Vec<_>>().join(" + ");
                    println!("{relation_name}: {term} = {output}");
                }
                _ => todo!("could not match (cached) {cached_relation:?} at layer {i}")
            }
        }
        // INJECT VIRTUAL POLY CACHES
        let injected_virtualpoly_relations = [
            VirtualSetupPoly::RangeCheck16Bits,
            VirtualSetupPoly::RangeCheckTimestamp,
            VirtualSetupPoly::InitsAndTeardownsLow,
            VirtualSetupPoly::InitsAndTeardownsHigh,
        ];
        if i == 0 {
            for virtualpoly_relation in injected_virtualpoly_relations {
                let cache_idx = running_cachedoutput_counter + virtualpoly_relation as usize;
                let output = format!("Cache({cache_idx})");
                let relation_name = format!("{virtualpoly_relation:?}");
                match virtualpoly_relation {
                    VirtualSetupPoly::RangeCheck16Bits => {
                        println!("{relation_name}: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8])(1 - r[7])(1 - r[6])(1 - r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = {output}");
                    }
                    VirtualSetupPoly::RangeCheckTimestamp => {
                        // TODO: u wanna custom merge this with RangeCheck16Bits since most calculations overlap and can be reused
                        println!("{relation_name}: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8] + 2^16 r[7] + 2^17 r[6] + 2^18 r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = {output}");
                    }
                    VirtualSetupPoly::InitsAndTeardownsLow => {
                        // TODO: u wanna custom merge this with RangeCheck16Bits since most calculations overlap and can be reused
                        println!("{relation_name}: 4(2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10]) = {output}");
                    }
                    VirtualSetupPoly::InitsAndTeardownsHigh => {
                        println!("{relation_name}: 2^0 r[9] + 2^1 r[8] + 2^2 r[7] + 2^3 r[6] + 2^4 r[5] + 2^5 r[4] + 2^6 r[3] + 2^7 r[2] + 2^8 r[1] + 2^9 r[0] = {output}");
                    }
                }
            }
        }
        const DEBUG_NATURAL_GATE_ORDER: bool = true;
        trait EachRefMaybeRev<T, const N: usize> {
            fn each_ref_mayberevmap<U>(&self, f: impl FnMut(&T) -> U) -> [U; N];
        }
        impl<T, const N: usize> EachRefMaybeRev<T, N> for [T; N] {
            fn each_ref_mayberevmap<U>(&self, f: impl FnMut(&T) -> U) -> [U; N] {
                if DEBUG_NATURAL_GATE_ORDER {
                    self.each_ref().map(f)
                } else {
                    self.each_ref_revmap(f)
                }
            }
        }
        let mut running_output_counter = if DEBUG_NATURAL_GATE_ORDER {
            0
        } else {
            previous_input_count
        };
        for gate_idx in 0..gates.len() {
            let gate_idx_rev = gates.len() - 1 - gate_idx;
            let gate = &gates[if DEBUG_NATURAL_GATE_ORDER { gate_idx } else { gate_idx_rev }];
            let GateArtifacts { output_layer, enforced_relation } = gate;
            assert!(*output_layer == i+1);
            let relation_name =  serde_json::to_value(enforced_relation).unwrap().as_object().unwrap().keys().next().unwrap().clone();
            let pointcheck_update = yul_format!("acc := add(mulmod(acc, alpha, P), gate)");

            fn gkraddress_to_calldata(address: &GKRAddress, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize)) -> Dual {
                let (l0_memvars, l0_witvars, _l0_setupvars, l0_cachevars) = layer0_group_widths;
                let (running_max_memvar, running_max_witvar, running_max_setupvar, running_max_cachevar) = running_max_group_offsets;
                match address {
                    InnerLayer { layer, offset } if *layer==expected_layer && expected_layer > 0 => {
                        Dual(format!("[{offset}]"), Yul::calldataload(offset))
                    },
                    GKRAddress::BaseLayerMemory(offset) if expected_layer == 0 => {
                        *running_max_memvar = *offset.max(running_max_memvar);
                        let calldata_offset = offset; // memory is first in calldata
                        Dual(format!("[{calldata_offset}]"), Yul::calldataload(calldata_offset))
                    },
                    GKRAddress::BaseLayerWitness(offset) if expected_layer == 0 => {
                        *running_max_witvar = *offset.max(running_max_witvar);
                        let calldata_offset = l0_memvars + offset; // witness is second in calldata
                        Dual(format!("[{calldata_offset}]"), Yul::calldataload(&calldata_offset))
                    },
                    GKRAddress::Setup(offset) if expected_layer == 0 => {
                        *running_max_setupvar = *offset.max(running_max_setupvar);
                        let calldata_offset = l0_memvars + l0_witvars + offset; // setup is third in calldata
                        Dual(format!("[{calldata_offset}]"), Yul::calldataload(&calldata_offset))
                    },
                    GKRAddress::Cached { layer, offset } if *layer==expected_layer && expected_layer == 0 => {
                        *running_max_cachevar = *offset.max(running_max_cachevar);
                        Dual(format!("Cache({offset})"), Yul::mload(offset))
                    },
                    GKRAddress::VirtualSetup(virtual_poly) if expected_layer == 0 => {
                        let cache_idx = l0_cachevars + *virtual_poly as usize;
                        *running_max_cachevar = cache_idx.max(*running_max_cachevar);
                        Dual(format!("Cache({cache_idx})"), Yul::mload(&cache_idx))
                    }
                    // GKRAddress::VirtualSetup(virtual_poly) => format!("VirtualSetup{setup:?}(x)")
                    _ => todo!("unexpected address {address:?} for layer {expected_layer}")
                }
            }
            fn gkraddress_to_outputvar(address: &GKRAddress, expected_layer: usize, running_output_counter: &mut usize) -> String {
                match address {
                    InnerLayer { layer, offset } if DEBUG_NATURAL_GATE_ORDER && *layer == expected_layer && *offset == *running_output_counter => {
                        *running_output_counter += 1;
                        format!("[{offset}]")
                    },
                    InnerLayer { layer, offset } if !DEBUG_NATURAL_GATE_ORDER && *layer == expected_layer && *offset + 1 == *running_output_counter => {
                        *running_output_counter -= 1;
                        format!("[{offset}]")
                    },
                    _ => unreachable!("unexpected output address {address:?} for layer {expected_layer} with {running_output_counter} outputs left")
                }
            }
            fn memrel_to_calldata(tuple: &NoFieldSpecialMemoryContributionRelation, running_max_group_offsets: &mut (usize, usize, usize, usize)) -> Dual {
                let (running_max_memvar, _running_max_witvar, _running_max_setupvar, _running_max_cachevar) = running_max_group_offsets;
                let NoFieldSpecialMemoryContributionRelation { address_space, address, timestamp, value, timestamp_offset } = tuple;
                let address_space = match address_space {
                    CompiledAddressSpaceRelationStrict::Constant(c) => const_to_evm(c),
                    CompiledAddressSpaceRelationStrict::IsRam(idx) => {
                        *running_max_memvar = *idx.max(running_max_memvar);
                        Dual(format!("[{idx}]"), Yul::calldataload(idx))
                    },
                    CompiledAddressSpaceRelationStrict::IsRegister(idx) => {
                        *running_max_memvar = *idx.max(running_max_memvar);
                        let var = Dual(format!("[{idx}]"), Yul::calldataload(idx));
                        let negvar = u128_to_neg(&var);
                        Dual(format!("(1 + {negvar})"), yul_format!("add(1, {negvar:x})"))
                    },
                };
                let [addr_low, addr_high] = match address {
                    CompiledAddressStrict::Constant(c) => {
                        assert!(*c < (1<<16), "with {address:?} we expect c < 2^16");
                        let c = const_to_evm(c);
                        let zero = Dual(format!("0"), yul_format!("0"));
                        [c, zero]
                    },
                    CompiledAddressStrict::ConstantU16(c) => {
                        let c = const_to_evm(&(*c as u32));
                        let zero = Dual(format!("0"), yul_format!("0"));
                        [c, zero]
                    },
                    CompiledAddressStrict::U16Space(idx) => {
                        *running_max_memvar = *idx.max(running_max_memvar);
                        let var = Dual(format!("[{idx}]"), Yul::calldataload(idx));
                        let zero = Dual(format!("0"), yul_format!("0"));
                        [var, zero]
                    },
                    CompiledAddressStrict::U32Space([low, high]) => {
                        *running_max_memvar = *low.max(running_max_memvar);
                        *running_max_memvar = *high.max(running_max_memvar);
                        let low = Dual(format!("[{low}]"), Yul::calldataload(low));
                        let high = Dual(format!("[{high}]"), Yul::calldataload(high));
                        [low, high]
                    },
                    _ => todo!()
                };
                let [ts_low, ts_high] = match timestamp {
                    CompiledMemoryTimestamp::Zero => {
                        assert_eq!(*timestamp_offset, 0, "with {timestamp:?} we expect timestamp_offset == 0");
                        let zero1 = Dual(format!("0"), yul_format!("0"));
                        let zero2 = Dual(format!("0"), yul_format!("0"));
                        [zero1, zero2]
                    },
                    CompiledMemoryTimestamp::Normal([low, high]) => {
                        *running_max_memvar = *low.max(running_max_memvar);
                        *running_max_memvar = *high.max(running_max_memvar);
                        let timestamp_offset = const_to_evm(timestamp_offset);
                        let low = Dual(format!("[{low}]"), Yul::calldataload(low));
                        let high = Dual(format!("[{high}]"), Yul::calldataload(high));
                        [Dual(format!("({timestamp_offset} + {low})"), yul_format!("add({timestamp_offset:x}, {low:x})")), high]
                    }
                };
                let [val_low, val_high] = match value {
                    RamWordRepresentation::Zero => {
                        let zero1 = Dual(format!("0"), yul_format!("0"));
                        let zero2 = Dual(format!("0"), yul_format!("0"));
                        [zero1, zero2]
                    },
                    RamWordRepresentation::U16Limbs([low, high]) => {
                        *running_max_memvar = *low.max(running_max_memvar);
                        *running_max_memvar = *high.max(running_max_memvar);
                        let low = Dual(format!("[{low}]"), Yul::calldataload(low));
                        let high = Dual(format!("[{high}]"), Yul::calldataload(high));
                        [low, high]
                    },
                    RamWordRepresentation::U8Limbs([ll, lh, hl, hh]) => {
                        *running_max_memvar = *ll.max(running_max_memvar);
                        *running_max_memvar = *lh.max(running_max_memvar);
                        *running_max_memvar = *hl.max(running_max_memvar);
                        *running_max_memvar = *hh.max(running_max_memvar);
                        let ll = Dual(format!("[{ll}]"), Yul::calldataload(ll));
                        let lh = Dual(format!("[{lh}]"), Yul::calldataload(lh));
                        let hl = Dual(format!("[{hl}]"), Yul::calldataload(hl));
                        let hh = Dual(format!("[{hh}]"), Yul::calldataload(hh));
                        let low = Dual(format!("([{ll}] + 2⁸[{lh}])"), yul_format!("add({ll:x}, shl(8, {lh:x}))"));
                        let high = Dual(format!("([{hl}] + 2⁸[{hh}])"), yul_format!("add({hl:x}, shl(8, {hh:x}))"));
                        [low, high]
                    }
                };
                let memory_gamma = Dual(format!("γ"), Yul::memory_gamma());
                let memory_alpha1 = Dual(format!("α"), Yul::memory_alpha(0));
                let memory_alpha2 = Dual(format!("α²"), Yul::memory_alpha(1));
                let memory_alpha3 = Dual(format!("α³"), Yul::memory_alpha(2));
                let memory_alpha4 = Dual(format!("α⁴"), Yul::memory_alpha(3));
                let memory_alpha5 = Dual(format!("α⁵"), Yul::memory_alpha(4));
                let memory_alpha6 = Dual(format!("α⁶"), Yul::memory_alpha(5));
                Dual(format!("({memory_gamma} + {address_space} + {memory_alpha1}{addr_low} + {memory_alpha2}{addr_high} + {memory_alpha3}{ts_low} + {memory_alpha4}{ts_high} + {memory_alpha5}{val_low} + {memory_alpha6}{val_high})"),
                yul_format!("add(add(add(add(add(add(add(mulmod({memory_alpha6:x}, {val_high:x}, P), mulmod({memory_alpha5:x}, {val_low:x}, P)), mulmod({memory_alpha4:x}, {ts_high:x}, P)), mulmod({memory_alpha3:x}, {ts_low:x}, P)), mulmod({memory_alpha2:x}, {addr_high:x}, P)), mulmod({memory_alpha1:x}, {addr_low:x}, P)), {address_space:x}), {memory_gamma:x})"))
            }
            fn memrelinitparts_to_calldata_inner(timestamp_and_value: &InitsOrTeardownsTimestampAndValue, running_max_group_offsets: &mut (usize, usize, usize, usize)) -> [String; 2] {
                let (running_max_memvar, _running_max_witvar, _running_max_setupvar, _running_max_cachevar) = running_max_group_offsets;
                match timestamp_and_value {
                    InitsOrTeardownsTimestampAndValue::Init => ["".to_string(), "".to_string()],
                    InitsOrTeardownsTimestampAndValue::Teardown { lhs_timestamp: [lhs_ts0, lhs_ts1], lhs_value: [lhs_val0, lhs_val1], rhs_timestamp: [rhs_ts0, rhs_ts1], rhs_value: [rhs_val0, rhs_val1] } => {
                        *running_max_memvar = *lhs_ts0.max(running_max_memvar);
                        *running_max_memvar = *lhs_ts1.max(running_max_memvar);
                        *running_max_memvar = *lhs_val0.max(running_max_memvar);
                        *running_max_memvar = *lhs_val1.max(running_max_memvar);
                        *running_max_memvar = *rhs_ts0.max(running_max_memvar);
                        *running_max_memvar = *rhs_ts1.max(running_max_memvar);
                        *running_max_memvar = *rhs_val0.max(running_max_memvar);
                        *running_max_memvar = *rhs_val1.max(running_max_memvar);
                        [
                            format!("α³[{lhs_ts0}] + α⁴[{lhs_ts1}] + α⁵[{lhs_val0}] + α⁶[{lhs_val1}]"),
                            format!("α³[{rhs_ts0}] + α⁴[{rhs_ts1}] + α⁵[{rhs_val0}] + α⁶[{rhs_val1}]")
                        ]
                    }
                }
            }
            fn lookrelsingle_to_calldata(tuple: &NoFieldSingleColumnLookupRelation, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize)) -> String {
                let NoFieldSingleColumnLookupRelation { input, lookup_set_index: _ } = tuple;
                let compressed = linrel_to_calldata_inner(input, expected_layer, layer0_group_widths, running_max_group_offsets);
                format!("(δ + {compressed})")
            }
            fn lookrelgeneric_to_calldata(tuple: &NoFieldVectorLookupRelation, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize)) -> Dual {
                let NoFieldVectorLookupRelation { columns, lookup_set_index: _ } = tuple;
                assert_eq!(columns.len(), 10, "we expect generic lookups to be tuples of 10 elements");
                let logup_alpha = Dual("β".to_string(), Yul::logup_alpha());
                let compressed = columns.iter().enumerate().rev().map(|(j, column)| {
                    let compressed_column = linrel_to_calldata_inner(column, expected_layer, layer0_group_widths, running_max_group_offsets);
                    let logup_alpha_j = logup_alpha.0.clone() + &superscript(j);
                    Dual(format!("{logup_alpha_j}({compressed_column})"), yul_format!("{compressed_column:x}"))
                }).reduce(|acc, el| Dual(format!("{acc} + {el}"), yul_format!("add(mulmod({acc:x}, {logup_alpha:x}, P), {el:x})"))).unwrap();
                let logup_gamma = Dual("δ".to_string(), Yul::logup_gamma());
                Dual(format!("({logup_gamma} + {compressed})"), yul_format!("add({compressed:x}, {logup_gamma:x})"))
            }
            fn linrel_to_calldata_inner(inputs: &NoFieldLinearRelation, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize)) -> Dual {
                let NoFieldLinearRelation { linear_terms, constant } = inputs;
                let linear = linear_terms.iter().map(|(c, addr)| {
                    let input = gkraddress_to_calldata(addr, expected_layer, layer0_group_widths, running_max_group_offsets);
                    let c = const_to_evm(c);
                    Dual(format!("{c}{input}"), yul_format!("mulmod({c:x}, {input:x}, P)"))
                }).reduce(|acc, el| Dual(format!("{acc} + {el}"), yul_format!("add({acc:x}, {el:x})"))).unwrap_or(Dual("0".to_string(), yul_format!("0")));
                let constant = const_to_evm(constant);
                Dual(format!("{constant} + {linear}"), yul_format!("add({constant:x}, {linear:x})"))
            }
            fn quadrel_to_calldata_inner(input: &NoFieldMaxQuadraticGKRRelation, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize)) -> String {
                let NoFieldMaxQuadraticGKRRelation { quadratic_terms, linear_terms, constant } = input;
                let quadratic = quadratic_terms.iter().map(|(address, linear_terms)| {
                    let read = gkraddress_to_calldata(address, expected_layer, layer0_group_widths, running_max_group_offsets);
                    let linear = linear_terms.iter().map(|(c, address)| {
                        let read = gkraddress_to_calldata(address, expected_layer, layer0_group_widths, running_max_group_offsets);
                        let c = const_to_evm(c);
                        format!("{c}{read}")
                    }).collect::<Vec<_>>().join(" + ");
                    format!("{read}({linear})")
                }).collect::<Vec<_>>().join(" + ");
                let linear = linear_terms.iter().map(|(c, address)| {
                    let read = gkraddress_to_calldata(address, expected_layer, layer0_group_widths, running_max_group_offsets);
                    let c = const_to_evm(c);
                    format!("{c}{read}")
                }).collect::<Vec<_>>().join(" + ");
                let constant = const_to_evm(constant);
                format!("{constant} + {linear} + {quadratic}")
            }
            // fn expression_to_calldata(expression: &NoFieldStructuredExpression, expected_layer: usize, layer0_group_widths: (usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize)) -> String {
            //    match expression {
            //         NoFieldStructuredExpression::Constant(c) => const_to_evm(c),
            //         NoFieldStructuredExpression::Place(address) => gkraddress_to_calldata(address, expected_layer, layer0_group_widths, running_max_group_offsets),
            //         NoFieldStructuredExpression::Sum(terms) => {
            //             let term = terms.iter().map(|expression| {
            //                 expression_to_calldata(expression, expected_layer, layer0_group_widths, running_max_group_offsets)
            //             }).collect::<Vec<_>>().join(" + ");
            //             format!("({term})")
            //         }
            //         NoFieldStructuredExpression::Product(terms) => {
            //             // assert!(terms.len() <= 2, "we dont tolerate degree > 2 expressions");
            //             let num_constants = terms.iter().filter(|term| {
            //                 matches!(term, NoFieldStructuredExpression::Constant(_))
            //             }).count();
            //             assert!(num_constants <= 1); // makes rendering faulty if more
            //             let term = terms.iter().map(|expression| {
            //                 expression_to_calldata(expression, expected_layer, layer0_group_widths, running_max_group_offsets)
            //             }).collect::<Vec<_>>().join("");
            //             term
            //         }
            //    }
            // }


            match enforced_relation {
                // 3
                NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
                    let [[num1, den1], [num2, den2]] = input.each_ref().map(|pair| pair.each_ref().map(|addr| gkraddress_to_calldata(addr, i, layer0_group_widths, &mut running_max_group_offsets)));
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter));
                    // println!("{relation_name}: {num1}/{den1} + {num2}/{den2} = {num_out}/{den_out}");
                    yul_println!("
                    \t{{  // {relation_name}: {num1}/{den1} + {num2}/{den2} = {num_out}/{den_out}
                    \t    let den_out := mulmod({den1:x}, {den2:x}, P)
                    \t    let gate := den_out
                    \t    {pointcheck_update:x}
                    \t    let num_out := add(mulmod({num1:x}, {den2:x}, P), mulmod({num2:x}, {den1:x}, P))
                    \t    gate := num_out
                    \t    {pointcheck_update:x}
                    \t}}");
                }
                NoFieldGKRRelation::CopyInExtensionField { input, output } => {
                    let input = gkraddress_to_calldata(input, i, layer0_group_widths, &mut running_max_group_offsets);
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    // println!("{relation_name}: {input} = {output}");
                    yul_println!("
                    \t{{  // {relation_name}: {input} = {output}
                    \t    let gate := {input:x}
                    \t    {pointcheck_update:x}
                    \t}}");
                }

                // 2
                NoFieldGKRRelation::MaskIntoIdentityProduct { input , mask, output } => {
                    let input = gkraddress_to_calldata(input, i, layer0_group_widths, &mut running_max_group_offsets);
                    let mask = gkraddress_to_calldata(mask, i, layer0_group_widths, &mut running_max_group_offsets);
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    // println!("{relation_name}: {input}*{mask} + (1-{mask}) = {output}");
                    let neg_mask = u128_to_neg(&mask);
                    yul_println!("
                    \t{{  // {relation_name}: {input}*{mask} + (1-{mask}) = {output}
                    \t    let gate := add(mulmod({input:x}, {mask:x}, P), add(1, {neg_mask:x}))
                    \t    {pointcheck_update:x}
                    \t}}");
                }

                // 1
                NoFieldGKRRelation::CopyInBaseField { input, output } => {
                    let input = gkraddress_to_calldata(input, i, layer0_group_widths, &mut running_max_group_offsets);
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    // println!("{relation_name}: {input} = {output}");
                    yul_println!("
                    \t{{  // {relation_name}: {input} = {output}
                    \t    let gate := {input:x}
                    \t    {pointcheck_update:x}
                    \t}}");
                }
                NoFieldGKRRelation::TrivialProduct { input, output } => {
                    let [lhs, rhs] = input.each_ref().map(|addr| gkraddress_to_calldata(addr, i, layer0_group_widths, &mut running_max_group_offsets));
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    // println!("{relation_name}: {lhs}*{rhs} = {output}");
                    yul_println!("
                    \t{{  // {relation_name}: {lhs}*{rhs} = {output}
                    \t    let gate := mulmod({lhs:x}, {rhs:x}, P)
                    \t    {pointcheck_update:x}
                    \t}}");
                }
                NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs { input, remainder, output } => {
                    let [num, den] = input.each_ref().map(|addr| gkraddress_to_calldata(addr, i, layer0_group_widths, &mut running_max_group_offsets));
                    let remainder = gkraddress_to_calldata(remainder, i, layer0_group_widths, &mut running_max_group_offsets);
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter));
                    let logup_gamma = Dual("δ".to_string(), Yul::logup_gamma());
                    // println!("{relation_name}: {num}/{den} + 1/({logup_gamma} + {remainder}) = {num_out}/{den_out}");
                    yul_println!("
                    \t{{  // {relation_name}: {num}/{den} + 1/({logup_gamma} + {remainder}) = {num_out}/{den_out}
                    \t    let den_out := mulmod({den:x}, add({logup_gamma:x}, {remainder:x}), P)
                    \t    let gate := den_out
                    \t    {pointcheck_update:x}
                    \t    let num_out := add(mulmod({num:x}, add({logup_gamma:x}, {remainder:x}), P), {den:x})
                    \t    gate := num_out
                    \t    {pointcheck_update:x}
                    \t}}");
                }
                // (unified)
                NoFieldGKRRelation::LookupPairFromVectorInputs { input, output } => {
                    let [den1, den2] = input.each_ref().map(|input| lookrelgeneric_to_calldata(input, i, layer0_group_widths, &mut running_max_group_offsets));
                    let [num_out, den_out] = output.each_ref_mayberevmap(|address| gkraddress_to_outputvar(address, i + 1, &mut running_output_counter));
                    // println!("{relation_name}: 1/{den1} + 1/{den2} = {num_out}/{den_out}");
                    yul_println!("
                    \t{{  // {relation_name}: 1/{den1} + 1/{den2} = {num_out}/{den_out}
                    \t    let den_out := mulmod({den1:x}, {den2:x}, P)
                    \t    let gate := den_out
                    \t    {pointcheck_update:x}
                    \t    let num_out := add({den1:x}, {den2:x})
                    \t    gate := num_out
                    \t    {pointcheck_update:x}
                    \t}}");
                }
                NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs { input, remainder, output } => {
                    let [num1, den1] = input.each_ref().map(|address| gkraddress_to_calldata(address, i, layer0_group_widths, &mut running_max_group_offsets));
                    let den2 = lookrelgeneric_to_calldata(remainder, i, layer0_group_widths, &mut running_max_group_offsets);
                    let [num_out, den_out] = output.each_ref_mayberevmap(|address| gkraddress_to_outputvar(address, i + 1, &mut running_output_counter));
                    // println!("{relation_name}: {num1}/{den1} + 1/{den2} = {num_out}/{den_out}")
                    yul_println!("
                    \t{{  // {relation_name}: {num1}/{den1} + 1/{den2} = {num_out}/{den_out}
                    \t    let den_out := mulmod({den1:x}, {den2:x}, P)
                    \t    let gate := den_out
                    \t    {pointcheck_update:x}
                    \t    let num_out := add(mulmod({num1:x}, {den2:x}, P), {den1:x})
                    \t    gate := num_out
                    \t    {pointcheck_update:x}
                    \t}}");
                }

                // 0
                NoFieldGKRRelation::InitialGrandProductWithoutCaches { input, output } => {
                    let [lhs, rhs] = input.each_ref().map(|contribution| memrel_to_calldata(contribution, &mut running_max_group_offsets));
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    // println!("{relation_name}: {lhs}*{rhs} = {output}");
                    yul_println!("
                    \t{{  // {relation_name}: {lhs}*{rhs} = {output}
                    \t    let gate := mulmod({lhs:x}, {rhs:x}, P)
                    \t    {pointcheck_update:x}
                    \t}}");
                }
                NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup { input, setup, output } => {
                    let input = gkraddress_to_calldata(input, i, layer0_group_widths, &mut running_max_group_offsets);
                    let [multiplicity, setup] = setup.each_ref().map(|address| gkraddress_to_calldata(address, i, layer0_group_widths, &mut running_max_group_offsets));
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter));
                    println!("{relation_name}: 1/(δ + {input}) - {multiplicity}/(δ + {setup}) = {num_out}/{den_out}");
                }
                NoFieldGKRRelation::LookupPairFromBaseInputs { input, output, range_check_width: _ } => {
                    let [den1, den2] = input.each_ref().map(|relation| lookrelsingle_to_calldata(relation, i, layer0_group_widths, &mut running_max_group_offsets));
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter));
                    println!("{relation_name}: 1/{den1} + 1/{den2} = {num_out}/{den_out}");
                }
                NoFieldGKRRelation::MaterializeSingleLookupInput { input, output, range_check_width: _ } => {
                    let NoFieldSingleColumnLookupRelation{ input, lookup_set_index: _ }  = input;
                    let compressed_tuple = linrel_to_calldata_inner(input, i, layer0_group_widths, &mut running_max_group_offsets);
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    println!("{relation_name}: {compressed_tuple} = {output}");
                }
                // NoFieldGKRRelation::LookupWithDensAndCachedSetup { input, setup, output } => {
                NoFieldGKRRelation::LookupWithDensAndSetupExpressions { input, setup, output } => {
                    let (input_mask, input_den) = input;
                    let (setup_multiplicity, setup_terms) = setup;
                    let input_mask = gkraddress_to_calldata(input_mask, i, layer0_group_widths, &mut running_max_group_offsets);
                    let input_den = lookrelgeneric_to_calldata(input_den, i, layer0_group_widths, &mut running_max_group_offsets);
                    let setup_multiplicity = gkraddress_to_calldata(setup_multiplicity, i, layer0_group_widths, &mut running_max_group_offsets);
                    let setup = setup_terms.iter().enumerate().map(|(j, addr)| {
                        let input = gkraddress_to_calldata(addr, i, layer0_group_widths, &mut running_max_group_offsets);
                        let beta_j = "β".to_string() + &superscript(j);
                        format!("{beta_j}{input}")
                    }).collect::<Vec<_>>().join(" + ");
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter));
                    println!("{relation_name}: {input_mask}/{input_den} - {setup_multiplicity}/(δ + {setup}) = {num_out}/{den_out}");
                }
                // NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input, expression } => {
                NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input } => {
                    let input = quadrel_to_calldata_inner(input, i, layer0_group_widths, &mut running_max_group_offsets);
                    // let expression = expression_to_calldata(expression, i, layer0_group_widths, &mut running_max_group_offsets);
                    println!("{relation_name}: 0 == {input}");
                }
                // (unified)
                NoFieldGKRRelation::InitsOrTeardownsInitialPair { timestamp_and_value, setup, output, set_idxes } => {
                    let [setup_low, setup_high] = setup.each_ref().map(|address| gkraddress_to_calldata(address, i, layer0_group_widths, &mut running_max_group_offsets));
                    let high_bits_shift = prover::gkr::high_bits_offset_for_inits_and_teardowns::<2>(1 << 24);
                    let top_bits = set_idxes.map(|c| c << high_bits_shift);
                    let [read_addr_high, write_addr_high] = top_bits.map(|c| format!("α²({setup_high} + {c})"));
                    let [read_timestamp_and_value, write_timestamp_and_value] = memrelinitparts_to_calldata_inner(timestamp_and_value, &mut running_max_group_offsets);
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    let address_space = AddressSpaceType::RAM as u32;
                    let shared = format!("γ + {address_space} + α{setup_low}");
                    println!("{relation_name}: ({shared} + {read_addr_high} + {read_timestamp_and_value})*({shared} + {write_addr_high} + {write_timestamp_and_value}) = {output}")
                }
                NoFieldGKRRelation::MaxQuadratic { input, output } => {
                    let input = quadrel_to_calldata_inner(input, i, layer0_group_widths, &mut running_max_group_offsets);
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    println!("{relation_name}: {input} = {output}")
                    // TODO: DO NOT FORGET TO INSTANTIATE CACHES
                }

                _ => todo!("could not match {enforced_relation:?} at layer {i}")
            }
        }

        assert_eq!(running_output_counter, if DEBUG_NATURAL_GATE_ORDER { previous_input_count } else { 0 });
        if i > 0 {
            previous_input_count = intermediate_layer_width.unwrap();
            assert!(cached_relations.len() == 0);
        } else {
            let (l0_memvars, l0_witvars, l0_setupvars, l0_cachevars) = layer0_group_widths;
            let (running_max_memvar, running_max_witvar, running_max_setupvar, running_max_cachevar) = running_max_group_offsets;
            // `running_max_*` stays 0 whether offset 0 was seen or the group is
            // empty, so only enforce `max + 1 == width` for non-empty groups.
            let assert_group_width = |running_max: usize, width: usize| {
                if width == 0 { assert_eq!(running_max, 0); } else { assert_eq!(running_max + 1, width); }
            };
            assert_group_width(running_max_memvar, l0_memvars);
            assert_group_width(running_max_witvar, l0_witvars);
            assert_group_width(running_max_setupvar, l0_setupvars);
            assert_group_width(running_max_cachevar, l0_cachevars + injected_virtualpoly_relations.len());
        }


        let check = if DEBUG_ENABLE_DUMMY_CHECKS {
            yul_format!("
            let dummy_check := mod(add(claim, sub(P, rhs_scaled)), P)
            \tmstore(CIRCUIT_CACHE_PTR, dummy_check)
            ")
        } else {
            yul_format!("
            if mod(add(claim, sub(P, rhs_scaled)), P) {{ revert(0, 0) }}
            ")
        };
        yul_println!("
            let rhs_scaled := mulmod(acc, eq_scale, P)
            // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
            {check:x}
            // after stack-heavy values are dead
            // if mload(CIRCUIT_CACHE_PTR) {{ revert(0, 0) }}

            // POINT CLAIMS BATCH ({previous_input_count} POINTS)
            let points := {previous_input_count}
            let is_odd := mod(points, 2)
            if is_odd {{
                next_claim := shr(128, calldataload(add(ptr, mul(16, sub(points, 1)))))
            }}
            next_alpha := transcript{previous_input_count}to1(ptr)
            let even_points := sub(points, is_odd)
            let pairs := shr(1, even_points)
            for {{ let pair := sub(pairs, 1) }} lt(pair, pairs) {{ pair := sub(pair, 1) }} {{
                let word := calldataload(add(ptr, mul(pair, 32)))
                let el1 := and(MASK, word)
                next_claim := add(mulmod(next_claim, next_alpha, P), el1)
                let el0 := shr(128, word)
                next_claim := add(mulmod(next_claim, next_alpha, P), el0)
            }}

            next_ptr := add(ptr, mul(16, points))
        }}
        ");
        if !collected_previous_input_counts.contains(&previous_input_count) {
            yul_println!("
            function transcript{previous_input_count}to1(ptr) -> alpha {{
                let input_bytes := mul({previous_input_count}, 16)
                calldatacopy(add(SEED_PTR, 32), ptr, input_bytes)
                let seed := keccak256(SEED_PTR, add(32, input_bytes))
                mstore(SEED_PTR, seed)
                alpha := shr(128, seed)
            }}
            ");
        } else {
            yul_println!("
            // SKIPPING TRANSCRIPT FN transcript{previous_input_count}to1 FOR LAYER {i} -- ALREADY AVAILABLE
            ");
        }
        collected_previous_input_counts.push(previous_input_count);

        // if i <= 1 {
        //     break
        // }
    }
}
