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
use field::baby_bear::base::BabyBearField;

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
impl std::fmt::Octal for Dual {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.1.fmt(f)
    }
}
impl std::fmt::LowerExp for Dual {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.1.fmt(f)
    }
}
impl std::fmt::Binary for Dual {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.1.fmt(f)
    }
}
impl std::fmt::Pointer for Dual {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.1.fmt(f)
    }
}

impl std::fmt::LowerHex for Yul {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.0, f)
    }
}
impl std::fmt::Octal for Yul {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.calldataload_idx(), f)
    }
}
impl std::fmt::LowerExp for Yul {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.mload_idx(), f)
    }
}
impl std::fmt::Binary for Yul {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.cfg_id(), f)
    }
}
impl std::fmt::Pointer for Yul {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.mem_pack(), f)
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
        yul_format!("shr(128, calldataload(add(ptr, mul(16, {idx}))))")
    }
    fn mload(idx: &usize) -> Self {
        yul_format!("mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, {idx})))")
    }
    fn calldataload_idx(&self) -> usize {
        let s = self.0.trim();
        let prefix = "shr(128, calldataload(add(ptr, mul(16, ";
        let suffix = "))))";
        let idx = s
            .strip_prefix(prefix)
            .and_then(|s| s.strip_suffix(suffix))
            .unwrap_or_else(|| panic!("expected simple calldata load, got: {s}"));
        assert!(
            idx.chars().all(|c| c.is_ascii_digit()),
            "expected literal calldata index, got: {idx}"
        );
        idx.parse().unwrap()
    }
    fn mload_idx(&self) -> usize {
        let s = self.0.trim();
        let prefix = "mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, ";
        let suffix = ")))";
        let idx = s
            .strip_prefix(prefix)
            .and_then(|s| s.strip_suffix(suffix))
            .unwrap_or_else(|| panic!("expected simple cache load, got: {s}"));
        assert!(
            idx.chars().all(|c| c.is_ascii_digit()),
            "expected literal cache index, got: {idx}"
        );
        idx.parse().unwrap()
    }
    fn cfg_id(&self) -> usize {
        let s = self.0.trim();
        let prefix1 = "lookrelgeneric_from_cfg(ptr, ";
        let prefix2 = "lookrelsingle_from_cfg(ptr, ";
        let prefix3 = "linrel_from_cfg(ptr, ";
        let prefix4 = "quadrel_from_cfg(ptr, ";
        let suffix = ")";
        let id = s
            .strip_prefix(prefix1)
            .or_else(|| s.strip_prefix(prefix2))
            .or_else(|| s.strip_prefix(prefix3))
            .or_else(|| s.strip_prefix(prefix4))
            .and_then(|s| s.strip_suffix(suffix))
            .unwrap_or_else(|| panic!("expected cfg wrapper call, got: {s}"));
        assert!(
            id.chars().all(|c| c.is_ascii_digit()),
            "expected literal cfg id, got: {id}"
        );
        id.parse().unwrap()
    }
    fn mem_pack(&self) -> &str {
        let s = self.0.trim();
        let prefix1 = "memrel_from_pack(ptr, ";
        let prefix2 = "memrelinitpart_from_pack(ptr, ";
        let suffix = ")";
        s.strip_prefix(prefix1)
            .or_else(|| s.strip_prefix(prefix2))
            .and_then(|s| s.strip_suffix(suffix))
            .unwrap_or_else(|| panic!("expected memory pack wrapper call, got: {s}"))
    }
    fn mstore(idx: &usize) -> Self {
        yul_format!("mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, {idx})), mod(gate, P))") // mod to prevent overflows with pointcheck const-cache multiplications
    }
    fn logup_gamma() -> Self {
        yul_format!("mload(add(LOGUP_CHALLS_PTR(), 32))")
    }
    fn logup_alpha() -> Self {
        yul_format!("mload(LOGUP_CHALLS_PTR())")
    }
    fn memory_gamma() -> Self {
        yul_format!("mload(add(MEMORY_CHALLS_PTR(), mul(32, 6)))")
    }
    fn memory_alpha(idx: usize) -> Self {
        match idx {
            0..6 => yul_format!("mload(add(MEMORY_CHALLS_PTR(), mul(32, {idx})))"),
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
    assert!(*c < (1<<31));
    // first check if negative
    let (sign, modc, yul) = if *c > BabyBearField::ORDER / 2 {
        let modc = BabyBearField::ORDER - c;
        assert!(modc < (1<<30));
        ("-", modc, yul_format!("sub(P, {modc})"))
    } else { 
        assert!(*c < (1<<30));
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
fn const_to_pack(c: &u32) -> Dual {
    let c = const_to_evm(c);
    if c.1.0.starts_with("sub(P, ") { // avoid overflows
        let modc = c.1.0.strip_circumfix("sub(P, ", ")").unwrap();
        Dual(format!("-{modc}"), yul_format!("add({modc}, shl(30, 1))"))
    } else {
        c
    }
}

fn main() {
    const DEBUG_ENABLE_DUMMY_CHECKS: bool = false;
    let json = std::fs::read_to_string(
        // "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
        // "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json",
        "../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json",
        // "../cs/compiled_circuits/unified_reduced_machine_layout_gkr.json",
    )
    .unwrap();
    let circuit: GKRCircuitArtifact<BabyBearField> = serde_json::from_str(&json).unwrap();
    let circuit_rounds = {
        assert!(circuit.trace_len.is_power_of_two() && circuit.trace_len > 0);
        assert_eq!(circuit.trace_len, 1<<24, "we need to keep sync with gkr.sol constant!");
        circuit.trace_len.trailing_zeros()
    };
    let gkr_sol_rounds = include_str!("gkr.sol")
        .lines()
        .find_map(|line| line.trim().strip_prefix("uint256 constant GKR_CIRCUIT_LAYER_ROUNDS = ")?.strip_suffix(";")?.parse::<u32>().ok())
        .expect("GKR_CIRCUIT_LAYER_ROUNDS not found");
    assert_eq!(circuit_rounds, gkr_sol_rounds, "inconsistent layer rounds/sizes, either fix the circuit json or GKR_CIRCUIT_LAYER_ROUNDS const in gkr.sol");
    let layer0_group_widths = (circuit.memory_layout.total_width, circuit.witness_layout.total_width, circuit.generic_lookup_tables_width, circuit.layers[0].cached_relations.len());
    // let mut previous_input_count = 8;
    let mut previous_input_count = 10; // TEMPORARY: unified adds another product pair for inits/teardowns
    let mut cfg = vec![]; // collects dynamic input configurations across layers for certain gates with variable inputs
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
        yul_println!("
        function sumcheck_circuit_layer{i}(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {{
            // SUMCHECK ROUNDS
            let eq_scale
            // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
            ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
            
            // POINT CHECK
            let acc");
        let mut running_max_group_offsets = (0, 0, 0, 0);
        let mut running_cachedoutput_counter = 0;
        for (cached_address, cached_relation) in cached_relations {
            let output = gkraddress_to_outputvar(cached_address, i, &mut running_cachedoutput_counter);
            let relation_name = serde_json::to_value(cached_relation).unwrap().as_object().unwrap().keys().next().unwrap().clone();

            fn gkraddress_to_calldata(address: &GKRAddress, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize)) -> Dual {
                let (l0_memvars, l0_witvars, _l0_setupvars, _l0_cachevars) = layer0_group_widths;
                let (_running_max_memvar, _running_max_witvar, running_max_setupvar, _running_max_cachevar) = running_max_group_offsets;
                match address {
                    // InnerLayer { layer, offset } if *layer==expected_layer && expected_layer > 0 => {
                    //     Dual(format!("[{offset}]"), Yul::calldataload(offset))
                    // },
                    // GKRAddress::BaseLayerMemory(offset) if expected_layer == 0 => {
                    //     *running_max_memvar = *offset.max(running_max_memvar);
                    //     let calldata_offset = offset; // memory is first in calldata
                    //     Dual(format!("[{calldata_offset}]"), Yul::calldataload(calldata_offset))
                    // },
                    // GKRAddress::BaseLayerWitness(offset) if expected_layer == 0 => {
                    //     *running_max_witvar = *offset.max(running_max_witvar);
                    //     let calldata_offset = l0_memvars + offset; // witness is second in calldata
                    //     Dual(format!("[{calldata_offset}]"), Yul::calldataload(&calldata_offset))
                    // },
                    GKRAddress::Setup(offset) if expected_layer == 0 => {
                        *running_max_setupvar = *offset.max(running_max_setupvar);
                        let calldata_offset = l0_memvars + l0_witvars + offset; // setup is third in calldata
                        Dual(format!("[{calldata_offset}]"), Yul::calldataload(&calldata_offset))
                    },
                    // GKRAddress::Cached { layer, offset } if *layer==expected_layer && expected_layer == 0 => {
                    //     *running_max_cachevar = *offset.max(running_max_cachevar);
                    //     Dual(format!("Cache({offset})"), Yul::mload(offset))
                    // },
                    // GKRAddress::VirtualSetup(virtual_poly) if expected_layer == 0 => {
                    //     let cache_idx = l0_cachevars + *virtual_poly as usize;
                    //     *running_max_cachevar = cache_idx.max(*running_max_cachevar);
                    //     Dual(format!("Cache({cache_idx})"), Yul::mload(&cache_idx))
                    // }
                    // GKRAddress::VirtualSetup(virtual_poly) => format!("VirtualSetup{setup:?}(x)")
                    _ => todo!("unexpected address {address:?} for layer {expected_layer}")
                }
            }
            fn gkraddress_to_outputvar(address: &GKRAddress, expected_layer: usize, running_cachedoutput_counter: &mut usize) -> Dual {
                match address {
                    GKRAddress::Cached { layer, offset } if *layer==expected_layer && expected_layer == 0 && *running_cachedoutput_counter == *offset => {
                        *running_cachedoutput_counter += 1;
                        Dual(format!("Cache({offset})"), Yul::mstore(offset))
                    },
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
                    let logup_alpha = Dual("β".to_string(), Yul::logup_alpha());
                    let setup = {
                        let [set0, set1, set2, set3, set4, set5, set6, set7, set8, set9] = terms.iter().enumerate().map(|(j, addr)| {
                            let input = gkraddress_to_calldata(addr, i, layer0_group_widths, &mut running_max_group_offsets);
                            let beta_j = logup_alpha.0.clone() + &superscript(j);
                            Dual(format!("{beta_j}{input}"), yul_format!("{input:x}"))
                        }).collect::<Vec<_>>().try_into().ok().unwrap();
                        Dual(
                            format!("{set0} + {set1} + {set2} + {set3} + {set4} + {set5} + {set6} + {set7} + {set8} + {set9}"),
                            yul_format!("gkr_lookrel_compress_half(gkr_lookrel_compress_half(0, {set5:x}, {set6:x}, {set7:x}, {set8:x}, {set9:x}), {set0:x}, {set1:x}, {set2:x}, {set3:x}, {set4:x})")
                        )
                    };
                    // println!("{relation_name}: {setup} = {output}");
                    yul_println!("
                    \t{{  // {relation_name}: {setup} = {output}
                    \t    let gate := {setup:x}
                    \t    {output:x}
                    \t}}");
                }
                _ => todo!("could not match (cached) {cached_relation:?} at layer {i}")
            }
        }
        // INJECT VIRTUAL POLY CACHES
        let injected_virtualpoly_relations = [
            VirtualSetupPoly::RangeCheck16Bits,
            VirtualSetupPoly::RangeCheckTimestamp,
            VirtualSetupPoly::InitsAndTeardownsLow, // (unified)
            VirtualSetupPoly::InitsAndTeardownsHigh, // (unified)
        ];
        if i == 0 {
            for virtualpoly_relation in injected_virtualpoly_relations {
                let cache_idx = running_cachedoutput_counter + virtualpoly_relation as usize;
                let output = Dual(format!("Cache({cache_idx})"), Yul::mstore(&cache_idx));
                let relation_name = format!("{virtualpoly_relation:?}");
                match virtualpoly_relation {
                    VirtualSetupPoly::RangeCheck16Bits => {
                        assert!(16 <= circuit_rounds);
                        // println!("{relation_name}: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8])(1 - r[7])(1 - r[6])(1 - r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = {output}");
                        yul_println!("
                        \t{{  // {relation_name}: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8])(1 - r[7])(1 - r[6])(1 - r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = {output}
                        \t    let gate := gkr_virtual_poly_rangecheck(16)
                        \t    {output:x}
                        \t}}");
                    }
                    VirtualSetupPoly::RangeCheckTimestamp => {
                        let timestamp_range_bits = cs::definitions::TIMESTAMP_COLUMNS_NUM_BITS;
                        assert!(timestamp_range_bits <= circuit_rounds);
                        // println!("{relation_name}: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8] + 2^16 r[7] + 2^17 r[6] + 2^18 r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = {output}");
                        yul_println!("
                        \t{{  // {relation_name}: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8] + 2^16 r[7] + 2^17 r[6] + 2^18 r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = {output}
                        \t    let gate := gkr_virtual_poly_rangecheck({timestamp_range_bits})
                        \t    {output:x}
                        \t}}");
                    }
                    VirtualSetupPoly::InitsAndTeardownsLow => {
                        assert_eq!(circuit.memory_layout.inits_and_teardowns_word_bits.unwrap(), 2, "we expect there to be just 2 empty inits/teardowns low bits");
                        let low_bits = 16 - 2;
                        assert!(low_bits <= circuit_rounds);
                        // println!("{relation_name}: 4(2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10]) = {output}");
                        yul_println!("
                        \t{{  // {relation_name}: 4(2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10]) = {output}
                        \t    let gate := mul(4, gkr_virtual_poly_compose_vars({low_bits}, 0)) // u32 word-aligned
                        \t    {output:x}
                        \t}}");
                    }
                    VirtualSetupPoly::InitsAndTeardownsHigh => {
                        assert_eq!(circuit.memory_layout.inits_and_teardowns_word_bits.unwrap(), 2, "we expect there to be just 2 empty inits/teardowns low bits");
                        let low_bits = 16 - 2;
                        assert!(low_bits <= circuit_rounds);
                        let high_bits = circuit_rounds - low_bits;
                        assert_eq!(high_bits, prover::gkr::high_bits_offset_for_inits_and_teardowns::<2>(circuit.trace_len));
                        // println!("{relation_name}: 2^0 r[9] + 2^1 r[8] + 2^2 r[7] + 2^3 r[6] + 2^4 r[5] + 2^5 r[4] + 2^6 r[3] + 2^7 r[2] + 2^8 r[1] + 2^9 r[0] = {output}");
                        yul_println!("
                        \t{{  // {relation_name}: 2^0 r[9] + 2^1 r[8] + 2^2 r[7] + 2^3 r[6] + 2^4 r[5] + 2^5 r[4] + 2^6 r[3] + 2^7 r[2] + 2^8 r[1] + 2^9 r[0] = {output}
                        \t    let gate := gkr_virtual_poly_compose_vars({high_bits}, {low_bits})
                        \t    {output:x}
                        \t}}");
                    }
                }
            }
        }
        const DEBUG_NATURAL_GATE_ORDER: bool = false;
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
                        assert!(*offset < (1<<7), "we expect inner layer offsets to be 7 bits, but we got {offset} for layer {expected_layer}");
                        Dual(format!("[{offset}]"), Yul::calldataload(offset))
                    },
                    GKRAddress::BaseLayerMemory(offset) if expected_layer == 0 => {
                        *running_max_memvar = *offset.max(running_max_memvar);
                        let calldata_offset = offset; // memory is first in calldata
                        assert!(*calldata_offset < (1<<7), "we expect inner layer offsets to be 7 bits, but we got {offset} for layer {expected_layer}");
                        Dual(format!("[{calldata_offset}]"), Yul::calldataload(calldata_offset))
                    },
                    GKRAddress::BaseLayerWitness(offset) if expected_layer == 0 => {
                        *running_max_witvar = *offset.max(running_max_witvar);
                        let calldata_offset = l0_memvars + offset; // witness is second in calldata
                        assert!(calldata_offset < (1<<7), "we expect inner layer offsets to be 7 bits, but we got {offset} for layer {expected_layer}");
                        Dual(format!("[{calldata_offset}]"), Yul::calldataload(&calldata_offset))
                    },
                    GKRAddress::Setup(offset) if expected_layer == 0 => {
                        *running_max_setupvar = *offset.max(running_max_setupvar);
                        let calldata_offset = l0_memvars + l0_witvars + offset; // setup is third in calldata
                        assert!(calldata_offset < (1<<7), "we expect inner layer offsets to be 7 bits, but we got {offset} for layer {expected_layer}");
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
                    CompiledAddressSpaceRelationStrict::Constant(c) => {
                        assert!(*c <= 2, "we expect addr_space in [0,1,2] but got {c}");
                        let c = const_to_evm(c);
                        Dual(format!("{c}"), yul_format!("shl(1, {c:x})"))
                    },
                    CompiledAddressSpaceRelationStrict::IsRam(idx) => {
                        assert!(*idx < (1<<7), "we expect layer offsets to be 7 bits, but we got {idx} for layer0");
                        *running_max_memvar = *idx.max(running_max_memvar);
                        let var = Dual(format!("[{idx}]"), Yul::calldataload(idx));
                        Dual(format!("{var}"), yul_format!("add(1, shl(1, {var:o}))"))
                    },
                    CompiledAddressSpaceRelationStrict::IsRegister(idx) => {
                        assert!(*idx < (1<<7), "we expect layer offsets to be 7 bits, but we got {idx} for layer0");
                        *running_max_memvar = *idx.max(running_max_memvar);
                        let var = Dual(format!("[{idx}]"), Yul::calldataload(idx));
                        let negvar = u128_to_neg(&var);
                        Dual(format!("(1 + {negvar})"), yul_format!("add(1, shl(1, add({var:o}, shl(7, 1))))"))
                    },
                };
                let [addr_low, addr_high] = match address {
                    CompiledAddressStrict::Constant(c) => {
                        assert!(*c < (1<<16), "with {address:?} we expect c < 2^16");
                        let c = const_to_evm(c);
                        let zero = Dual(format!("0"), yul_format!("0"));
                        [Dual(format!("{c}"), yul_format!("shl(1, {c:x})")), zero]
                    },
                    CompiledAddressStrict::ConstantU16(c) => {
                        let c = const_to_evm(&(*c as u32));
                        let zero = Dual(format!("0"), yul_format!("0"));
                        [Dual(format!("{c}"), yul_format!("shl(1, {c:x})")), zero]
                    },
                    CompiledAddressStrict::U16Space(idx) => {
                        assert!(*idx < (1<<7), "we expect layer offsets to be 7 bits, but we got {idx} for layer0");
                        *running_max_memvar = *idx.max(running_max_memvar);
                        let var = Dual(format!("[{idx}]"), Yul::calldataload(idx));
                        let zero = Dual(format!("0"), yul_format!("0"));
                        [Dual(format!("{var}"), yul_format!("add(1, shl(1, {var:o}))")), zero]
                    },
                    CompiledAddressStrict::U32Space([low, high]) => {
                        assert!(*low < (1<<7), "we expect layer offsets to be 7 bits, but we got {low} for layer0");
                        assert!(*high < (1<<7), "we expect layer offsets to be 7 bits, but we got {high} for layer0");
                        *running_max_memvar = *low.max(running_max_memvar);
                        *running_max_memvar = *high.max(running_max_memvar);
                        let low = Dual(format!("[{low}]"), Yul::calldataload(low));
                        let high = Dual(format!("[{high}]"), Yul::calldataload(high));
                        [Dual(format!("{low}"), yul_format!("add(1, shl(1, add({low:o}, shl(7, add(1, shl(1, {high:o}))))))")), high]
                    },
                    _ => todo!()
                };
                let [ts_low, ts_high] = match timestamp {
                    CompiledMemoryTimestamp::Zero => {
                        assert_eq!(*timestamp_offset, 0, "with {timestamp:?} we expect timestamp_offset == 0");
                        let zero1 = Dual(format!("0"), yul_format!("0"));
                        let zero2 = Dual(format!("0"), yul_format!("0"));
                        [Dual(format!("{zero1}"), yul_format!("shl(1, {zero1:x})")), zero2]
                    },
                    CompiledMemoryTimestamp::Normal([low, high]) => {
                        assert!(*low < (1<<7), "we expect layer offsets to be 7 bits, but we got {low} for layer0");
                        assert!(*high < (1<<7), "we expect layer offsets to be 7 bits, but we got {high} for layer0");
                        *running_max_memvar = *low.max(running_max_memvar);
                        *running_max_memvar = *high.max(running_max_memvar);
                        assert!(*timestamp_offset < 4, "we expect timestamp_offset < 4 but got {timestamp:?}");
                        let timestamp_offset = const_to_evm(timestamp_offset);
                        let low = Dual(format!("[{low}]"), Yul::calldataload(low));
                        let high = Dual(format!("[{high}]"), Yul::calldataload(high));
                        [Dual(format!("({timestamp_offset} + {low})"), yul_format!("add(1, shl(1, add({timestamp_offset:x}, shl(2, add({low:o}, shl(7, {high:o}))))))")), high]
                    }
                };
                let [val_low, val_high] = match value {
                    RamWordRepresentation::Zero => {
                        let zero1 = Dual(format!("0"), yul_format!("0"));
                        let zero2 = Dual(format!("0"), yul_format!("0"));
                        [Dual(format!("{zero1}"), yul_format!("shl(1, {zero1:x})")), zero2]
                    },
                    RamWordRepresentation::U16Limbs([low, high]) => {
                        assert!(*low < (1<<7), "we expect layer offsets to be 7 bits, but we got {low} for layer0");
                        assert!(*high < (1<<7), "we expect layer offsets to be 7 bits, but we got {high} for layer0");
                        *running_max_memvar = *low.max(running_max_memvar);
                        *running_max_memvar = *high.max(running_max_memvar);
                        let low = Dual(format!("[{low}]"), Yul::calldataload(low));
                        let high = Dual(format!("[{high}]"), Yul::calldataload(high));
                        [Dual(format!("{low}"), yul_format!("add(1, shl(2, add({low:o}, shl(7, {high:o}))))")), high]
                    },
                    RamWordRepresentation::U8Limbs([ll, lh, hl, hh]) => {
                        assert!(*ll < (1<<7), "we expect layer offsets to be 7 bits, but we got {ll} for layer0");
                        assert!(*lh < (1<<7), "we expect layer offsets to be 7 bits, but we got {lh} for layer0");
                        assert!(*hl < (1<<7), "we expect layer offsets to be 7 bits, but we got {hl} for layer0");
                        assert!(*hh < (1<<7), "we expect layer offsets to be 7 bits, but we got {hh} for layer0");
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
                        [Dual(format!("{low}"), yul_format!("add(3, shl(2, add(add({ll:o}, shl(7, {hl:o})), shl(14, add({lh:o}, shl(7, {hh:o}))))))")), high]
                    }
                };
                let memory_gamma = Dual(format!("γ"), Yul::memory_gamma());
                let memory_alpha1 = Dual(format!("α"), Yul::memory_alpha(0));
                let memory_alpha2 = Dual(format!("α²"), Yul::memory_alpha(1));
                let memory_alpha3 = Dual(format!("α³"), Yul::memory_alpha(2));
                let memory_alpha4 = Dual(format!("α⁴"), Yul::memory_alpha(3));
                let memory_alpha5 = Dual(format!("α⁵"), Yul::memory_alpha(4));
                let memory_alpha6 = Dual(format!("α⁶"), Yul::memory_alpha(5));
                Dual(
                    format!("({memory_gamma} + {address_space} + {memory_alpha1}{addr_low} + {memory_alpha2}{addr_high} + {memory_alpha3}{ts_low} + {memory_alpha4}{ts_high} + {memory_alpha5}{val_low} + {memory_alpha6}{val_high})"),
                    yul_format!("memrel_from_pack(ptr, add({address_space:x}, shl(9, add({addr_low:x}, shl(17, add({ts_low:x}, shl(17, {val_low:x})))))))")
                )

            }
            fn memrelinitparts_to_calldata_inner(timestamp_and_value: &InitsOrTeardownsTimestampAndValue, running_max_group_offsets: &mut (usize, usize, usize, usize)) -> [Dual; 2] {
                let (running_max_memvar, _running_max_witvar, _running_max_setupvar, _running_max_cachevar) = running_max_group_offsets;
                match timestamp_and_value {
                    InitsOrTeardownsTimestampAndValue::Init => {
                        let zero1 = Dual(format!("0"), yul_format!("0"));
                        let zero2 = Dual(format!("0"), yul_format!("0"));
                        let lhs_pack = yul_format!("shl(1, {zero1:x})");
                        let rhs_pack = yul_format!("shl(1, {zero2:x})");
                        [
                            Dual(format!("{zero1}"), yul_format!("memrelinitpart_from_pack(ptr, {lhs_pack:x})")), 
                            Dual(format!("{zero2}"), yul_format!("memrelinitpart_from_pack(ptr, {rhs_pack:x})")), 
                        ]
                    },
                    InitsOrTeardownsTimestampAndValue::Teardown { lhs_timestamp: [lhs_ts0, lhs_ts1], lhs_value: [lhs_val0, lhs_val1], rhs_timestamp: [rhs_ts0, rhs_ts1], rhs_value: [rhs_val0, rhs_val1] } => {
                        assert!(*lhs_ts0 < (1<<7), "we expect layer offsets to be 7 bits, but we got {lhs_ts0} for layer0");
                        assert!(*lhs_ts1 < (1<<7), "we expect layer offsets to be 7 bits, but we got {lhs_ts1} for layer0");
                        assert!(*lhs_val0 < (1<<7), "we expect layer offsets to be 7 bits, but we got {lhs_val0} for layer0");
                        assert!(*lhs_val1 < (1<<7), "we expect layer offsets to be 7 bits, but we got {lhs_val1} for layer0");
                        assert!(*rhs_ts0 < (1<<7), "we expect layer offsets to be 7 bits, but we got {rhs_ts0} for layer0");
                        assert!(*rhs_ts1 < (1<<7), "we expect layer offsets to be 7 bits, but we got {rhs_ts1} for layer0");
                        assert!(*rhs_val0 < (1<<7), "we expect layer offsets to be 7 bits, but we got {rhs_val0} for layer0");
                        assert!(*rhs_val1 < (1<<7), "we expect layer offsets to be 7 bits, but we got {rhs_val1} for layer0");
                        *running_max_memvar = *lhs_ts0.max(running_max_memvar);
                        *running_max_memvar = *lhs_ts1.max(running_max_memvar);
                        *running_max_memvar = *lhs_val0.max(running_max_memvar);
                        *running_max_memvar = *lhs_val1.max(running_max_memvar);
                        *running_max_memvar = *rhs_ts0.max(running_max_memvar);
                        *running_max_memvar = *rhs_ts1.max(running_max_memvar);
                        *running_max_memvar = *rhs_val0.max(running_max_memvar);
                        *running_max_memvar = *rhs_val1.max(running_max_memvar);
                        let lhs_ts0 = Dual(format!("[{lhs_ts0}]"), Yul::calldataload(lhs_ts0));
                        let lhs_ts1 = Dual(format!("[{lhs_ts1}]"), Yul::calldataload(lhs_ts1));
                        let lhs_val0 = Dual(format!("[{lhs_val0}]"), Yul::calldataload(lhs_val0));
                        let lhs_val1 = Dual(format!("[{lhs_val1}]"), Yul::calldataload(lhs_val1));
                        let rhs_ts0 = Dual(format!("[{rhs_ts0}]"), Yul::calldataload(rhs_ts0));
                        let rhs_ts1 = Dual(format!("[{rhs_ts1}]"), Yul::calldataload(rhs_ts1));
                        let rhs_val0 = Dual(format!("[{rhs_val0}]"), Yul::calldataload(rhs_val0));
                        let rhs_val1 = Dual(format!("[{rhs_val1}]"), Yul::calldataload(rhs_val1));
                        let lhs_pack = yul_format!("add(1, shl(1, add({lhs_ts0:o}, shl(7, add({lhs_ts1:o}, shl(7, add({lhs_val0:o}, shl(7, {lhs_val1:o}))))))))");
                        let rhs_pack = yul_format!("add(1, shl(1, add({rhs_ts0:o}, shl(7, add({rhs_ts1:o}, shl(7, add({rhs_val0:o}, shl(7, {rhs_val1:o}))))))))");
                        [
                            Dual(
                                format!("α³{lhs_ts0} + α⁴{lhs_ts1} + α⁵{lhs_val0} + α⁶{lhs_val1}"),
                                yul_format!("memrelinitpart_from_pack(ptr, {lhs_pack:x})")
                            ),
                            Dual(
                                format!("α³{rhs_ts0} + α⁴{rhs_ts1} + α⁵{rhs_val0} + α⁶{rhs_val1}"),
                                yul_format!("memrelinitpart_from_pack(ptr, {rhs_pack:x})")
                            )
                        ]
                    }
                }
            }
            fn lookrelsingle_to_calldata(tuple: &NoFieldSingleColumnLookupRelation, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize), cfg: &mut Vec<Vec<[Dual; 4]>>) -> Dual {
                let NoFieldSingleColumnLookupRelation { input, lookup_set_index: _ } = tuple;
                let NoFieldLinearRelation { linear_terms, constant } = input;
                let [constant, linear_pack1, linear_pack2, linear_pack3] = linrel_to_pack(constant, linear_terms, expected_layer, layer0_group_widths, running_max_group_offsets);
                let logup_gamma = Dual("δ".to_string(), Yul::logup_gamma());
                let cfg_id = cfg.len();
                let out = Dual( format!("({logup_gamma} + {constant} + {linear_pack1} + {linear_pack2} + {linear_pack3})"), yul_format!("lookrelsingle_from_cfg(ptr, {cfg_id})"));
                cfg.push(vec![[constant, linear_pack1, linear_pack2, linear_pack3]]);
                out
            }
            fn lookrelgeneric_to_calldata(tuple: &NoFieldVectorLookupRelation, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize), cfg: &mut Vec<Vec<[Dual; 4]>>) -> Dual {
                let NoFieldVectorLookupRelation { columns, lookup_set_index: _ } = tuple;
                assert_eq!(columns.len(), 10, "we expect generic lookups to be tuples of 10 elements");
                let logup_gamma = Dual("δ".to_string(), Yul::logup_gamma());
                let logup_alpha = Dual("β".to_string(), Yul::logup_alpha());
                let cfg_id = cfg.len();
                let mut cfg_items = vec![];
                let compressed_column = columns.iter().enumerate().map(|(j, column)| {
                    let NoFieldLinearRelation { linear_terms, constant } = column;
                    let [constant, linear_pack1, linear_pack2, linear_pack3] = linrel_to_pack(constant, linear_terms, expected_layer, layer0_group_widths, running_max_group_offsets);
                    let logup_alpha_j = logup_alpha.0.clone() + &superscript(j);
                    let out = Dual(format!("{logup_alpha_j}({constant} + {linear_pack1} + {linear_pack2} + {linear_pack3})"), yul_format!(""));
                    cfg_items.push([constant, linear_pack1, linear_pack2, linear_pack3]);
                    out
                }).reduce(|acc, el| Dual(format!("{acc} + {el}"), yul_format!(""))).unwrap();
                cfg.push(cfg_items);
                Dual(
                    format!("({logup_gamma} + {compressed_column})"),
                    yul_format!("lookrelgeneric_from_cfg(ptr, {cfg_id})")
                )
            }
            fn linrel_to_calldata(inputs: &NoFieldLinearRelation, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize), cfg: &mut Vec<Vec<[Dual; 4]>>) -> Dual {
                let NoFieldLinearRelation { linear_terms, constant } = inputs;
                let [constant, linear_pack1, linear_pack2, linear_pack3] = linrel_to_pack(constant, linear_terms, expected_layer, layer0_group_widths, running_max_group_offsets);
                let cfg_idx = cfg.len();
                let out = Dual(format!("{constant} + {linear_pack1} + {linear_pack2} + {linear_pack3}"), yul_format!("linrel_from_cfg(ptr, {cfg_idx})"));
                cfg.push(vec![[constant, linear_pack1, linear_pack2, linear_pack3]]);
                out
            }
            fn linrel_to_pack(constant: &u32, linear_terms: &Box<[(u32, GKRAddress)]>, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize)) -> [Dual; 4] {
                let constant = const_to_pack(constant);
                let [linear_pack1, linear_pack2, linear_pack3] = linterms_to_pack(linear_terms, expected_layer, layer0_group_widths, running_max_group_offsets);
                [constant, linear_pack1, linear_pack2, linear_pack3]
            }
            fn quadrel_to_pack(address: &GKRAddress, linear_terms: &Box<[(u32, GKRAddress)]>, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize)) -> [Dual; 4] {
                let read = gkraddress_to_calldata(address, expected_layer, layer0_group_widths, running_max_group_offsets);
                let [linear_pack1, linear_pack2, linear_pack3] = linterms_to_pack(linear_terms, expected_layer, layer0_group_widths, running_max_group_offsets);
                [read, linear_pack1, linear_pack2, linear_pack3]
            }
            fn linterms_to_pack(linear_terms: &Box<[(u32, GKRAddress)]>, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize)) -> [Dual; 3] {
                fn const_and_gkraddress_to_term(c: &u32, addr: &GKRAddress, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize)) -> Dual {
                    let input = gkraddress_to_calldata(addr, expected_layer, layer0_group_widths, running_max_group_offsets);
                    let packc = const_to_pack(c); // 31 bits
                    Dual(format!("{packc}{input}"), yul_format!("add({input:o}, shl(7, {packc:x}))")) // 31 + 7 = 38 bits
                }
                assert!(linear_terms.len() <= 18, "we expect linear_terms to have at most 18 elements, but got {}", linear_terms.len());
                let mut packed_terms = linear_terms.chunks(6).map(|chunk| {
                    let len = chunk.len();
                    let pack = chunk.iter().map(|(c, addr)| {
                        const_and_gkraddress_to_term(c, addr, expected_layer, layer0_group_widths, running_max_group_offsets)
                    }).reduce(|acc, el| Dual(format!("{acc} + {el}"), yul_format!("add({el:x}, shl(38, {acc:x}))"))).unwrap();
                    Dual(format!("{pack}"), yul_format!("add({len}, shl(3, {pack:x}))"))
                });
                assert!(packed_terms.len() <= 3, "we expect linear_terms to have at most 18 elements, but got {}", linear_terms.len());
                core::array::from_fn(|_| packed_terms.next().unwrap_or(Dual(format!("0"), yul_format!("0"))))
            }
            fn quadrel_to_calldata(input: &NoFieldMaxQuadraticGKRRelation, expected_layer: usize, layer0_group_widths: (usize, usize, usize, usize), running_max_group_offsets: &mut (usize, usize, usize, usize), cfg: &mut Vec<Vec<[Dual; 4]>>) -> Dual {
                let NoFieldMaxQuadraticGKRRelation { quadratic_terms, linear_terms, constant } = input;
                assert!(quadratic_terms.len() <= 18, "we expect linear_terms to have at most 18 elements, but got {}", quadratic_terms.len());
                let cfg_id = cfg.len();
                let mut cfg_items = vec![];
                let [mut constant, linear_pack1, linear_pack2, linear_pack3] = linrel_to_pack(constant, linear_terms, expected_layer, layer0_group_widths, running_max_group_offsets);
                let constant_plus_linear = Dual(format!("{constant} + {linear_pack1} + {linear_pack2} + {linear_pack3}"), yul_format!(""));
                if quadratic_terms.len() > 0 {
                    constant = Dual(format!("{constant}"), yul_format!("add({constant:x}, shl(31, 1))")); // 32 bits to indicate that we have quadratic terms
                }
                cfg_items.push([constant, linear_pack1, linear_pack2, linear_pack3]);
                let quadratic = quadratic_terms.iter().enumerate().map(|(j, (address, linear_terms))| {
                    let [var, linear_pack1, linear_pack2, linear_pack3] = quadrel_to_pack(address, linear_terms, expected_layer, layer0_group_widths, running_max_group_offsets);
                    let out = Dual(format!("{var}({linear_pack1} + {linear_pack2} + {linear_pack3})"), yul_format!(""));
                    let mut var_idx = Dual(format!("{var}"), yul_format!("{var:o}"));
                    if j != quadratic_terms.len() - 1 {
                        var_idx = Dual(format!("{var_idx}"), yul_format!("add({var_idx:x}, shl(7, 1))")); // 8 bits to indicate that we have more quadratic terms
                    }
                    cfg_items.push([var_idx, linear_pack1, linear_pack2, linear_pack3]);
                    out
                }).reduce(|acc, el| Dual(format!("{acc} + {el}"), yul_format!(""))).unwrap_or(Dual(format!("0"), yul_format!("0")));
                cfg.push(cfg_items);
                Dual(
                    format!("{constant_plus_linear} + {quadratic}"),
                    yul_format!("quadrel_from_cfg(ptr, {cfg_id})")
                )
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
                    yul_println!("
                    \t// {relation_name}: {num1}/{den1} + {num2}/{den2} = {num_out}/{den_out}
                    \tacc := gate_aggregatelookuprationalpair(ptr, alpha, acc, {num1:o}, {num2:o}, {den1:o}, {den2:o})
                    \t");
                }
                NoFieldGKRRelation::CopyInExtensionField { input, output } => {
                    let input = gkraddress_to_calldata(input, i, layer0_group_widths, &mut running_max_group_offsets);
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    yul_println!("
                    \t// {relation_name}: {input} = {output}
                    \tacc := gate_copyinextensionfield(ptr, alpha, acc, {input:o})
                    \t");
                }

                // 2
                NoFieldGKRRelation::MaskIntoIdentityProduct { input , mask, output } => {
                    let input = gkraddress_to_calldata(input, i, layer0_group_widths, &mut running_max_group_offsets);
                    let mask = gkraddress_to_calldata(mask, i, layer0_group_widths, &mut running_max_group_offsets);
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    yul_println!("
                    \t// {relation_name}: {input}*{mask} + (1-{mask}) = {output}
                    \tacc := gate_maskintoidentityproduct(ptr, alpha, acc, {input:o}, {mask:o})
                    \t");
                }

                // 1
                NoFieldGKRRelation::CopyInBaseField { input, output } => {
                    let input = gkraddress_to_calldata(input, i, layer0_group_widths, &mut running_max_group_offsets);
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    yul_println!("
                    \t// {relation_name}: {input} = {output}
                    \tacc := gate_copyinbasefield(ptr, alpha, acc, {input:o})
                    \t");
                }
                NoFieldGKRRelation::TrivialProduct { input, output } => {
                    let [lhs, rhs] = input.each_ref().map(|addr| gkraddress_to_calldata(addr, i, layer0_group_widths, &mut running_max_group_offsets));
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    yul_println!("
                    \t// {relation_name}: {lhs}*{rhs} = {output}
                    \tacc := gate_trivialproduct(ptr, alpha, acc, {lhs:o}, {rhs:o})
                    \t");
                }
                NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs { input, remainder, output } => {
                    let [num, den] = input.each_ref().map(|addr| gkraddress_to_calldata(addr, i, layer0_group_widths, &mut running_max_group_offsets));
                    let remainder = gkraddress_to_calldata(remainder, i, layer0_group_widths, &mut running_max_group_offsets);
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter));
                    let logup_gamma = Dual("δ".to_string(), Yul::logup_gamma());
                    yul_println!("
                    \t// {relation_name}: {num}/{den} + 1/({logup_gamma} + {remainder}) = {num_out}/{den_out}
                    \tacc := gate_lookupunbalancedpairwithmaterializedbaseinputs(ptr, alpha, acc, {num:o}, {den:o}, {remainder:o})
                    \t");
                }
                // (unified)
                NoFieldGKRRelation::LookupPairFromVectorInputs { input, output } => {
                    let [den1, den2] = input.each_ref().map(|input| lookrelgeneric_to_calldata(input, i, layer0_group_widths, &mut running_max_group_offsets, &mut cfg));
                    let [num_out, den_out] = output.each_ref_mayberevmap(|address| gkraddress_to_outputvar(address, i + 1, &mut running_output_counter));
                    yul_println!("
                    \t// {relation_name}: 1/{den1} + 1/{den2} = {num_out}/{den_out}
                    \tacc := gate_lookuppairfromvectorinputs(ptr, alpha, acc, {den1:b}, {den2:b})
                    \t");
                }
                NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs { input, remainder, output } => {
                    let [num1, den1] = input.each_ref().map(|address| gkraddress_to_calldata(address, i, layer0_group_widths, &mut running_max_group_offsets));
                    let den2 = lookrelgeneric_to_calldata(remainder, i, layer0_group_widths, &mut running_max_group_offsets, &mut cfg);
                    let [num_out, den_out] = output.each_ref_mayberevmap(|address| gkraddress_to_outputvar(address, i + 1, &mut running_output_counter));
                    yul_println!("
                    \t// {relation_name}: {num1}/{den1} + 1/{den2} = {num_out}/{den_out}
                    \tacc := gate_lookupunbalancedpairwithvectorinputs(ptr, alpha, acc, {num1:o}, {den1:o}, {den2:b})
                    \t");
                }

                // 0
                NoFieldGKRRelation::InitialGrandProductWithoutCaches { input, output } => {
                    let [lhs, rhs] = input.each_ref().map(|contribution| memrel_to_calldata(contribution, &mut running_max_group_offsets));
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    yul_println!("
                    \t// {relation_name}: {lhs}*{rhs} = {output}
                    \tacc := gate_initialgrandproductwithoutcaches(ptr, alpha, acc, {lhs:p}, {rhs:p})
                    \t");
                }
                NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup { input, setup, output } => {
                    let input = gkraddress_to_calldata(input, i, layer0_group_widths, &mut running_max_group_offsets);
                    let [multiplicity, setup] = setup.each_ref().map(|address| gkraddress_to_calldata(address, i, layer0_group_widths, &mut running_max_group_offsets));
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter));
                    let logup_gamma = Dual("δ".to_string(), Yul::logup_gamma());
                    yul_println!("
                    \t// {relation_name}: 1/({logup_gamma} + {input}) - {multiplicity}/({logup_gamma} + {setup}) = {num_out}/{den_out}
                    \tacc := gate_lookupfrommaterializedbaseinputwithsetup(ptr, alpha, acc, {multiplicity:o}, {input:o}, {setup:e})
                    \t");
                }
                NoFieldGKRRelation::LookupPairFromBaseInputs { input, output, range_check_width: _ } => {
                    let [den1, den2] = input.each_ref().map(|relation| lookrelsingle_to_calldata(relation, i, layer0_group_widths, &mut running_max_group_offsets, &mut cfg));
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter));
                    yul_println!("
                    \t// {relation_name}: 1/{den1} + 1/{den2} = {num_out}/{den_out}
                    \tacc := gate_lookuppairfrombaseinputs(ptr, alpha, acc, {den1:b}, {den2:b})
                    \t");
                }
                NoFieldGKRRelation::MaterializeSingleLookupInput { input, output, range_check_width: _ } => {
                    let NoFieldSingleColumnLookupRelation{ input, lookup_set_index: _ }  = input;
                    let compressed_tuple = linrel_to_calldata(input, i, layer0_group_widths, &mut running_max_group_offsets, &mut cfg);
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    yul_println!("
                    \t// {relation_name}: {compressed_tuple} = {output}
                    \tacc := gate_materializesinglelookupinput(ptr, alpha, acc, {compressed_tuple:b})
                    \t");
                }
                // NoFieldGKRRelation::LookupWithDensAndCachedSetup { input, setup, output } => {
                NoFieldGKRRelation::LookupWithDensAndSetupExpressions { input, setup, output } => {
                    let (input_mask, input_den) = input;
                    let (setup_multiplicity, setup_terms) = setup;
                    let input_mask = gkraddress_to_calldata(input_mask, i, layer0_group_widths, &mut running_max_group_offsets);
                    let input_den = lookrelgeneric_to_calldata(input_den, i, layer0_group_widths, &mut running_max_group_offsets, &mut cfg);
                    let setup_multiplicity = gkraddress_to_calldata(setup_multiplicity, i, layer0_group_widths, &mut running_max_group_offsets);
                    let logup_alpha = Dual("β".to_string(), Yul::logup_alpha());
                    assert_eq!(setup_terms.len(), 10, "we expect generic lookups to be tuples of 10 elements");
                    let setup = {
                        let setup_pack = setup_terms.iter().enumerate().map(|(j, addr)| {
                            let input = gkraddress_to_calldata(addr, i, layer0_group_widths, &mut running_max_group_offsets);
                            let beta_j = logup_alpha.0.clone() + &superscript(j);
                            Dual(format!("{beta_j}{input}"), yul_format!("{input:o}"))
                        }).reduce(|acc, el| Dual(format!("{acc} + {el}"), yul_format!("add({el:x}, shl(7, {acc:x}))"))).unwrap();
                        setup_pack
                    };
                    let [num_out, den_out] = output.each_ref_mayberevmap(|addr| gkraddress_to_outputvar(addr, i + 1, &mut running_output_counter));
                    let logup_gamma = Dual("δ".to_string(), Yul::logup_gamma());
                    yul_println!("
                    \t// {relation_name}: {input_mask}/{input_den} - {setup_multiplicity}/({logup_gamma} + {setup}) = {num_out}/{den_out}
                    \tacc := gate_lookupwithdensandsetupexpressions(ptr, alpha, acc, {input_mask:o}, {setup_multiplicity:o}, {input_den:b}, {setup:x})
                    \t");
                }
                // NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input, expression } => {
                NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input } => {
                    let input = quadrel_to_calldata(input, i, layer0_group_widths, &mut running_max_group_offsets, &mut cfg);
                    // let expression = expression_to_calldata(expression, i, layer0_group_widths, &mut running_max_group_offsets);
                    yul_println!("
                    \t// {relation_name}: 0 == {input}
                    \tacc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, {input:b})
                    \t");
                }
                // (unified)
                NoFieldGKRRelation::InitsOrTeardownsInitialPair { timestamp_and_value, setup, output, set_idxes } => {
                    let addr_high_tops = {
                        assert!(set_idxes.iter().all(|c| *c < (1<<8)), "we expect set_idxes to be 8 bits, but got {set_idxes:?}");
                        let [lhs_addr_high_top, rhs_addr_high_top] = set_idxes;
                        yul_format!("add({lhs_addr_high_top:o}, shl(8, {rhs_addr_high_top:o}))")
                    };
                    let [setup_low, setup_high] = setup.each_ref().map(|address| gkraddress_to_calldata(address, i, layer0_group_widths, &mut running_max_group_offsets));
                    let [lhs_addr_high, rhs_addr_high] = {
                        assert_eq!(circuit.trace_len, 1<<24, "currently we expect gkr_compress to go up to 2^24");
                        assert_eq!(circuit.memory_layout.inits_and_teardowns_word_bits.unwrap(), 2, "we expect there to be just 2 empty low bits");
                        let high_bits_shift = prover::gkr::high_bits_offset_for_inits_and_teardowns::<2>(circuit.trace_len);
                        let top_bits = set_idxes.map(|c| c << high_bits_shift);
                        let memory_alpha2 = Dual(format!("α²"), Yul::memory_alpha(1));
                        top_bits.map(|c| Dual(format!("{memory_alpha2}({setup_high} + {c})"), yul_format!("mulmod({memory_alpha2:x}, add({setup_high:x}, {c}), P)")))
                    };
                    let [lhs_timestamp_and_value, rhs_timestamp_and_value] = memrelinitparts_to_calldata_inner(timestamp_and_value, &mut running_max_group_offsets);
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    let shared = {
                        let address_space = AddressSpaceType::RAM as u32;
                        let memory_gamma = Dual(format!("γ"), Yul::memory_gamma());
                        let memory_alpha1 = Dual(format!("α"), Yul::memory_alpha(0));
                        Dual(format!("{memory_gamma} + {address_space} + {memory_alpha1}{setup_low}"), yul_format!("add(add({memory_gamma:x}, {address_space}), mulmod({memory_alpha1:x}, {setup_low:x}, P))"))
                    };
                    yul_println!("
                    \t// {relation_name}: ({shared} + {lhs_addr_high} + {lhs_timestamp_and_value}) * ({shared} + {rhs_addr_high} + {rhs_timestamp_and_value}) = {output}
                    \tacc := gate_initsorteardownsinitialpair(ptr, alpha, acc, {setup_low:e}, {setup_high:e}, {addr_high_tops:x}, {lhs_timestamp_and_value:p}, {rhs_timestamp_and_value:p})
                    \t");
                }
                NoFieldGKRRelation::MaxQuadratic { input, output } => {
                    let input = quadrel_to_calldata(input, i, layer0_group_widths, &mut running_max_group_offsets, &mut cfg);
                    let output = gkraddress_to_outputvar(output, i + 1, &mut running_output_counter);
                    yul_println!("
                    \t// {relation_name}: {input} = {output}
                    \tacc := gate_maxquadratic(ptr, alpha, acc, {input:b})
                    \t");
                }

                _ => todo!("could not match {enforced_relation:?} at layer {i}")
            }
        }

        assert_eq!(running_output_counter, if DEBUG_NATURAL_GATE_ORDER { previous_input_count } else { 0 });
        if i > 0 {
            assert!(cached_relations.len() == 0);
            previous_input_count = intermediate_layer_width.unwrap();
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
            previous_input_count = l0_memvars + l0_witvars + l0_setupvars;
        }


        let check = if DEBUG_ENABLE_DUMMY_CHECKS {
            yul_format!("
            let dummy_check := mod(add(claim, sub(P, rhs_scaled)), P)
            \tmstore(GKR_CIRCUIT_CACHE_PTR(), dummy_check)
            ")
        } else {
            yul_format!("
            if mod(add(claim, sub(P, rhs_scaled)), P) {{ revert(0, 0) }}
            ")
        };
        yul_println!("
            let rhs_scaled := mulmod(acc, eq_scale, P)
            // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
            // after stack-heavy values are dead
            {check:x}

            // POINT CLAIMS BATCH ({previous_input_count} POINTS)
            next_ptr, next_claim, next_alpha := sumcheck_claims_batch(ptr, {previous_input_count})
        }}
        ");

        // if i <= 1 {
        //     break
        // }
    }

    // INTRODUCE EXTERNAL HELPER FNS
    // GREAT FOR BYTECODE REDUCTION!!
    let check = if DEBUG_ENABLE_DUMMY_CHECKS {
        yul_format!("
        let dummy_check := mod(add(claim, sub(P, g0g1_scaled)), P)
        \t\tmstore(GKR_CIRCUIT_CACHE_PTR(), dummy_check)
        ")
    } else {
        yul_format!("
        if mod(add(claim, sub(P, g0g1_scaled)), P) {{ revert(0, 0) }}
        ")
    };
    let gate_calldataload_inner = Yul::calldataload(&1234567890).0.replace("1234567890", "idx");
    let gate_mload_inner = Yul::mload(&1234567890).0.replace("1234567890", "idx");
    let memory_gamma = Yul::memory_gamma();
    let memory_alpha1 = Yul::memory_alpha(0);
    let memory_alpha2 = Yul::memory_alpha(1);
    let memory_alpha3 = Yul::memory_alpha(2);
    let memory_alpha4 = Yul::memory_alpha(3);
    let memory_alpha5 = Yul::memory_alpha(4);
    let memory_alpha6 = Yul::memory_alpha(5);
    let memory_address_space_ram = AddressSpaceType::RAM as u32;
    let memory_address_high_top_shift = prover::gkr::high_bits_offset_for_inits_and_teardowns::<2>(circuit.trace_len);
    let logup_gamma = Yul::logup_gamma();
    let logup_alpha = Yul::logup_alpha();
    let yul_cfg = cfg.iter().enumerate().map(|(i, items)| {
        let yul_items = items.iter().enumerate().map(|(j, item)| {
            let [meta, linear_pack1, linear_pack2, linear_pack3] = item;
            yul_format!("\tcase {j} {{ meta := {meta:x} pack1 := {linear_pack1:x} pack2 := {linear_pack2:x} pack3 := {linear_pack3:x} }}")
        }).reduce(|acc, el| yul_format!("{acc:x}\n\t{el:x}")).unwrap();
        yul_format!("
        case {i} {{ switch item
            {yul_items:x}
        \t}}")
    }).reduce(|acc, el| yul_format!("{acc:x}\n\t{el:x}")).unwrap();
    yul_println!("
        function sumcheck_rounds_circuit(ptr, claim) -> next_ptr, next_claim, eq_scale {{
            // NB: need to inline GKR_CIRCUIT_LAYER_ROUNDS unfortunately
            eq_scale := 1
            for {{ let i := 0 }} lt(i, GKR_CIRCUIT_LAYER_ROUNDS) {{ i := add(i, 1) }} {{
                let w0 := calldataload(ptr)
                let w1 := calldataload(add(ptr, 32))
                let c0 := shr(128, w0)
                let c1 := and(w0, MASK)
                let c2 := shr(128, w1)
                let c3 := and(w1, MASK)
                let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, P)
                let r := transcript_4to1_dual(w0, w1) // before-check draw is intentional; see HEURISTICS.md
                // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
                if mod(add(claim, sub(P, g0g1_scaled)), P) {{ revert(0, 0) }}
                {check:x}
                claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
                let z := mload(add(POINT_PTR(), mul(i, 32)))
                let zr := mulmod(z, r, P)
                eq_scale := add(add(add(zr, zr), 1), sub(mul(4, P), add(z, r)))
                mstore(add(POINT_PTR(), mul(i, 32)), r)
                ptr := add(ptr, 64)
            }}
            next_ptr := ptr
            next_claim := claim
        }}
        function transcriptNto1(ptr, input_elements) -> alpha {{
            let input_bytes := mul(input_elements, 16)
            calldatacopy(add(SEED_PTR(), 32), ptr, input_bytes)
            let seed := keccak256(SEED_PTR(), add(32, input_bytes))
            mstore(SEED_PTR(), seed)
            alpha := shr(128, seed)
        }}
        function sumcheck_claims_batch(ptr, points) -> next_ptr, next_claim, next_alpha {{
            let is_odd := mod(points, 2)
            if is_odd {{
                next_claim := shr(128, calldataload(add(ptr, mul(16, sub(points, 1)))))
            }}
            next_alpha := transcriptNto1(ptr, points)
            let even_points := sub(points, is_odd)
            let pairs := shr(1, even_points)
            for {{ let pair := sub(pairs, 1) }} lt(pair, pairs) {{ pair := sub(pair, 1) }} {{
                let word := calldataload(add(ptr, mul(pair, 32)))
                let el1 := and(MASK, word)
                let el0 := shr(128, word)
                next_claim := add(mulmod(next_claim, next_alpha, P), el1)
                next_claim := add(mulmod(next_claim, next_alpha, P), el0)
            }}
            next_ptr := add(ptr, mul(16, points))
        }}

        function gkr_memrel_compress(address_space, addr_low, addr_high, ts_low, ts_high, val_low, val_high) -> compressed {{
            compressed := add(mload(add(MEMORY_CHALLS_PTR(), 192)), address_space)
            compressed := add(compressed, mulmod(mload(MEMORY_CHALLS_PTR()), addr_low, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 32)), addr_high, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 64)), ts_low, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 96)), ts_high, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 128)), val_low, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 160)), val_high, P))
        }}

        // Fold five generic lookup tuple columns into an existing Horner accumulator.
        // A single helper that took all c0..c9 made solc materialize all ten columns
        // at the call boundary and failed stack allocation. Splitting the fold into
        // two five-column calls keeps each call boundary small while still supporting
        // arbitrary linrel_to_calldata_inner() output for every column.
        function gkr_lookrel_compress_half(acc, c0, c1, c2, c3, c4) -> acc_next {{
            acc_next := add(mulmod(acc, mload(LOGUP_CHALLS_PTR()), P), c4)
            acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c3)
            acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c2)
            acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c1)
            acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c0)
        }}

        // function gkr_memrel_compress_low(address_space, addr_low, addr_high) -> compressed {{
        //     compressed := add(compressed, add(mload(add(MEMORY_CHALLS_PTR(), 192)), address_space))
        //     compressed := add(compressed, mulmod(mload(MEMORY_CHALLS_PTR()), addr_low, P))
        //     compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 32)), addr_high, P))
        // }}
        function gkr_memrel_compress_high(ts_low, ts_high, val_low, val_high) -> compressed {{
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 64)), ts_low, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 96)), ts_high, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 128)), val_low, P))
            compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 160)), val_high, P))
        }}

        function gkr_virtual_poly_compose_vars(len, skip) -> eval {{
            // let total := add(skip, len)
            let max := sub(GKR_CIRCUIT_LAYER_ROUNDS, skip) // exclusive
            let min := sub(max, len)
            // NO NEED FOR THIS CHECK, WE DO IT VIA RUST
            // if gt(total, GKR_CIRCUIT_LAYER_ROUNDS) {{ // abort when bad
            //     min := max
            // }}
            for {{ let i := min }} lt(i, max) {{ i := add(i, 1) }} {{
                eval := add(mul(eval, 2), mload(add(POINT_PTR(), mul(i, 32))))
            }}
        }}
        function gkr_virtual_poly_zero_vars(len) -> eval {{
            eval := 1
            for {{ let i := 0 }} lt(i, len) {{ i := add(i, 1) }} {{
                eval := mulmod(eval, add(1, sub(mul(2, P), mload(add(POINT_PTR(), mul(i, 32))))), P)
            }}
        }}
        function gkr_virtual_poly_rangecheck(width) -> eval {{
            eval := mulmod(gkr_virtual_poly_compose_vars(width, 0), gkr_virtual_poly_zero_vars(sub(GKR_CIRCUIT_LAYER_ROUNDS, width)), P)
        }}

        function gate_calldataload(ptr, idx) -> load {{
            load := {gate_calldataload_inner}
        }}
        function gate_mload(ptr, idx) -> load {{
            load := {gate_mload_inner}
        }}
        function pointcheck_update(acc, alpha, gate) -> next_acc {{
            next_acc := add(mulmod(acc, alpha, P), gate)
        }}
        function logup_pointcheck_update(acc, alpha, num_out, den_out) -> next_acc {{
            acc := pointcheck_update(acc, alpha, den_out)
            next_acc := pointcheck_update(acc, alpha, num_out)
        }}
        function u128_neg(input) -> neg_input {{
            neg_input := sub(mul(2, P), input)
        }}
        function memory_gamma() -> gamma {{
            gamma := {memory_gamma:x}
        }}
        function memory_alpha1() -> alpha1 {{
            alpha1 := {memory_alpha1:x}
        }}
        function memory_alpha2() -> alpha2 {{
            alpha2 := {memory_alpha2:x}
        }}
        function memory_alpha3() -> alpha3 {{
            alpha3 := {memory_alpha3:x}
        }}
        function memory_alpha4() -> alpha4 {{
            alpha4 := {memory_alpha4:x}
        }}
        function memory_alpha5() -> alpha5 {{
            alpha5 := {memory_alpha5:x}
        }}
        function memory_alpha6() -> alpha6 {{
            alpha6 := {memory_alpha6:x}
        }}
        function logup_gamma() -> gamma {{
            gamma := {logup_gamma:x}
        }}
        function logup_alpha() -> alpha {{
            alpha := {logup_alpha:x}
        }}
        function linterm_to_calldata(ptr, modc, sign, var_idx) -> term {{
            let input := gate_calldataload(ptr, var_idx)
            if sign {{
                input := u128_neg(input)
            }}
            term := mul(modc, input)
        }}
        function linterms6_from_pack(ptr, pack) -> linear {{
            let n := and(pack, sub(shl(3, 1), 1))
            pack := shr(3, pack)
            for {{ let i := 0 }} lt(i, n) {{ i := add(i, 1) }} {{
                let var_idx := and(pack, sub(shl(7, 1), 1))
                pack := shr(7, pack)
                let modc := and(pack, sub(shl(30, 1), 1))
                pack := shr(30, pack)
                let sign := and(pack, 1)
                let term := linterm_to_calldata(ptr, modc, sign, var_idx)
                linear := add(linear, term)
                pack := shr(1, pack)
            }}
        }}
        function linterms18_from_pack(ptr, pack1, pack2, pack3) -> linear {{
            linear := add(linear, linterms6_from_pack(ptr, pack1))
            linear := add(linear, linterms6_from_pack(ptr, pack2))
            linear := add(linear, linterms6_from_pack(ptr, pack3))
        }}
        function linrel_from_pack(ptr, const, pack1, pack2, pack3) -> linear {{
            let sign := shr(30, const)
            if sign {{
                let modc := and(const, sub(shl(30, 1), 1))
                const := sub(P, modc)
            }}
            linear := add(const, linterms18_from_pack(ptr, pack1, pack2, pack3))
        }}
        function quadrel_from_pack(ptr, var_idx, pack1, pack2, pack3) -> quadratic {{
            let var := gate_calldataload(ptr, var_idx)
            quadratic := mulmod(var, linterms18_from_pack(ptr, pack1, pack2, pack3), P)
        }}
        function linrel_from_cfg(ptr, id) -> value {{
            let const, pack1, pack2, pack3 := cfg(id, 0)
            value := linrel_from_pack(ptr, const, pack1, pack2, pack3)
        }}
        function lookrelsingle_from_cfg(ptr, id) -> value {{
            let const, pack1, pack2, pack3 := cfg(id, 0)
            value := add(logup_gamma(), linrel_from_pack(ptr, const, pack1, pack2, pack3))
        }}
        function lookrelgeneric_from_cfg(ptr, id) -> value {{
            for {{ let i := 9 }} lt(i, 10) {{ i := sub(i, 1) }} {{
                let const, pack1, pack2, pack3 := cfg(id, i)
                value := add(mulmod(value, logup_alpha(), P), linrel_from_pack(ptr, const, pack1, pack2, pack3))
            }}
            value := add(value, logup_gamma())
        }}
        function quadrel_from_cfg(ptr, id) -> value {{
            let dyn_const, pack1, pack2, pack3 := cfg(id, 0)
            let const := and(dyn_const, sub(shl(31, 1), 1))
            let top_bit := shr(31, dyn_const)
            value := linrel_from_pack(ptr, const, pack1, pack2, pack3)
            for {{ let i := 1 }} top_bit {{ i := add(i, 1) }} {{
                let dyn_var_idx
                dyn_var_idx, pack1, pack2, pack3 := cfg(id, i)
                top_bit := shr(7, dyn_var_idx)
                let var_idx := and(dyn_var_idx, sub(shl(7, 1), 1))
                value := add(value, quadrel_from_pack(ptr, var_idx, pack1, pack2, pack3))
            }}
        }}
        // this fn is for fetching dynamic inputs
        function cfg(id, item) -> meta, pack1, pack2, pack3 {{
            switch id
            {yul_cfg:x}
        }}
        // memory related
        function memrel_to_calldata(addr_space, addr_low, addr_high, ts_low, ts_high, val_low, val_high) -> compressed {{
            compressed := add(memory_gamma(), addr_space)
            compressed := add(compressed, mulmod(memory_alpha1(), addr_low, P))
            compressed := add(compressed, mulmod(memory_alpha2(), addr_high, P))
            compressed := add(compressed, mulmod(memory_alpha3(), ts_low, P))
            compressed := add(compressed, mulmod(memory_alpha4(), ts_high, P))
            compressed := add(compressed, mulmod(memory_alpha5(), val_low, P))
            compressed := add(compressed, mulmod(memory_alpha6(), val_high, P))
        }}
        function memrelinitpart_to_calldata(ts_low, ts_high, val_low, val_high) -> compressed {{
            compressed := add(compressed, mulmod(memory_alpha3(), ts_low, P))
            compressed := add(compressed, mulmod(memory_alpha4(), ts_high, P))
            compressed := add(compressed, mulmod(memory_alpha5(), val_low, P))
            compressed := add(compressed, mulmod(memory_alpha6(), val_high, P))
        }}
        function memrel_from_pack(ptr, pack) -> value {{
            let addr_space := and(pack, sub(shl(9, 1), 1)) // 9 bits
            pack := shr(9, pack)
            {{
                let is_var := and(addr_space, 1)
                addr_space := shr(1, addr_space)
                if is_var {{
                    let var_idx := and(addr_space, sub(shl(7, 1), 1)) // 7 bits
                    let var := gate_calldataload(ptr, var_idx)
                    let is_neg_var := shr(7, addr_space)
                    if is_neg_var {{
                        var := add(1, u128_neg(var))
                    }}
                    addr_space := var
                }}
            }}

            let addr_low := and(pack, sub(shl(17, 1), 1)) // 17 bits
            let addr_high
            pack := shr(17, pack)
            {{
                let is_var_low := and(addr_low, 1)
                addr_low := shr(1, addr_low)
                if is_var_low {{
                    let var_low_idx := and(addr_low, sub(shl(7, 1), 1)) // 7 bits
                    let var_low := gate_calldataload(ptr, var_low_idx)
                    let is_var_high := shr(7, addr_low)
                    if is_var_high {{
                        let var_high_idx := shr(1, is_var_high)
                        let var_high := gate_calldataload(ptr, var_high_idx)
                        addr_high := var_high
                    }}
                    addr_low := var_low
                }}
            }}

            let ts_low := and(pack, sub(shl(17, 1), 1)) // 17 bits
            let ts_high
            pack := shr(17, pack)
            {{
                let is_vars := ts_low
                ts_low := shr(1, ts_low)
                if is_vars {{
                    let offset := and(ts_low, 3) // 2 bits
                    let vars_idx := shr(2, ts_low) // 7+7 bits
                    let var_low_idx := and(vars_idx, sub(shl(7, 1), 1)) // 7 bits
                    let var_high_idx := shr(7, vars_idx) // 7 bits
                    let var_low := gate_calldataload(ptr, var_low_idx)
                    let var_high := gate_calldataload(ptr, var_high_idx)
                    ts_low := add(var_low, offset)
                    ts_high := var_high
                }}
            }}

            let val_low := and(pack, sub(shl(30, 1), 1)) // 30 bits
            let val_high
            pack := shr(30, pack)
            {{
                let is_vars := val_low
                val_low := shr(1, val_low)
                if is_vars {{
                    let is_vars_u8 := and(val_low, 1)
                    val_low := shr(1, val_low)
                    let var_low_idx := and(val_low, sub(shl(7, 1), 1)) // 7 bits
                    let var_high_idx := and(shr(7, val_low), sub(shl(7, 1), 1)) // 7 bits
                    let var_low := gate_calldataload(ptr, var_low_idx)
                    let var_high := gate_calldataload(ptr, var_high_idx)
                    if is_vars_u8 {{
                        let var_lh_idx := and(shr(14, val_low), sub(shl(7, 1), 1)) // 7 bits
                        let var_hh_idx := shr(21, val_low) // 7 bits
                        let var_lh := gate_calldataload(ptr, var_lh_idx)
                        let var_hh := gate_calldataload(ptr, var_hh_idx)
                        var_low := add(var_low, shl(8, var_lh))
                        var_high := add(var_high, shl(8, var_hh))
                    }}
                    val_low := var_low
                    val_high := var_high
                }}
            }}

            value := memrel_to_calldata(addr_space, addr_low, addr_high, ts_low, ts_high, val_low, val_high)
        }}
        function memrelinitpart_from_pack(ptr, pack) -> value {{
            let ts_low := pack // 29 bits
            let ts_high, val_low, val_high
            {{
                let is_vars := ts_low
                ts_low := shr(1, ts_low)
                if is_vars {{
                    let ts_low_idx := and(ts_low, sub(shl(7, 1), 1)) // 7 bits
                    let ts_high_idx := and(shr(7, ts_low), sub(shl(7, 1), 1)) // 7 bits
                    let val_low_idx := and(shr(14, ts_low), sub(shl(7, 1), 1)) // 7 bits
                    let val_high_idx := shr(21, ts_low) // 7 bits
                    ts_low := gate_calldataload(ptr, ts_low_idx)
                    ts_high := gate_calldataload(ptr, ts_high_idx)
                    val_low := gate_calldataload(ptr, val_low_idx)
                    val_high := gate_calldataload(ptr, val_high_idx)
                }}
            }}
            value := memrelinitpart_to_calldata(ts_low, ts_high, val_low, val_high)
        }}
        

        // 3
        function gate_aggregatelookuprationalpair(ptr, alpha, acc, num1_idx, num2_idx, den1_idx, den2_idx) -> next_acc {{
            let num1 := gate_calldataload(ptr, num1_idx)
            let num2 := gate_calldataload(ptr, num2_idx)
            let den1 := gate_calldataload(ptr, den1_idx)
            let den2 := gate_calldataload(ptr, den2_idx)
            let den_out := mulmod(den1, den2, P)
            let num_out := add(mulmod(num1, den2, P), mulmod(num2, den1, P))
            next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
        }}
        function gate_copyinextensionfield(ptr, alpha, acc, input_idx) -> next_acc {{
            let input := gate_calldataload(ptr, input_idx)
            next_acc := pointcheck_update(acc, alpha, input)
        }}

        // 2
        function gate_maskintoidentityproduct(ptr, alpha, acc, input_idx, mask_idx) -> next_acc {{
            let input := gate_calldataload(ptr, input_idx)
            let mask := gate_calldataload(ptr, mask_idx)
            // let neg_mask := u128_neg(mask)
            // let gate := add(mulmod(input, mask, P), add(1, neg_mask))
            let neg_one := sub(P, 1)
            let gate := add(mulmod(mask, add(input, neg_one), P), 1)
            next_acc := pointcheck_update(acc, alpha, gate)
        }}

        // 1
        function gate_copyinbasefield(ptr, alpha, acc, input_idx) -> next_acc {{
            let input := gate_calldataload(ptr, input_idx)
            next_acc := pointcheck_update(acc, alpha, input)
        }}
        function gate_trivialproduct(ptr, alpha, acc, lhs_idx, rhs_idx) -> next_acc {{
            let lhs := gate_calldataload(ptr, lhs_idx)
            let rhs := gate_calldataload(ptr, rhs_idx)
            let gate := mulmod(lhs, rhs, P)
            next_acc := pointcheck_update(acc, alpha, gate)
        }}
        function gate_lookupunbalancedpairwithmaterializedbaseinputs(ptr, alpha, acc, num1_idx, den1_idx, den2_remainder_idx) -> next_acc {{
            let num1 := gate_calldataload(ptr, num1_idx)
            let den1 := gate_calldataload(ptr, den1_idx)
            let den2_remainder := gate_calldataload(ptr, den2_remainder_idx)
            let den2 := add(logup_gamma(), den2_remainder)
            let den_out := mulmod(den1, den2, P)
            let num_out := add(mulmod(num1, den2, P), den1)
            next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
        }}
        // (unified)
        function gate_lookuppairfromvectorinputs(ptr, alpha, acc, den1_cfg, den2_cfg) -> next_acc {{
            let den1 := lookrelgeneric_from_cfg(ptr, den1_cfg)
            let den2 := lookrelgeneric_from_cfg(ptr, den2_cfg)
            let den_out := mulmod(den1, den2, P)
            let num_out := add(den2, den1)
            next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
        }}
        function gate_lookupunbalancedpairwithvectorinputs(ptr, alpha, acc, num1_idx, den1_idx, den2_cfg) -> next_acc {{
            let num1 := gate_calldataload(ptr, num1_idx)
            let den1 := gate_calldataload(ptr, den1_idx)
            let den2 := lookrelgeneric_from_cfg(ptr, den2_cfg)
            let den_out := mulmod(den1, den2, P)
            let num_out := add(mulmod(num1, den2, P), den1)
            next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
        }}

        // 0
        function gate_initialgrandproductwithoutcaches(ptr, alpha, acc, lhs_pack, rhs_pack) -> next_acc {{
            let lhs := memrel_from_pack(ptr, lhs_pack)
            let rhs := memrel_from_pack(ptr, rhs_pack)
            let gate := mulmod(lhs, rhs, P)
            next_acc := pointcheck_update(acc, alpha, gate)
        }}
        function gate_lookupfrommaterializedbaseinputwithsetup(ptr, alpha, acc, num2_idx, den1_remainder_idx, den2_remainder_cacheidx) -> next_acc {{
            let num2 := gate_calldataload(ptr, num2_idx)
            let den1_remainder := gate_calldataload(ptr, den1_remainder_idx)
            let den2_remainder := gate_mload(ptr, den2_remainder_cacheidx)
            let den1 := add(logup_gamma(), den1_remainder)
            let den2 := add(logup_gamma(), den2_remainder)
            let den_out := mulmod(den1, den2, P)
            let num_out := add(den2, sub(P, mulmod(num2, den1, P)))
            next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
        }}
        function gate_lookuppairfrombaseinputs(ptr, alpha, acc, den1_cfg, den2_cfg) -> next_acc {{
            let den1 := lookrelsingle_from_cfg(ptr, den1_cfg)
            let den2 := lookrelsingle_from_cfg(ptr, den2_cfg)
            let den_out := mulmod(den1, den2, P)
            let num_out := add(den2, den1)
            next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
        }}
        function gate_materializesinglelookupinput(ptr, alpha, acc, compressed_tuple_cfg) -> next_acc {{
            let compressed_tuple := linrel_from_cfg(ptr, compressed_tuple_cfg)
            next_acc := pointcheck_update(acc, alpha, compressed_tuple)
        }}
        function gate_lookupwithdensandsetupexpressions(ptr, alpha, acc, num1_idx, num2_idx, den1_cfg, den2_remainder_pack) -> next_acc {{
            let num1 := gate_calldataload(ptr, num1_idx)
            let num2 := gate_calldataload(ptr, num2_idx)
            let den1 := lookrelgeneric_from_cfg(ptr, den1_cfg)
            let den2_remainder
            for {{ let i := 0 }} lt(i, 10) {{ i := add(i, 1) }} {{
                let idx := and(den2_remainder_pack, sub(shl(7, 1), 1)) // 7 bits
                let var := gate_calldataload(ptr, idx)
                den2_remainder := add(mulmod(den2_remainder, logup_alpha(), P), var)
                den2_remainder_pack := shr(7, den2_remainder_pack)
            }}
            let den2 := add(logup_gamma(), den2_remainder)
            let den_out := mulmod(den1, den2, P)
            let num_out := add(mulmod(num1, den2, P), sub(P, mulmod(num2, den1, P)))
            next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
        }}
        function gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, input_cfg) -> next_acc {{
            let input := quadrel_from_cfg(ptr, input_cfg)
            next_acc := add(mulmod(acc, alpha, P), input)
        }}
        // (unified)
        function gate_initsorteardownsinitialpair(ptr, alpha, acc, addr_low_cacheidx, addr_high_base_cacheidx, addr_high_tops_pack, lhs_ts_and_val_pack, rhs_ts_and_val_pack) -> next_acc {{
            let addr_low := gate_mload(ptr, addr_low_cacheidx)
            let addr_high_base := gate_mload(ptr, addr_high_base_cacheidx)
            let lhs_addr_high_top := and(addr_high_tops_pack, sub(shl(8, 1), 1)) // 8 bits
            let rhs_addr_high_top := shr(8, addr_high_tops_pack) // 8 bits
            let shared := add(add(memory_gamma(), {memory_address_space_ram}), mulmod(memory_alpha1(), addr_low, P))
            let lhs_addr_high := add(addr_high_base, shl({memory_address_high_top_shift}, lhs_addr_high_top))
            let rhs_addr_high := add(addr_high_base, shl({memory_address_high_top_shift}, rhs_addr_high_top))
            let lhs_upper := memrelinitpart_from_pack(ptr, lhs_ts_and_val_pack)
            let rhs_upper := memrelinitpart_from_pack(ptr, rhs_ts_and_val_pack)
            let lhs := add(shared, add(mulmod(memory_alpha2(), lhs_addr_high, P), lhs_upper))
            let rhs := add(shared, add(mulmod(memory_alpha2(), rhs_addr_high, P), rhs_upper))
            let gate := mulmod(lhs, rhs, P)
            next_acc := pointcheck_update(acc, alpha, gate)
        }}
        function gate_maxquadratic(ptr, alpha, acc, input_cfg) -> next_acc {{
            let input := quadrel_from_cfg(ptr, input_cfg)
            next_acc := add(mulmod(acc, alpha, P), input)
        }}

    ");
}
