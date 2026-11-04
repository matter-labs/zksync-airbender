use std::fmt::Write;

pub struct LookupParams {
    pub name: String,
    pub logup_type: String,
    pub rows_l: usize,
    pub rows_t: usize,
    pub num_columns_s: usize,
    pub num_lookups_m: usize,
    pub grinding_bits_lookup: usize,
}

pub struct AirbenderTomlParams {
    // Metadata
    pub created_date: String,
    pub commit_hash: String,

    // Circuit parameters
    pub trace_length: usize,
    pub rho: f64,
    pub air_max_degree: usize,
    pub max_combo: usize,
    pub num_columns: usize,
    pub num_constraints: usize,
    pub batch_size: usize,
    pub opening_points: usize,
    pub power_batching: bool,

    // FRI parameters
    pub fri_folding_factors: Vec<usize>,
    pub fri_early_stop_degree: usize,

    // Grinding/PoW bits (100-bit security)
    pub grinding_deep: usize,
    pub grinding_commit_phase: usize,
    pub grinding_query_phase: usize,
    pub num_queries: usize,

    // Lookups
    pub lookups: Vec<LookupParams>,
}

fn header_comment(created_date: &str, commit_hash: &str) -> String {
    format!(
        "\
# Airbender VM Configuration
#
# Generated with https://github.com/matter-labs/zksync-airbender/tree/dev/tools/pow_config_generator
# Created: {created_date}
# Commit:  {commit_hash}

# Airbender has a layered proving architecture:
# - Base layer: proves correct execution of the base program.
# - Recursion layers: each layer proves the verifier program that verifies the
#   *entire* previous layer.
#
# Airbender supports multiple circuit types, and each circuit type defines its
# own instruction set. For a given layer, all proofs share a common state and
# memory argument.
#
# The set of circuit types may differ across layers:
# - Recursion layers do not need to support the full instruction set.
# - Higher layers typically prioritize fewer circuit types to reduce complexity.
#
# In this configuration we use \"worst-case\" parameters across all circuit types.
#
# Note: Additional outer layers (using other proving systems) wrap the final
# Airbender layer into a SNARK suitable for L1 verification.
"
    )
}

pub fn generate_airbender_toml(params: &AirbenderTomlParams) -> String {
    let mut out = String::new();

    writeln!(
        out,
        "{}",
        header_comment(&params.created_date, &params.commit_hash)
    )
    .unwrap();

    writeln!(out, "[zkevm]").unwrap();
    writeln!(out, "name = \"Airbender\"").unwrap();
    writeln!(out, "protocol_family = \"FRI_STARK\"").unwrap();
    writeln!(out, "field = \"M31^4\"").unwrap();
    writeln!(out, "hash_size_bits = 256").unwrap();
    writeln!(out).unwrap();
    writeln!(out).unwrap();

    writeln!(out, "[[circuits]]").unwrap();
    writeln!(out, "name = \"generalized_circuit\"").unwrap();
    writeln!(out, "rho = {}", params.rho).unwrap();
    writeln!(out, "trace_length = {}", params.trace_length).unwrap();
    writeln!(out).unwrap();
    writeln!(out, "air_max_degree = {}", params.air_max_degree).unwrap();
    writeln!(out, "max_combo = {}", params.max_combo).unwrap();
    writeln!(out).unwrap();
    writeln!(out, "num_columns = {}", params.num_columns).unwrap();
    writeln!(out, "num_constraints = {}", params.num_constraints).unwrap();
    writeln!(out, "batch_size = {}", params.batch_size).unwrap();
    writeln!(out).unwrap();
    writeln!(out, "grinding_deep = {}", params.grinding_deep).unwrap();
    writeln!(out).unwrap();
    writeln!(out, "opening_points = {}", params.opening_points).unwrap();
    writeln!(out, "power_batching = {}", params.power_batching).unwrap();
    writeln!(out).unwrap();

    let factors_str: Vec<String> = params
        .fri_folding_factors
        .iter()
        .map(|f| f.to_string())
        .collect();
    writeln!(out, "fri_folding_factors = [{}]", factors_str.join(", ")).unwrap();
    writeln!(
        out,
        "fri_early_stop_degree = {}",
        params.fri_early_stop_degree
    )
    .unwrap();
    writeln!(
        out,
        "grinding_commit_phase = {}",
        params.grinding_commit_phase
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(
        out,
        "grinding_query_phase = {}",
        params.grinding_query_phase
    )
    .unwrap();
    writeln!(out, "num_queries = {}", params.num_queries).unwrap();

    for lookup in &params.lookups {
        writeln!(out).unwrap();
        writeln!(out).unwrap();
        writeln!(out, "[[circuits.lookups]]").unwrap();
        writeln!(out, "name = \"{}\"", lookup.name).unwrap();
        writeln!(out, "logup_type = \"{}\"", lookup.logup_type).unwrap();
        writeln!(out).unwrap();
        writeln!(out, "rows_L = {}", lookup.rows_l).unwrap();
        writeln!(out, "rows_T = {}", lookup.rows_t).unwrap();
        writeln!(out, "num_columns_S = {}", lookup.num_columns_s).unwrap();
        writeln!(out, "num_lookups_M = {}", lookup.num_lookups_m).unwrap();
        writeln!(out).unwrap();
        writeln!(
            out,
            "grinding_bits_lookup = {}",
            lookup.grinding_bits_lookup
        )
        .unwrap();
    }

    out
}
