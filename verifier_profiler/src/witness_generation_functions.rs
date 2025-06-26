use super::*;
pub fn get_witness_function_from_config(
    config: &ProfilingConfig,
) -> fn(&mut SimpleWitnessProxy<'_, MainRiscVOracle<'_, IMStandardIsaConfig>>) {
    panic!("No witness generation function found for the given configuration");
}
