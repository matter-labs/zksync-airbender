use super::*;
mod witness_gen_20_4_full {
    use super::*;
    include!("../circuit_files/full_machine_2^20_4_2nd_word_bits_generated.rs");
    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut SimpleWitnessProxy<'a, MainRiscVOracle<'b, IMStandardIsaConfig>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, MainRiscVOracle<'b, IMStandardIsaConfig>>,
        >;
        (fn_ptr)(proxy);
    }
}
mod witness_gen_21_4_full {
    use super::*;
    include!("../circuit_files/full_machine_2^21_4_2nd_word_bits_generated.rs");
    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut SimpleWitnessProxy<'a, MainRiscVOracle<'b, IMStandardIsaConfig>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, MainRiscVOracle<'b, IMStandardIsaConfig>>,
        >;
        (fn_ptr)(proxy);
    }
}
mod witness_gen_22_4_reduced {
    use super::*;
    include!("../circuit_files/reduced_machine_2^22_4_2nd_word_bits_generated.rs");
    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut SimpleWitnessProxy<'a, MainRiscVOracle<'b, IMStandardIsaConfig>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, MainRiscVOracle<'b, IMStandardIsaConfig>>,
        >;
        (fn_ptr)(proxy);
    }
}
mod witness_gen_23_4_reduced {
    use super::*;
    include!("../circuit_files/reduced_machine_2^23_4_2nd_word_bits_generated.rs");
    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut SimpleWitnessProxy<'a, MainRiscVOracle<'b, IMStandardIsaConfig>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, MainRiscVOracle<'b, IMStandardIsaConfig>>,
        >;
        (fn_ptr)(proxy);
    }
}
pub fn get_witness_function_from_config(
    config: &ProfilingConfig,
) -> fn(&mut SimpleWitnessProxy<'_, MainRiscVOracle<'_, IMStandardIsaConfig>>) {
    if config.trace_len_log == 20usize
        && config.second_word_bits == 4usize
        && config.reduced_machine == false
    {
        return witness_gen_20_4_full::witness_eval_fn;
    }
    if config.trace_len_log == 21usize
        && config.second_word_bits == 4usize
        && config.reduced_machine == false
    {
        return witness_gen_21_4_full::witness_eval_fn;
    }
    if config.trace_len_log == 22usize
        && config.second_word_bits == 4usize
        && config.reduced_machine == true
    {
        return witness_gen_22_4_reduced::witness_eval_fn;
    }
    if config.trace_len_log == 23usize
        && config.second_word_bits == 4usize
        && config.reduced_machine == true
    {
        return witness_gen_23_4_reduced::witness_eval_fn;
    }
    panic!("No witness generation function found for the given configuration");
}
