use super::*;

pub fn generate_circuit_files(
    config: &ProfilingConfig,
    dir: &str,
) {
    const SECOND_WORD_BITS_FOUR: usize = 4;
    const SECOND_WORD_BITS_FIVE: usize = 5;

    let rom_table = match config.second_word_bits {
        SECOND_WORD_BITS_FOUR => create_table_for_rom_image::<Mersenne31Field, SECOND_WORD_BITS_FOUR>(
            &[],
            TableType::RomRead.to_table_id(),
        ),
        SECOND_WORD_BITS_FIVE => create_table_for_rom_image::<_, SECOND_WORD_BITS_FIVE>(
            &[],
            TableType::RomRead.to_table_id(),
        ),
        _ => panic!("Unsupported second word bits: {}", config.second_word_bits),
    };

    let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
        true,
        &[1991],
        TableType::SpecialCSRProperties.to_table_id(),
    );

    let (compiled_circuit, ssa_forms) = if config.reduced_machine {
        let machine = MinimalMachineNoExceptionHandlingWithDelegation;
        match config.second_word_bits {
            SECOND_WORD_BITS_FOUR => (
                default_compile_machine::<MinimalMachineNoExceptionHandlingWithDelegation, SECOND_WORD_BITS_FOUR>(machine, rom_table, Some(csr_table), config.trace_len_log),
                dump_ssa_witness_eval_form::<Mersenne31Field, _, SECOND_WORD_BITS_FOUR>(machine)
            ),
            SECOND_WORD_BITS_FIVE => (
                default_compile_machine::<_, SECOND_WORD_BITS_FIVE>(machine, rom_table, Some(csr_table), config.trace_len_log),
                dump_ssa_witness_eval_form::<Mersenne31Field, _, SECOND_WORD_BITS_FIVE>(machine)
            ),
            _ => panic!("Unsupported second word bits: {}", config.second_word_bits),
        }
    } else {
        let machine = FullIsaMachineWithDelegationNoExceptionHandling;
        match config.second_word_bits {
            SECOND_WORD_BITS_FOUR => (
                default_compile_machine::<_, SECOND_WORD_BITS_FOUR>(machine, rom_table, Some(csr_table), config.trace_len_log),
                dump_ssa_witness_eval_form::<Mersenne31Field, _, SECOND_WORD_BITS_FOUR>(machine)
            ),
            SECOND_WORD_BITS_FIVE => (
                default_compile_machine::<_, SECOND_WORD_BITS_FIVE>(machine, rom_table, Some(csr_table), config.trace_len_log),
                dump_ssa_witness_eval_form::<Mersenne31Field, _, SECOND_WORD_BITS_FIVE>(machine)
            ),
            _ => panic!("Unsupported second word bits: {}", config.second_word_bits),
        }
    };

    let full_stream = derive_from_ssa(&ssa_forms, &compiled_circuit, false);

    let circuit_layout = verifier_generator::generate_from_parts(&compiled_circuit);
    let quotient = verifier_generator::generate_inlined(compiled_circuit.clone());

    let mut dir = dir.to_string();
    dir.push_str("/");

    let mut layout_filename = dir.clone();
    layout_filename.push_str(&config.layout_file_name());
    serialize_to_file(&compiled_circuit, &layout_filename);

    let mut ssa_filename = dir.clone();
    ssa_filename.push_str(&config.ssa_file_name());
    serialize_to_file(&ssa_forms, &ssa_filename);

    let mut generated_filename = dir.clone();
    generated_filename.push_str(&config.witness_gen_file_name());

    std::fs::File::create(&generated_filename)
        .unwrap()
        .write_all(&format_rust_code(&full_stream.to_string()).unwrap().as_bytes())
        .unwrap();

    let mut generated_filename = dir.clone();
        generated_filename.push_str(&config.circuit_layout_file_name());
    
    std::fs::File::create(&generated_filename)
        .unwrap()
        .write_all(&format_rust_code(&circuit_layout.to_string()).unwrap().as_bytes())
        .unwrap();

    let mut generated_filename = dir;
        generated_filename.push_str(&config.quotient_file_name());
    
    std::fs::File::create(&generated_filename)
        .unwrap()
        .write_all(&format_rust_code(&quotient.to_string()).unwrap().as_bytes())
        .unwrap();
}
