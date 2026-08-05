use gpu_gkr_compiler::manual::parse_args;

fn base() -> Vec<String> {
    "--circuit tiny --layout tiny.json --output tiny_schedule_b16_gkr.json --seed 7 \
     --cache-cells 16 --population 2 --evaluations 8"
        .split_whitespace()
        .map(str::to_owned)
        .collect()
}

#[test]
fn required_inputs_are_hard_errors() {
    for required in ["--seed", "--cache-cells", "--output"] {
        let mut args = base();
        let index = args.iter().position(|arg| arg == required).unwrap();
        args.drain(index..=index + 1);
        assert!(parse_args(args).is_err(), "{required}");
    }
}

#[test]
fn output_name_is_exact() {
    let mut args = base();
    let index = args.iter().position(|arg| arg == "--output").unwrap() + 1;
    args[index] = "another.json".into();
    assert!(parse_args(args).is_err());
}
