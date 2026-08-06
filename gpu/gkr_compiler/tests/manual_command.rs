use gpu_gkr_compiler::manual::parse_args;

fn base() -> Vec<String> {
    "--circuit tiny --layout tiny.json --output tiny_schedule_b4_gkr.json --seed 7 \
     --cache-buckets 4 --population 2 --evaluations 8"
        .split_whitespace()
        .map(str::to_owned)
        .collect()
}

#[test]
fn required_inputs_are_hard_errors() {
    for required in ["--seed", "--cache-buckets", "--output"] {
        let mut args = base();
        let index = args.iter().position(|arg| arg == required).unwrap();
        args.drain(index..=index + 1);
        assert!(parse_args(args).is_err(), "{required}");
    }
}

#[test]
fn cache_budget_uses_e4_buckets() {
    let args = parse_args(base()).unwrap();
    assert_eq!(args.cache_buckets, 4);
}

#[test]
fn output_name_is_exact() {
    let mut args = base();
    let index = args.iter().position(|arg| arg == "--output").unwrap() + 1;
    args[index] = "another.json".into();
    assert!(parse_args(args).is_err());
}
