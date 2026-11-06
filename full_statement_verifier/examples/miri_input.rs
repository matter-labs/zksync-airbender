//! Decode and verify the committed fixture outside Miri, then embed its NDS.
#[path = "../tests/common/hashed_fibonacci.rs"]
mod fixture;
#[path = "../tests/common/miri_stream.rs"]
mod miri_stream;

fn main() {
    let mut args = std::env::args_os().skip(1);
    let output = args.next().expect("usage: miri_input OUTPUT_PATH");
    assert!(args.next().is_none(), "usage: miri_input OUTPUT_PATH");
    let (nds, manifest) = fixture::load(&fixture::fixture_dir());
    let input = miri_stream::encode(&manifest.expected_output, &nds);
    let (expected, decoded) = miri_stream::decode(&input);
    assert_eq!(expected, manifest.expected_output);
    assert!(decoded.eq(nds.iter().copied()));
    std::fs::write(&output, &input).unwrap();
    println!(
        "verified full FSV output and {} NDS words; wrote {} bytes",
        nds.len(),
        input.len()
    );
}
