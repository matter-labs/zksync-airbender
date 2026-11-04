use common_constants::rom::ROM_BYTE_SIZE;

pub(super) const RAM_TEST_BASE: u32 = ROM_BYTE_SIZE as u32 + 2048;

pub(super) fn parse_immediate_token(token: &str) -> (String, u32) {
    if let Ok(value) = token.parse::<u32>() {
        (value.to_string(), value)
    } else if let Ok(value) = token.parse::<i32>() {
        (value.to_string(), value as u32)
    } else if let Some(hex) = token.strip_prefix("0x") {
        let value = u32::from_str_radix(hex, 16).unwrap();
        (value.to_string(), value)
    } else if let Some(hex) = token.strip_prefix("-0x") {
        let value = i32::from_str_radix(&format!("-{hex}"), 16).unwrap();
        (value.to_string(), value as u32)
    } else {
        panic!("failed to parse immediate `{token}`");
    }
}

pub(super) fn parse_memory_operand(token: &str) -> (u32, usize) {
    let open = token.find('(').unwrap();
    let close = token.rfind(')').unwrap();

    (
        parse_value_token(&token[..open]),
        parse_register(&token[open + 1..close]),
    )
}

pub(super) fn parse_register(token: &str) -> usize {
    token
        .strip_prefix('x')
        .unwrap_or_else(|| panic!("expected register token, got `{token}`"))
        .parse()
        .unwrap()
}

pub(super) fn parse_value_token(token: &str) -> u32 {
    parse_immediate_token(token).1
}

pub(super) fn instruction_tokens(instruction: &str) -> Vec<String> {
    instruction
        .replace(',', " ")
        .split_whitespace()
        .map(str::to_owned)
        .collect()
}

pub(super) fn split_macro_fields<'a>(line: &'a str, prefix: &str) -> Vec<&'a str> {
    assert!(
        line.starts_with(prefix),
        "expected `{line}` to start with `{prefix}`"
    );
    let open = prefix.len();
    let close = line
        .rfind(')')
        .unwrap_or_else(|| panic!("expected closing `)` in `{line}`"));

    line[open + 1..close]
        .split(',')
        .map(str::trim)
        .filter(|field| !field.is_empty())
        .collect()
}
