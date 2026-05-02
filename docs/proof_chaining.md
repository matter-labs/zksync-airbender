# Proof chaining

a.k.a combining proofs together.

The regular flow of proving the program is following:

```
program -> basic proof -> recursion proofs (many rounds).
```

Then we do steps to "wrap it" in a SNARK proof:

```
-> "final" proof (couple rounds) -> boojum verifier -> compressor -> snark.
```

This flow works correctly, but in production it can become too slow & expensive if we applied it for each block separately (as this means that we'd have to pay SNARK generation & L1 verification costs for each block).

Instead, what we can do, is try to combine a bunch of program FRI proofs, into a single FRI, and than wrap that one instead.

It'd look like this:

```
program (block 1) -> basic proof -> recursion proofs -\
                                                       \
program (block 2) -> basic proof -> recursion proofs ----->
                                                       /
program (block 3) -> basic proof -> recursion proofs -/
```


## How to combine proofs

As proof verification is also a risc program - combining proofs means that we simply verify multiple "child" proofs within a single program.

You can actually see it in the tools/verifier program:

```rust
// First - verify both proofs (keep reading from the CSR).
let output1 = full_statement_verifier::verify_recursion_layer();
let output2 = full_statement_verifier::verify_recursion_layer();
```

We have verified the program, but now we have to figure out what should be the outputs.

Outputs consist of 2 parts:
* first 8 slots are used to pass user program's output (a.k.a public input)
* second 8 slots are used to pass the verification chain (which is a keccak of user program combined with all verifier binaries that were used)

As we're "combining" child proofs, we should do something that is matching this behavior.

This means that for the first 8 slots, we'll output the keccak of the combination of the slots from the child proofs.

```rust
let mut hasher = Keccak32::new();
hasher.update(&[0u32]); // 0 after shift
for i in 0..7 {
    hasher.update(&[output1[i]]);
}
hasher.update(&[0u32]); // 0 after shift
for i in 0..7 {
    hasher.update(&[output2[i]]);
}
```

(we actually use only 7 slots - this is due to SNARK limitations - where its public inputs can fit only 224 bits)

For the second 8 slots, we'll do two things:

We'll check that both inputs are coming from the same "chain" of computations:

```rust
// Proving chains must be equal.
for i in 8..16 {
    assert_eq!(output1[i], output2[i], "Proving chains must be equal");
}
```

and then we'll output this data directly:

```rust
result[8..16].copy_from_slice(&output1[8..16]);
```

## Universal verifier

In theory, the code above (combining proofs), can be done in separate binary, completely independent from the regular verifiers.

Unfortunately doing this, would mean that th final proving chain slots would differ, depending on how many times we did the combination, as the rule for proving chain hash is:

```rust
if current_program != last_program {
    proving_chain = keccak(previous_proving_chain || current_program)
}
```

But if we put the combination logic **together** in the same program as recursion proofs etc, this means that the final proving chain would always be the same, giving us flexibility to apply as many or as little mergings as we need.


## Future work

Currently the code in the verifier is merging exactly 2 FRI proofs together. As an optimisation, we'll add the option to merge N FRI proofs together soon.
