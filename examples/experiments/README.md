# ZK verifier example.

Verifies the riscV circuit FRI proof within riscV.


This example is special - as verification requires to run on the `mini` machine, and has to be compiled in release mode.


It is also using special `+zimop` operations (flag in .cargo/config.toml)

Make sure to use profile cli (or --release) when compiling

```
cargo objcopy --profile cli  -- -O binary app.bin
```


Make sure to use machine `mini` when running / proving.
```
.... --machine mini 
```
