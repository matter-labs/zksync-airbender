# ZKsyncOS

This directory contains a binary built from ZKsyncOS repo.

In the future, we should have a proper release pipeline there, so this will no longer be needed.


Binary built from da43fa30036e9fd8d8ca3e350d9ecdc94d089686 (tag: 0.0.2) (June 9).


To rebuild:
* checkout zksync-os repo
* cp app.bin zksync-airbender/examples/zksync_os/app.bin

And in this repo:

```
cargo run --release -p cli generate-vk --bin app.bin --machine standard --output app.vk.json
```

You can also run:
```
cargo run --release -p cli generate-constants app.bin --universal-verifier
```

to see the final verification keys:

```
End params: [4250250141, 1573178321, 1385045928, 2825549767, 443732210, 3784997290, 3165410519, 1422234642]
Aux values: [3936623182, 2900692497, 4203631053, 100485392, 1992734646, 1184593053, 345581557, 682509245]
```
