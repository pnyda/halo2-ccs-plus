# halo2ccs
Convert a Plonkish circuit written in [Halo2](https://zcash.github.io/halo2/) into a [CCS](https://eprint.iacr.org/2023/552) circuit for [sonobe](https://github.com/privacy-scaling-explorations/sonobe).

[📕 rustdoc](https://pnyda.github.io/halo2-ccs-plus/halo2ccs)　[📗 ethresearch](https://ethresear.ch/t/transpiling-a-halo2-circuit-into-ccs/21963)　[📘 Usage](https://github.com/pnyda/halo2-ccs-plus/blob/develop/tests/fibonacci.rs#L24)

*This is an unaudited experimentation. You should not use it in production unless you can audit the code by yourself!*

This crate works on [my fork of halo2](https://github.com/pnyda/halo2/tree/ccs) because some of the private members needed to be accessible from external crate. If you wish to convert your circuit you have to add to Cargo.toml
```toml
[dependencies]
halo2_proofs = { git = "https://github.com/pnyda/halo2.git", branch = "ccs" }
halo2_gadgets = { git = "https://github.com/pnyda/halo2.git", branch = "ccs" }
```

If you need to switch dependencies of dependencies at once then you can use:
```toml
[patch.crates-io]
halo2_proofs = { git = "https://github.com/pnyda/halo2.git", branch = "ccs" }
halo2_gadgets = { git = "https://github.com/pnyda/halo2.git", branch = "ccs" }
```

# test
The test code uses rayon internally, so I recommend you to run `cargo test` in single threaded mode.
```sh
cargo test -- --test-threads=1 --nocapture
```