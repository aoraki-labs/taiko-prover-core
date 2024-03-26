# Introduction
This module is the the prover core of Taiko prover. It can receive the tasks from ZKPool-Prover.

Currently, the ZKPool-Prover links to Taiko Prover Core via API.

Refer to the API of `generate_proof` under `prover/src/shared_state.rs`

# Build
```bash
cargo build --release
```

# Test
```bash
cargo test --release test_generate_proof -- --nocapture
```
```bash
cargo build --bin prover_rpcd --release
```