# Introduction
This module is the the prover core of Taiko prover. It can receive the tasks from ZKPool-Prover.

Currently, the ZKPool-Prover links to Taiko Prover Core via API.

Refer to the API of `generate_proof` under `prover/src/shared_state.rs`

# Build & Test
```bash
wget https://storage.googleapis.com/zkevm-circuits-keys/kzg_bn254_22.srs -P ./prover/
cargo test --release test_generate_proof -- --nocapture
```
