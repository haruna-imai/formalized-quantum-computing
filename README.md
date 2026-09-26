# Formalized Quantum Computing
[日本語版](README_ja.md)

A Lean 4 library for formalizing basic results in quantum computing.

This project currently focuses on elementary quantum states and quantum gates,
with the goal of exploring the formalization of quantum computing in Lean.

## Status

This project is under development and is being created as part of the author's
study of formalizing quantum computing in Lean.

The library is not yet mature, and its definitions and APIs may change.
Please use it with this in mind.

## Contents

The library currently includes:

- Basic quantum state vectors
- Pauli `X` and `Z` gates
- Hadamard gate
- CNOT gate
- Basic identities for quantum gates, such as `H² = I` and `CNOT² = I`
- Bell-state calculations
- Quantum gates are represented as unitary matrices and preserve the norm of state vectors

## Requirements

This project uses Lean 4 and Mathlib.

The Lean toolchain is specified in `lean-toolchain`, and the versions of
dependencies such as Mathlib are recorded in `lake-manifest.json`.

## Build

From the project root, run:

```bash
lake build
```

## License

This project is licensed under the Apache License 2.0.
See `LICENSE` for details.
