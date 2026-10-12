# Formalized Quantum Computing

[日本語版](README_ja.md)

An experimental Lean 4 library for formalizing foundational concepts and results in quantum computing.

The project develops reusable definitions and theorems for quantum states, unitary gates, and basic quantum circuits.

## Status

This library is under active development. It provides a small but structured foundation for formalizing quantum computing, rather than a comprehensive quantum computing framework.

Its scope is currently limited, and definitions and APIs may change as the project evolves.

## Contents

The library currently includes:

- State vectors for `n`-qubit systems, normalized states, and basic single-qubit states
- Tensor products of state vectors, outer products, and the action of matrices on states
- Inner-product properties of computational basis states and basic properties of tensor products
- Quantum gates represented by unitary matrices, including the Pauli `X` and `Z`, Hadamard, and CNOT gates
- Tensor products of quantum gates and their action on tensor-product states
- Gate identities, including `X² = I`, `Z² = I`, `H² = I`, and `CNOT² = I`
- Preservation of inner products and norms under unitary quantum gates
- A proof of Bell-state preparation using Hadamard and CNOT gates

## Requirements

This project uses Lean 4 and Mathlib.

The Lean toolchain is specified in `lean-toolchain`, and dependency versions, including Mathlib, are recorded in `lake-manifest.json`.

## Build

From the project root, run:

```bash
lake build
```

## License

This project is licensed under the Apache License 2.0.
See `LICENSE` for details.