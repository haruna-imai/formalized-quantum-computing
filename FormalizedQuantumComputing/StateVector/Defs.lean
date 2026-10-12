/-
Copyright (c) 2026 Haruna Imai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruna Imai
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# State vectors

This file defines state vectors and normalized states, single-qubit states, and operations
on state vectors for quantum computation.
-/

namespace StateVector
open Kronecker
open scoped Matrix
open scoped ComplexConjugate

/-! ## State vectors -/

/-- An `n`-qubit state vector without a normalization assumption. -/
abbrev State (n : ℕ) :=
  EuclideanSpace ℂ (Fin n → Fin 2)

/-- An `n`-qubit state vector with unit norm. -/
structure NormalizedState (n : ℕ) where
  vec : State n
  normalized : ‖vec‖ = 1

/-! ## Single-qubit states -/

/-- The computational basis state `|i⟩`. -/
def ket (i : Fin 2) : State 1 :=
  WithLp.toLp 2 (fun x =>
    if x 0 = i then 1 else 0)

/-- The computational basis state `|0⟩`. -/
def ket0 : State 1 := ket 0

/-- The computational basis state `|1⟩`. -/
def ket1 : State 1 := ket 1

/-- `|+⟩` -/
noncomputable def ketplus : State 1 :=
  (1 / √2 : ℂ) • ket0 + (1 / √2 : ℂ) • ket1

/-- `|-⟩` -/
noncomputable def ketminus : State 1 :=
  (1 / √2 : ℂ) • ket0 - (1 / √2 : ℂ) • ket1

/-! ## Operations on state vectors -/

/-- The tensor product of `ψ` and `φ` -/
def tensor {m n : ℕ} (ψ : State m) (φ : State n) : State (m + n) :=
  WithLp.toLp 2 (fun x =>
    ψ.ofLp (fun i : Fin m => x (Fin.castAdd n i)) *
    φ.ofLp (fun j : Fin n => x (Fin.natAdd m j)))

/-- The outer product of `ψ_1` and `ψ_2` -/
def outer {n : ℕ} (ψ_1 ψ_2 : State n) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun i j =>
    ψ_1.ofLp i * conj (ψ_2.ofLp j)

/-- Applies the matrix `A` to the state `ψ`. -/
def applyMatrix {n : ℕ}
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (ψ : State n) : State n :=
  WithLp.toLp 2 (A *ᵥ ψ.ofLp)

end StateVector
