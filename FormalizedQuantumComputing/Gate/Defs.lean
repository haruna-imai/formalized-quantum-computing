/-
Copyright (c) 2026 Haruna Imai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruna Imai
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import FormalizedQuantumComputing.StateVector.Defs
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# quantum gates

This file defines quantum Gates.
-/

namespace Gate
open Kronecker
open StateVector
open scoped Matrix

variable (n : ℕ)

-- 量子Gateの定義
abbrev QuantumGate := Matrix.unitaryGroup (Fin n → Fin 2) ℂ

/-- Applies a quantum gate to a state vector. -/
def apply {n : ℕ} (U : Gate.QuantumGate n) (ψ : StateVector.State n) :
  StateVector.State n
  := WithLp.toLp 2 (U *ᵥ ψ.ofLp)

-- Hadamardの定義
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ := !![1/√2, 1/√2; 1/√2, -1/√2]

-- CNOT = |00><00| + |01><01| + |11><10| +|10><11|
def CNOT : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((ket0) ⊗ₖ (ket0)) * ((ket0) ⊗ₖ (ket0))ᴴ +
  ((ket0) ⊗ₖ (ket1)) * ((ket0) ⊗ₖ (ket1))ᴴ +
  ((ket1) ⊗ₖ (ket1)) * ((ket1) ⊗ₖ (ket0))ᴴ +
  ((ket1) ⊗ₖ (ket0)) * ((ket1) ⊗ₖ (ket1))ᴴ

end Gate
