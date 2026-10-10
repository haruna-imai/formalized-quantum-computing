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
import FormalizedQuantumComputing.StateVector.Basic
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
def apply {n : ℕ}
    (U : QuantumGate n) (ψ : StateVector.State n) : StateVector.State n :=
  applyMatrix U ψ

-- Hadamardの定義
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ := !![1/√2, 1/√2; 1/√2, -1/√2]

def CNOTMatrix : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  outer (tensor ket0 ket0) (tensor ket0 ket0) +
  outer (tensor ket0 ket1) (tensor ket0 ket1) +
  outer (tensor ket1 ket1) (tensor ket1 ket0) +
  outer (tensor ket1 ket0) (tensor ket1 ket1)

/- The CNOT matrix satisfies `CNOTMatrixᴴ * CNOTMatrix = 1`. --/
theorem star_mul_CNOTMatrix : star CNOTMatrix * CNOTMatrix = 1 := by
  rw [CNOTMatrix]
  simp only [star_add]
  simp_rw [Matrix.add_mul, Matrix.mul_add]
  simp_rw [StateVector.star_outer]
  simp_rw [StateVector.outer_mul_outer]
  simp_rw [inner_tensor]
  simp_rw [inner_ket0_ket0, inner_ket0_ket1, inner_ket1_ket0, inner_ket1_ket1]
  simp
  rw [computationalBasis_two_qubit_outerproduct_sum]

/- The CNOT matrix satisfies `CNOTMatrix = 1 * CNOTMatrixᴴ`. --/
theorem CNOTMatrix_mul_star : CNOTMatrix * star CNOTMatrix = 1 := by
  rw [CNOTMatrix]
  simp only [star_add]
  simp_rw [Matrix.add_mul, Matrix.mul_add]
  simp_rw [StateVector.star_outer]
  simp_rw [StateVector.outer_mul_outer]
  simp_rw [inner_tensor]
  simp_rw [inner_ket0_ket0, inner_ket0_ket1, inner_ket1_ket0, inner_ket1_ket1]
  simp
  simpa [add_comm, add_left_comm, add_assoc] using
    computationalBasis_two_qubit_outerproduct_sum

/-  The controlled-NOT (CNOT) gate as a unitary operator on two qubits. --/
def CNOT : QuantumGate 2 := by
  refine ⟨CNOTMatrix, ?_⟩
  unfold QuantumGate Matrix.unitaryGroup unitary
  change star CNOTMatrix * CNOTMatrix = 1 ∧
    CNOTMatrix * star CNOTMatrix = 1
  exact ⟨star_mul_CNOTMatrix, CNOTMatrix_mul_star⟩

end Gate
