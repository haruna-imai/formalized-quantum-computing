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

/-- The Hadamard (H) matrix. -/
noncomputable def HMatrix :
    Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ :=
  (1 / Real.sqrt 2 : ℂ) •
    (outer ket0 ket0 +
     outer ket1 ket0 +
     outer ket0 ket1 -
     outer ket1 ket1)

/-- The squared norm of the normalization coefficient of the Hadamard matrix. -/
lemma hadamard_coefficient_norm_sq :
    star (1 / (↑(Real.sqrt 2) : ℂ)) *
      (1 / (↑(Real.sqrt 2) : ℂ)) = (1 / 2 : ℂ) := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrtC : (↑(Real.sqrt 2) : ℂ) ^ 2 = (2 : ℂ) := by
    exact_mod_cast hsqrt
  simp only [Complex.star_def, map_div₀, map_one, Complex.conj_ofReal]
  rw [div_mul_div_comm, ← pow_two (↑(Real.sqrt 2) : ℂ), hsqrtC]
  norm_num

/- The Hadamard matrix satisfies `HMatrixᴴ * HMatrix = 1`. --/
theorem star_mul_HMatrix : star HMatrix * HMatrix = 1 := by
  rw [HMatrix]
  rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hadamard_coefficient_norm_sq]
  simp_rw [star_sub, star_add]
  simp_rw [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add]
  simp_rw [StateVector.star_outer]
  simp_rw [StateVector.outer_mul_outer]
  simp_rw [inner_ket0_ket0, inner_ket0_ket1, inner_ket1_ket0, inner_ket1_ket1]
  simp
  calc
    (2⁻¹ : ℂ) •
     (outer ket0 ket0 + outer ket0 ket0 +
      (outer ket1 ket0 + outer ket1 ket1) -
       (outer ket1 ket0 - outer ket1 ket1))
       =
        outer ket0 ket0 + outer ket1 ket1 := by
        module
    _ = 1 := StateVector.computationalBasis_one_qubit_outerproduct_sum

/- The Hadamard matrix satisfies `HMatrix * HMatrixᴴ = 1`. --/
theorem HMatrix_mul_star : HMatrix * star HMatrix = 1 := by
  rw [HMatrix]
  rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm, hadamard_coefficient_norm_sq]
  simp_rw [star_sub, star_add]
  simp_rw [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add]
  simp_rw [StateVector.star_outer]
  simp_rw [StateVector.outer_mul_outer]
  simp_rw [inner_ket0_ket0, inner_ket0_ket1, inner_ket1_ket0, inner_ket1_ket1]
  simp
  calc
    (2⁻¹ : ℂ) •
     (outer ket0 ket0 + outer ket0 ket1 +
      (outer ket1 ket0 + outer ket1 ket1) +
       (outer ket0 ket0 - outer ket0 ket1) -
        (outer ket1 ket0 - outer ket1 ket1))
        =
        outer ket0 ket0 + outer ket1 ket1 := by
        module
    _ = 1 := StateVector.computationalBasis_one_qubit_outerproduct_sum

/-  The Hadamard (H) gate as a unitary operator on one qubit. --/
noncomputable def H : QuantumGate 1 := by
  refine ⟨HMatrix, ?_⟩
  unfold QuantumGate Matrix.unitaryGroup unitary
  change star HMatrix * HMatrix = 1 ∧
    HMatrix * star HMatrix = 1
  exact ⟨star_mul_HMatrix, HMatrix_mul_star⟩

/-- The controlled-NOT (CNOT) matrix. -/
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

/- The CNOT matrix satisfies `CNOTMatrix * CNOTMatrixᴴ = 1`. --/
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
