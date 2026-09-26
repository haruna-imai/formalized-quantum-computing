/-
Copyright (c) 2026 Haruna Imai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruna Imai
-/

import FormalizedQuantumComputing.Gate.Defs
import FormalizedQuantumComputing.Gate.Pauli.Defs
import FormalizedQuantumComputing.StateVector.Defs
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Basic properties of quantum gates

This file proves basic properties of quantum Gates.
-/

namespace Gate
open Pauli
open StateVector
open Kronecker

-- H^2 = I
theorem H_mul_H_eq_id : H * H = 1 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, Matrix.mul_apply] <;>
    field_simp <;>
    norm_cast <;>
    rw [hsqrt] <;>
    norm_num

-- HXH = Z
theorem H_mul_X_mul_H_eq_Z : H * X * H = Z := by
  -- 実数上で√2 ^ 2 = 2を補題として証明
  have hsqrt : √2 ^ 2 = 2 :=by
    apply Real.sq_sqrt
    linarith
  -- 行列の要素の比較をすることで等式証明を行う
  ext i j
  simp_rw [Matrix.mul_apply]
  fin_cases i <;>
  fin_cases j <;>
  simp [H, X, Z] <;>
  field_simp <;>
  norm_num <;>
  norm_cast <;>
  rw[hsqrt]

-- HZH = X
theorem H_mul_Z_mul_H_eq_X : H * Z * H = X :=by
  -- H * (H * X * H) * H = (H * H) * X * (H * H)
  have h: H * (H * X * H) * H = (H * H) * X * (H * H) :=  by
    simp_rw[Matrix.mul_assoc]
  rw[← H_mul_X_mul_H_eq_Z]
  rw[h]
  rw[H_mul_H_eq_id]
  rw[Matrix.one_mul]
  rw[Matrix.mul_one]

-- CNOT^2 = I
-- CNOT = |00><00| + |01><01| + |11><10| +|10><11|
theorem CNOT_mul_CNOT_eq_id : CNOT * CNOT = 1 := by
  rw [CNOT]
  simp_rw [Matrix.add_mul, Matrix.mul_add]
  simp_rw [Matrix.outerproduct_mul_outerproduct]
  simp_rw [Matrix.kronecker_conjTranspose_mul_kronecker]
  simp_rw [ket0star_mul_ket0, ket1star_mul_ket0, ket0star_mul_ket1, ket1star_mul_ket1]
  simp
  simpa [add_assoc, add_comm, add_left_comm]
   using Matrix.computationalBasis_two_qubit_outerproduct_sum

variable (n : ℕ)
variable (U : Gate.QuantumGate n) (ψ : StateVector.State n)

-- U^* (U ψ) = ψ
/-- Applying the adjoint of a quantum gate after the gate itself
returns the original state. -/
lemma adjoint_apply_apply :
    Matrix.toEuclideanLin
        (Matrix.conjTranspose
          (U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ))
        (Gate.apply U ψ)
      = ψ := by
  rw [Matrix.toLpLin_apply]
  rw [Gate.apply]
  rw [Matrix.mulVec_mulVec]
  rw [← Matrix.star_eq_conjTranspose
    (U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)]
  rw [U.property.1]
  simp

-- <Uψ, Uψ> = <ψ, ψ>
/-- A quantum gate preserves the self-inner product of a state. -/
lemma gate_preserves_self_inner :
    inner ℂ (Gate.apply U ψ) (Gate.apply U ψ) =
      inner ℂ ψ ψ := by
  -- <Uψ, Uψ> = <ψ, U^* (U ψ)>
  have h1 : inner ℂ (Gate.apply U ψ) (Gate.apply U ψ) =
    inner ℂ ψ
      (Matrix.toEuclideanLin
        (Matrix.conjTranspose
          (U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ))
            (Gate.apply U ψ)) := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint
      (U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)]
    rw [LinearMap.adjoint_inner_right]
    rfl
  rw [h1]
  rw [adjoint_apply_apply]

-- U:Unitary → ||Uψ|| = ||ψ||
/-- A quantum gate preserves the norm of a state vector. -/
theorem gate_preserves_norm : ‖Gate.apply U ψ‖ = ‖ψ‖ := by
  have hUψ :=
    norm_sq_eq_re_inner (𝕜 := ℂ) (Gate.apply U ψ)
  have hψ :=
    norm_sq_eq_re_inner (𝕜 := ℂ) ψ
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hUψ, hψ]
  rw [gate_preserves_self_inner]

end Gate
