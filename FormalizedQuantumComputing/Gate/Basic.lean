/-
Copyright (c) 2026 Haruna Imai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruna Imai
-/

import FormalizedQuantumComputing.Gate.Defs
import FormalizedQuantumComputing.Gate.Pauli.Defs
import FormalizedQuantumComputing.StateVector.Defs

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

end Gate
