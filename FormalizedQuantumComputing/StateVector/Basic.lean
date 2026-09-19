/-
Copyright (c) 2026 Haruna Imai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruna Imai
-/

import FormalizedQuantumComputing.Gate.Defs
import FormalizedQuantumComputing.Gate.Pauli.Defs
import FormalizedQuantumComputing.StateVector.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Basic properties of state vectors

This file proves basic properties of state vectors and includes calculations involving
Bell states.
-/

namespace StateVector

open Gate
open Gate.Pauli
open Kronecker
open scoped Matrix

-- H |0> = |+>
theorem H_ket0_eq_ketplus : H * ket0 = ketplus :=by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i, j <;>
  simp [H, ket0, ketplus]

-- CNOT |0>|0> = |0>|0>
theorem CNOT_ket00_eq_ket00 : CNOT * (ket0 ⊗ₖ ket0) = ket0 ⊗ₖ ket0 :=by
  rw [CNOT]
  simp_rw [Matrix.add_mul]
  simp_rw [Matrix.mul_assoc]
  simp_rw [Matrix.conjTranspose_kronecker]
  simp_rw [← Matrix.mul_kronecker_mul]
  simp_rw [ket0star_mul_ket0, ket1star_mul_ket0]
  simp

-- CNOT |1>|0> = |1>|1>
theorem CNOT_ket10_eq_ket11 : CNOT * (ket1 ⊗ₖ ket0) = ket1 ⊗ₖ ket1 :=by
  rw [CNOT]
  simp_rw [Matrix.add_mul]
  simp_rw [Matrix.mul_assoc]
  simp_rw [Matrix.conjTranspose_kronecker]
  simp_rw [← Matrix.mul_kronecker_mul]
  simp_rw [ket0star_mul_ket0, ket1star_mul_ket0, ket0star_mul_ket1, ket1star_mul_ket1]
  simp

theorem Bell_State :
  CNOT * ((H ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * (ket0 ⊗ₖ ket0))
    = (1/√2 : ℂ) • (ket0 ⊗ₖ ket0) + (1/√2 : ℂ) • (ket1 ⊗ₖ ket1) := by
  rw [← Matrix.mul_kronecker_mul]
  rw [H_ket0_eq_ketplus]
  rw [Matrix.one_mul]
  rw [ketplus_eq]
  rw [Matrix.add_kronecker]
  simp_rw [Matrix.smul_kronecker]
  rw [Matrix.mul_add]
  simp_rw [Matrix.mul_smul]
  rw [CNOT_ket00_eq_ket00, CNOT_ket10_eq_ket11]

end StateVector
