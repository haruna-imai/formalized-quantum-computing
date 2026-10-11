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

This file proves basic properties of quantum gates.
-/

namespace Gate
open Pauli
open StateVector
open Kronecker

/-- The Hadamard matrix is self-adjoint. -/
theorem HMatrix_self_adjoint :
  star HMatrix = HMatrix := by
    unfold HMatrix
    rw [star_smul]
    simp_rw [star_sub, star_add]
    simp_rw [StateVector.star_outer]
    have hc :
    star (1 / (↑(Real.sqrt 2) : ℂ)) =
      (1 / (↑(Real.sqrt 2) : ℂ)) := by
      simp only [Complex.star_def, map_div₀, map_one, Complex.conj_ofReal]
    rw [hc]
    module

/-- Applying the Hadamard gate twice gives the identity. -/
theorem H_mul_H_eq_id : H * H = 1 := by
  apply Subtype.ext
  change (HMatrix * HMatrix = 1)
  nth_rewrite 1 [← HMatrix_self_adjoint]
  exact star_mul_HMatrix

/-- Conjugating the Pauli X gate by the Hadamard gate gives the Pauli Z gate. -/
theorem H_mul_X_mul_H_eq_Z : H * X * H = Z := by
  apply Subtype.ext
  change (HMatrix * XMatrix * HMatrix = ZMatrix)
  rw [HMatrix, XMatrix, ZMatrix]
  simp_rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hadamard_coefficient_mul_self]
  simp_rw [Matrix.sub_mul, Matrix.add_mul,
    Matrix.mul_sub, Matrix.mul_add]
  simp only [StateVector.outer_mul_outer,
    inner_ket0_ket0, inner_ket0_ket1,
    inner_ket1_ket0, inner_ket1_ket1,
    one_smul, zero_smul, add_zero, zero_add, sub_zero, one_div]
  module

/-- Conjugating the Pauli Z gate by the Hadamard gate gives the Pauli X gate. -/
theorem H_mul_Z_mul_H_eq_X : H * Z * H = X :=by
  have h: H * (H * X * H) * H = (H * H) * X * (H * H) := by
    simp_rw [mul_assoc]
  rw[← H_mul_X_mul_H_eq_Z]
  rw[h]
  rw[H_mul_H_eq_id]
  rw[one_mul, mul_one]

/-- The CNOT matrix is self-adjoint. -/
theorem CNOTMatrix_self_adjoint :
  star CNOTMatrix = CNOTMatrix := by
    unfold CNOTMatrix
    simp_rw [star_add]
    simp_rw [StateVector.star_outer]
    abel

/-- Applying the CNOT gate twice gives the identity. -/
theorem CNOT_mul_CNOT_eq_id : CNOT * CNOT = 1 := by
  apply Subtype.ext
  change (CNOTMatrix * CNOTMatrix = 1)
  nth_rewrite 1 [← CNOTMatrix_self_adjoint]
  exact star_mul_CNOTMatrix

variable (n : ℕ)
variable (U : Gate.QuantumGate n) (ψ : StateVector.State n)

/-- Applying the adjoint of a quantum gate after the gate itself
returns the original state.
`U^* (U ψ) = ψ`. -/
lemma adjoint_apply_apply :
    Matrix.toEuclideanLin
        (Matrix.conjTranspose
          (U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ))
        (Gate.apply U ψ)
      = ψ := by
  rw [Matrix.toLpLin_apply]
  rw [Gate.apply]
  unfold StateVector.applyMatrix
  rw [Matrix.mulVec_mulVec]
  rw [← Matrix.star_eq_conjTranspose
    (U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)]
  rw [U.property.1]
  simp

/-- A quantum gate preserves the self-inner product of a state.
`<Uψ, Uψ> = <ψ, ψ>`. -/
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

/-- A quantum gate preserves the norm of a state vector.
`U:Unitary → ||Uψ|| = ||ψ||`. -/
theorem gate_preserves_norm : ‖Gate.apply U ψ‖ = ‖ψ‖ := by
  have hUψ :=
    norm_sq_eq_re_inner (𝕜 := ℂ) (Gate.apply U ψ)
  have hψ :=
    norm_sq_eq_re_inner (𝕜 := ℂ) ψ
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hUψ, hψ]
  rw [gate_preserves_self_inner]

end Gate
