/-
Copyright (c) 2026 Haruna Imai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruna Imai
-/

import FormalizedQuantumComputing.Gate.Defs
import FormalizedQuantumComputing.Gate.Pauli.Defs
import FormalizedQuantumComputing.StateVector.Defs
import FormalizedQuantumComputing.StateVector.Basic
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

/-- Gate application is additive in the state vector.

`Gate.apply U (v + w) = Gate.apply U v + Gate.apply U w` -/
theorem apply_add {n : ℕ}
    (U : QuantumGate n) (ψ φ : StateVector.State n) :
    Gate.apply U (ψ + φ) =
      Gate.apply U ψ + Gate.apply U φ := by
  exact StateVector.applyMatrix_add_state U ψ φ

/-- Applying a Gate to a scalar multiple of a state vector
equals the scalar multiple of the Gate application.

`Gate.apply U (c • v) = c • Gate.apply U v` -/
theorem apply_smul {n : ℕ}
    (U : QuantumGate n) (c : ℂ) (ψ : StateVector.State n) :
    Gate.apply U (c • ψ) =
      c • Gate.apply U ψ := by
  exact StateVector.applyMatrix_smul_state c U ψ

-- General properties of quantum gates

/-- Applying the tensor product of two quantum gates to a tensor product
of state vectors gives the tensor product of their individual applications.

`Gate.apply (Gate.tensor U V) (StateVector.tensor ψ φ) =
  StateVector.tensor (Gate.apply U ψ) (Gate.apply V φ)`
-/
theorem apply_tensor {m n : ℕ}
  (U : QuantumGate m) (V : QuantumGate n)
    (ψ : StateVector.State m) (φ : StateVector.State n) :
      Gate.apply (Gate.tensor U V) (StateVector.tensor ψ φ) =
        StateVector.tensor (Gate.apply U ψ) (Gate.apply V φ) := by
  unfold Gate.apply
  change
    applyMatrix (tensorMatrix U V) (StateVector.tensor ψ φ) =
      StateVector.tensor (applyMatrix U ψ) (applyMatrix V φ)
  ext x
  unfold StateVector.applyMatrix
  unfold StateVector.tensor
  -- Express both sides in terms of matrix entries and state amplitudes.
  change
    (∑ y, (U (splitBits m n x).1 (splitBits m n y).1 *
      V (splitBits m n x).2 (splitBits m n y).2) *
      (ψ.ofLp (splitBits m n y).1 * φ.ofLp (splitBits m n y).2)) =
    (∑ a, U (splitBits m n x).1 a * ψ.ofLp a) *
      (∑ b, V (splitBits m n x).2 b * φ.ofLp b)
  -- Reindex the sum by splitting the bit string into two parts.
  rw [Equiv.sum_comp (splitBits m n) (fun y =>
    (U (splitBits m n x).1 y.1 * V (splitBits m n x).2 y.2) *
      (ψ.ofLp y.1 * φ.ofLp y.2)), Fintype.sum_prod_type,
    Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

-- Basic properties of specific gates

/-- Applying the identity quantum gate leaves a state unchanged. -/
theorem apply_one {n : ℕ} (ψ : StateVector.State n) :
    Gate.apply (1 : QuantumGate n) ψ = ψ := by
  simp [Gate.apply, StateVector.applyMatrix]

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

/-- Applying the Hadamard gate to `|0⟩` gives the `|+⟩` state.

`Gate.apply H ket0 = ketplus`
-/
theorem H_ket0_eq_ketplus : Gate.apply H ket0 = ketplus :=by
  rw [Gate.apply]
  rw [H]
  change (applyMatrix (HMatrix) ket0 = ketplus)
  rw [HMatrix]
  rw [applyMatrix_smul]
  simp_rw [applyMatrix_sub, applyMatrix_add]
  simp_rw [Matrix.outer_apply]
  simp only [inner_ket0_ket0, inner_ket1_ket0]
  rw [ketplus]
  simp

/-- Applying the CNOT gate to `|0⟩|0⟩` gives the `|0⟩|0⟩` state.

`Gate.apply CNOT (tensor ket0 ket0) = tensor ket0 ket0`
-/
theorem CNOT_ket00_eq_ket00 :
  Gate.apply CNOT (tensor ket0 ket0)
    = tensor ket0 ket0 := by
  rw [Gate.apply]
  rw [CNOT]
  change (applyMatrix CNOTMatrix (tensor ket0 ket0) = tensor ket0 ket0)
  rw [CNOTMatrix]
  simp_rw [applyMatrix_add]
  simp_rw [Matrix.outer_apply]
  simp_rw [StateVector.inner_tensor (n := 1)]
  simp only [inner_ket0_ket0, inner_ket1_ket0]
  simp

/-- Applying the CNOT gate to `|1⟩|0⟩` gives the `|1⟩|1⟩` state.

`Gate.apply CNOT (tensor ket1 ket0) = tensor ket1 ket1`
-/
theorem CNOT_ket10_eq_ket11 :
  Gate.apply CNOT (tensor ket1 ket0)
    = tensor ket1 ket1 := by
  rw [Gate.apply]
  rw [CNOT]
  change (applyMatrix CNOTMatrix (tensor ket1 ket0) = tensor ket1 ket1)
  rw [CNOTMatrix]
  simp_rw [applyMatrix_add]
  simp_rw [Matrix.outer_apply]
  simp_rw [StateVector.inner_tensor (n := 1)]
  simp only [inner_ket0_ket0, inner_ket1_ket0, inner_ket0_ket1, inner_ket1_ket1]
  simp

/-- Applying the Hadamard gate to the first qubit of `|00⟩`,
followed by the CNOT gate, produces the Bell state.

`Gate.apply CNOT
  (Gate.apply (Gate.tensor H (1 : QuantumGate 1))
    (tensor ket0 ket0)) =
  (1 / √2 : ℂ) • (tensor ket0 ket0) +
  (1 / √2 : ℂ) • (tensor ket1 ket1)` -/
theorem Bell_State :
    Gate.apply CNOT
      (Gate.apply (Gate.tensor H (1 : QuantumGate 1))
        (tensor ket0 ket0)) =
      (1 / √2 : ℂ) • (tensor ket0 ket0) +
      (1 / √2 : ℂ) • (tensor ket1 ket1) := by
  rw [apply_tensor, H_ket0_eq_ketplus, ketplus]
  rw [StateVector.tensor_add_left]
  simp_rw [StateVector.tensor_smul_left, apply_one]
  rw [apply_add]
  simp_rw [apply_smul]
  rw [CNOT_ket00_eq_ket00, CNOT_ket10_eq_ket11]

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
