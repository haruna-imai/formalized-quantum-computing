/-
Copyright (c) 2026 Haruna Imai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruna Imai
-/

import FormalizedQuantumComputing.StateVector.Defs
import FormalizedQuantumComputing.StateVector.Basic
import FormalizedQuantumComputing.Gate.Defs

/-!
# Pauli gates

This file defines the Pauli X and Z matrices, proves their unitarity,
and constructs the corresponding single-qubit quantum gates.
-/

namespace Gate.Pauli
open StateVector

/-! ## Pauli X gate -/

/-- The X matrix. -/
def XMatrix :
    Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ :=
     outer ket1 ket0 + outer ket0 ket1

/-- The X matrix satisfies `XMatrixᴴ * XMatrix = 1`. -/
theorem star_mul_XMatrix : star XMatrix * XMatrix = 1 := by
  rw [XMatrix]
  simp_rw [star_add]
  simp_rw [Matrix.add_mul, Matrix.mul_add]
  simp_rw [StateVector.star_outer]
  simp_rw [StateVector.outer_mul_outer]
  simp_rw [inner_ket0_ket0, inner_ket0_ket1, inner_ket1_ket0, inner_ket1_ket1]
  simp only [one_smul, zero_smul, add_zero, zero_add]
  exact StateVector.computationalBasis_one_qubit_outerproduct_sum

/-- The X matrix satisfies `XMatrix * XMatrixᴴ = 1`. -/
theorem XMatrix_mul_star : XMatrix * star XMatrix = 1 := by
  rw [XMatrix]
  simp_rw [star_add]
  simp_rw [Matrix.add_mul, Matrix.mul_add]
  simp_rw [StateVector.star_outer]
  simp_rw [StateVector.outer_mul_outer]
  simp_rw [inner_ket0_ket0, inner_ket0_ket1, inner_ket1_ket0, inner_ket1_ket1]
  simp
  simpa [add_comm] using
   StateVector.computationalBasis_one_qubit_outerproduct_sum

/-- The Pauli X gate as a unitary operator on one qubit. -/
def X : QuantumGate 1 := by
  refine ⟨XMatrix, ?_⟩
  unfold QuantumGate Matrix.unitaryGroup unitary
  change star XMatrix * XMatrix = 1 ∧
    XMatrix * star XMatrix = 1
  exact ⟨star_mul_XMatrix, XMatrix_mul_star⟩

/-! ## Pauli Z gate -/

/-- The Z matrix. -/
def ZMatrix :
    Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ :=
     outer ket0 ket0 - outer ket1 ket1

/-- The Z matrix satisfies `ZMatrixᴴ * ZMatrix = 1`. -/
theorem star_mul_ZMatrix : star ZMatrix * ZMatrix = 1 := by
  rw [ZMatrix]
  simp_rw [star_sub]
  simp_rw [Matrix.sub_mul, Matrix.mul_sub]
  simp_rw [StateVector.star_outer]
  simp_rw [StateVector.outer_mul_outer]
  simp_rw [inner_ket0_ket0, inner_ket0_ket1, inner_ket1_ket0, inner_ket1_ket1]
  simp only [one_smul, zero_smul, sub_zero, zero_sub, sub_neg_eq_add]
  exact StateVector.computationalBasis_one_qubit_outerproduct_sum

/-- The Z matrix satisfies `ZMatrix * ZMatrixᴴ = 1`. -/
theorem ZMatrix_mul_star : ZMatrix * star ZMatrix = 1 := by
  rw [ZMatrix]
  simp_rw [star_sub]
  simp_rw [Matrix.sub_mul, Matrix.mul_sub]
  simp_rw [StateVector.star_outer]
  simp_rw [StateVector.outer_mul_outer]
  simp_rw [inner_ket0_ket0, inner_ket0_ket1, inner_ket1_ket0, inner_ket1_ket1]
  simp only [one_smul, zero_smul, sub_zero, zero_sub, sub_neg_eq_add]
  exact StateVector.computationalBasis_one_qubit_outerproduct_sum

/-- The Pauli Z gate as a unitary operator on one qubit. -/
def Z : QuantumGate 1 := by
  refine ⟨ZMatrix, ?_⟩
  unfold QuantumGate Matrix.unitaryGroup unitary
  change star ZMatrix * ZMatrix = 1 ∧
    ZMatrix * star ZMatrix = 1
  exact ⟨star_mul_ZMatrix, ZMatrix_mul_star⟩

end Gate.Pauli
