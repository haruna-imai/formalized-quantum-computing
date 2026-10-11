/-
Copyright (c) 2026 Haruna Imai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruna Imai
-/

import FormalizedQuantumComputing.Gate.Pauli.Defs

/-!
# Basic properties of Pauli matrices

This file proves basic properties of Pauli matrices.
-/

namespace Gate.Pauli

/-- The Pauli X matrix is self-adjoint -/
theorem XMatrix_self_adjoint :
  star XMatrix = XMatrix := by
    unfold XMatrix
    simp_rw [star_add]
    simp_rw [StateVector.star_outer]
    module

/-- The Pauli X gate satisfies `X² = 1`. -/
theorem X_mul_X_eq_id : X * X = 1 := by
  apply Subtype.ext
  change (XMatrix * XMatrix = 1)
  nth_rewrite 1 [← XMatrix_self_adjoint]
  exact star_mul_XMatrix

/-- The Pauli Z matrix is self-adjoint. -/
theorem ZMatrix_self_adjoint :
  star ZMatrix = ZMatrix := by
    unfold ZMatrix
    simp_rw [star_sub]
    simp_rw [StateVector.star_outer]

/-- The Pauli Z gate satisfies `Z² = 1`. -/
theorem Z_mul_Z_eq_id : Z * Z = 1 := by
  apply Subtype.ext
  change (ZMatrix * ZMatrix = 1)
  nth_rewrite 1 [← ZMatrix_self_adjoint]
  exact star_mul_ZMatrix

end Gate.Pauli
