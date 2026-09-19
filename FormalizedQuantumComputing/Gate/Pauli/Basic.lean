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

-- X * X = 1
theorem X_mul_X_eq_id : X * X = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;>
  fin_cases j <;>
  simp [X]

end Gate.Pauli
