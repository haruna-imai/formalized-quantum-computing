/-
Copyright (c) 2026 Haruna Imai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruna Imai
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Complex.Basic

/-!
# Pauli matrices

This file defines Pauli matrices for quantum computation.
-/

namespace Gate.Pauli

-- Pauli X の定義
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

-- Pauli Z の定義
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

end Gate.Pauli
