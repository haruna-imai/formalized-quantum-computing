/-
Copyright (c) 2026 Haruna Imai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruna Imai
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# State vectors

This file provides basic definitions and properties of state vectors for quantum computation.
-/

namespace StateVector
open Kronecker
open scoped Matrix

-- |0> を定義
def ket0 : Matrix (Fin 2) (Fin 1) ℂ := !![1 ; 0]

-- |1> を定義
def ket1 : Matrix (Fin 2) (Fin 1) ℂ := !![0 ; 1]

-- <0|0>
theorem ket0star_mul_ket0 : ket0ᴴ * ket0 = 1 :=by
  ext i j
  rw [Matrix.mul_apply]
  rw [ket0]
  fin_cases i, j
  simp

-- <0|1>
theorem ket0star_mul_ket1 : ket0ᴴ * ket1 = 0 :=by
  ext i j
  rw [Matrix.mul_apply]
  rw [ket0, ket1]
  fin_cases i, j
  simp

-- <1|0>
theorem ket1star_mul_ket0 : ket1ᴴ * ket0 = 0 :=by
  ext i j
  rw [Matrix.mul_apply]
  rw [ket0, ket1]
  fin_cases i, j
  simp

-- <1|1>
theorem ket1star_mul_ket1 : ket1ᴴ * ket1 = 1 :=by
    ext i j
    rw [Matrix.mul_apply]
    rw [ket1]
    fin_cases i, j
    simp

-- |+> を定義
noncomputable def ketplus : Matrix (Fin 2) (Fin 1) ℂ := !![(1/√2 : ℂ) ; (1/√2 : ℂ)]

-- |-> を定義
noncomputable def ketminus : Matrix (Fin 2) (Fin 1) ℂ := !![(1/√2 : ℂ) ; -(1/√2 : ℂ)]

theorem ketplus_eq : ketplus = (1 / √2 : ℂ) • ket0 + (1 / √2 : ℂ) • ket1 := by
  ext i j
  fin_cases i <;>
  fin_cases j <;>
  simp [ketplus, ket0, ket1]

end StateVector

namespace Matrix
open Kronecker
open StateVector

variable {m n p q r s : Type*}

-- (M * Mᴴ) * (N * Nᴴ) = M * (Mᴴ * N) * Nᴴ
theorem outerproduct_mul_outerproduct
  [Fintype m] [Fintype n] {L M N R : Matrix m n ℂ} :
  (L * Mᴴ) * (N * Rᴴ) = L * (Mᴴ * N) * Rᴴ := by
    calc
      (L * Mᴴ) * (N * Rᴴ) = L * (Mᴴ * (N * Rᴴ)) := Matrix.mul_assoc L Mᴴ (N * Rᴴ)
      _ = L * ((Mᴴ * N) * Rᴴ) :=by rw [← Matrix.mul_assoc Mᴴ N Rᴴ]
      _ = L * (Mᴴ * N) * Rᴴ :=by rw [← Matrix.mul_assoc L (Mᴴ * N) Rᴴ]

-- (|a> ⊗ |b>)ᴴ * (|c> ⊗ |d>) = (<a|c>) ⊗ (<b|d>)
theorem kronecker_conjTranspose_mul_kronecker
 [Fintype m] [Fintype p]
 {L : Matrix m n ℂ} {M : Matrix p q ℂ}
 {N : Matrix m r ℂ} {R : Matrix p s ℂ} :
 (L ⊗ₖ M)ᴴ * (N ⊗ₖ R) = (Lᴴ * N) ⊗ₖ (Mᴴ * R) := by
    rw [Matrix.conjTranspose_kronecker]
    rw [Matrix.mul_kronecker_mul]

-- ∑_i|eᵢ><eᵢ| = I₄
-- TODO: 4次元のベクトル空間の標準基底(|00>, |01>, |10>, |11>)を用いて証明を行う方針に変更する。現状は愚直に行列の等式を計算
theorem computationalBasis_two_qubit_outerproduct_sum :
  ket0 ⊗ₖ ket0 * (ket0 ⊗ₖ ket0)ᴴ +
  ket0 ⊗ₖ ket1 * (ket0 ⊗ₖ ket1)ᴴ +
  ket1 ⊗ₖ ket0 * (ket1 ⊗ₖ ket0)ᴴ +
  ket1 ⊗ₖ ket1 * (ket1 ⊗ₖ ket1)ᴴ = 1 :=by
    simp_rw [Matrix.conjTranspose_kronecker]
    simp_rw [← Matrix.mul_kronecker_mul]
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    fin_cases i₁ <;>
    fin_cases i₂ <;>
    fin_cases j₁ <;>
    fin_cases j₂ <;>
    simp [ket0, ket1, Matrix.vecMul]

end Matrix
