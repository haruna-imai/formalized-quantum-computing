/-
Copyright (c) 2026 Haruna Imai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruna Imai
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# State vectors

This file provides basic definitions and properties of state vectors for quantum computation.
-/

namespace StateVector
open Kronecker
open scoped Matrix
open scoped ComplexConjugate

-- 正規化を仮定しない状態ベクトル
abbrev State (n : ℕ) :=
  EuclideanSpace ℂ (Fin n → Fin 2)

-- 正規化済みの状態ベクトル
structure NormalizedState (n : ℕ) where
  vec : State n
  normalized : ‖vec‖ = 1

/-- The tensor product of `ψ` and `φ` -/
def tensor {m n : ℕ} (ψ : State m) (φ : State n) : State (m + n) :=
  WithLp.toLp 2 (fun x =>
    ψ.ofLp (fun i : Fin m => x (Fin.castAdd n i)) *
    φ.ofLp (fun j : Fin n => x (Fin.natAdd m j)))

/-- The outer product of `ψ_1` and `ψ_2` -/
def outer {n : ℕ} (ψ_1 ψ_2 : State n) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun i j =>
    ψ_1.ofLp i * conj (ψ_2.ofLp j)

/-- Applies the matrix `A` to the state `ψ`. -/
def applyMatrix {n : ℕ}
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (ψ : State n) : State n :=
  WithLp.toLp 2 (A *ᵥ ψ.ofLp)

/-- The computational basis state `|i⟩`. -/
def ket (i : Fin 2) : State 1 :=
  WithLp.toLp 2 (fun x =>
    if x 0 = i then 1 else 0)

/-- The computational basis state `|0⟩`. -/
def ket0 : State 1 := ket 0

/-- The computational basis state `|1⟩`. -/
def ket1 : State 1 := ket 1

/-- `⟨i|i⟩ = 1`. -/
theorem inner_ket_self (i : Fin 2) : inner ℂ (ket i) (ket i) = 1 := by
  unfold ket
  rw [PiLp.inner_apply]
  simp only [Fin.isValue, inner_self_eq_norm_sq_to_K, Complex.coe_algebraMap]
  rw [Fintype.sum_eq_single (a := fun _ : Fin 1 => (i : Fin 2))]
  · simp
  · intro x hx
    simp only [Fin.isValue, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, Complex.ofReal_eq_zero, norm_eq_zero, ite_eq_right_iff,
      one_ne_zero, imp_false]
    intro h
    apply hx
    funext i
    fin_cases i
    exact h

/-- `⟨i|j⟩ = 0` if i ≠ j. -/
theorem inner_ket_of_ne {i j : Fin 2} (h : i ≠ j) :
    inner ℂ (ket i) (ket j) = 0 := by
    unfold ket
    rw [PiLp.inner_apply]
    simp only [Fin.isValue, RCLike.inner_apply, MonoidWithZeroHom.map_ite_one_zero, mul_ite,
      mul_one, mul_zero]
    apply Finset.sum_eq_zero
    simp only [Finset.mem_univ, Fin.isValue, ite_eq_right_iff, one_ne_zero,
      imp_false, forall_const]
    intro x x0i x0j
    rw [x0i] at x0j
    exact h x0j

/-- Computational basis states are orthonormal. -/
theorem inner_ket (i j : Fin 2) :
    inner ℂ (ket i) (ket j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst i
    rw [ite_eq_left rfl]
    exact inner_ket_self j
  · rw [ite_eq_right h]
    exact inner_ket_of_ne h

/-- `⟨0|0⟩ = 1`. -/
theorem inner_ket0_ket0 : inner ℂ ket0 ket0 = (1 : ℂ) := by
  unfold ket0
  exact inner_ket 0 0

/-- `⟨0|1⟩ = 0`. -/
theorem inner_ket0_ket1 : inner ℂ ket0 ket1 = (0 : ℂ) := by
  unfold ket0 ket1
  exact inner_ket 0 1

/-- `⟨1|0⟩ = 0`. -/
theorem inner_ket1_ket0 : inner ℂ ket1 ket0 = (0 : ℂ) := by
  unfold ket0 ket1
  exact inner_ket 1 0

/-- `⟨1|1⟩ = 1`. -/
theorem inner_ket1_ket1 : inner ℂ ket1 ket1 = (1 : ℂ) := by
  unfold ket1
  exact inner_ket 1 1

/-- `|+⟩` -/
noncomputable def ketplus : State 1 :=
  (1 / √2 : ℂ) • ket0 + (1 / √2 : ℂ) • ket1

/-- `|-⟩` -/
noncomputable def ketminus : State 1 :=
  (1 / √2 : ℂ) • ket0 - (1 / √2 : ℂ) • ket1

end StateVector
