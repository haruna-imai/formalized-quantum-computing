/-
Copyright (c) 2026 Haruna Imai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruna Imai
-/

import FormalizedQuantumComputing.StateVector.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Basic properties of state vectors

This file proves basic properties of state vectors and includes calculations involving
Bell states.
-/

namespace StateVector

open Kronecker
open scoped Matrix

/- Applying the outer product `|ψ⟩⟨φ|` to a state `v` yields
the scalar multiple `⟨φ, v⟩ • ψ`. --/
theorem Matrix.outer_apply {n : ℕ} (ψ φ v : State n) :
  applyMatrix (outer ψ φ) v = (inner ℂ φ v) • ψ := by
    unfold outer applyMatrix
    ext i
    simp
    rw [PiLp.inner_apply]
    simp
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring

/- star (outer ψ φ) = outer φ ψ --/
theorem star_outer (ψ φ : State n) :
  star (outer ψ φ) = outer φ ψ := by
    unfold outer
    ext i j
    rw [Matrix.star_apply (fun i j ↦ ψ.ofLp i * (starRingEnd ((fun x ↦ ℂ) j)) (φ.ofLp j)) i j]
    rw [star_mul]
    simp

/- Applying the outer product `|ψ_1⟩⟨ψ_2|` to a outer product `|φ_1⟩⟨φ_2|` yields
the scalar multiple `⟨ψ_2, φ_1⟩ • |ψ_1⟩⟨φ_2|`. --/
theorem outer_mul_outer (ψ_1 ψ_2 φ_1 φ_2 : State n) :
    (outer ψ_1 ψ_2) * (outer φ_1 φ_2) =
      (inner ℂ ψ_2 φ_1) • (outer ψ_1 φ_2) := by
  unfold outer
  ext i j
  rw [PiLp.inner_apply]
  simp
  change
    (∑ k,
      (ψ_1.ofLp i * (starRingEnd ℂ) (ψ_2.ofLp k)) *
      (φ_1.ofLp k * (starRingEnd ℂ) (φ_2.ofLp j))) =
    (∑ k,
      φ_1.ofLp k * (starRingEnd ℂ) (ψ_2.ofLp k)) *
      (ψ_1.ofLp i * (starRingEnd ℂ) (φ_2.ofLp j))

  calc
    (∑ k,
      (ψ_1.ofLp i * (starRingEnd ℂ) (ψ_2.ofLp k)) *
      (φ_1.ofLp k * (starRingEnd ℂ) (φ_2.ofLp j)))
        =
      ∑ k,
        (φ_1.ofLp k * (starRingEnd ℂ) (ψ_2.ofLp k)) *
        (ψ_1.ofLp i * (starRingEnd ℂ) (φ_2.ofLp j)) := by
          apply Fintype.sum_congr
          intro k
          ring

    _ =
      (∑ k,
        φ_1.ofLp k * (starRingEnd ℂ) (ψ_2.ofLp k)) *
      (ψ_1.ofLp i * (starRingEnd ℂ) (φ_2.ofLp j)) := by
        exact
          (Finset.sum_mul
            Finset.univ
            (fun k =>
              φ_1.ofLp k * (starRingEnd ℂ) (ψ_2.ofLp k))
            (ψ_1.ofLp i * (starRingEnd ℂ) (φ_2.ofLp j))).symm



/- (Fin (m + n) → Fin 2) ≃ (Fin m → Fin 2) × (Fin n → Fin 2) --/
def basisIndexEquivProd (m n : ℕ) :
  (Fin (m + n) → Fin 2) ≃ (Fin m → Fin 2) × (Fin n → Fin 2) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl _)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) (Fin 2))

variable (n : ℕ)

/- inner product of tensor product --/
theorem inner_tensor {m : ℕ}
    (ψ₁ φ₁ : State m) (ψ₂ φ₂ : State n) :
    inner ℂ (tensor ψ₁ ψ₂) (tensor φ₁ φ₂) =
      inner ℂ ψ₁ φ₁ * inner ℂ ψ₂ φ₂ := by
  unfold tensor
  rw [PiLp.inner_apply]
  simp

  rw [Fintype.sum_equiv
    (basisIndexEquivProd m n)
    (fun x =>
      (φ₁.ofLp (fun i => x (Fin.castAdd n i)) *
        φ₂.ofLp (fun j => x (Fin.natAdd m j))) *
      ((starRingEnd ℂ) (ψ₁.ofLp (fun i => x (Fin.castAdd n i))) *
        (starRingEnd ℂ) (ψ₂.ofLp (fun j => x (Fin.natAdd m j)))))
    (fun y =>
      (φ₁.ofLp y.1 * φ₂.ofLp y.2) *
      ((starRingEnd ℂ) (ψ₁.ofLp y.1) *
        (starRingEnd ℂ) (ψ₂.ofLp y.2)))
    (by
      intro x
      rfl)]

  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro x
  apply Fintype.sum_congr
  intro y
  ring

/-- The amplitude of `|a⟩ ⊗ |b⟩` is `1` at the
basis state `(a, b)` and `0` elsewhere. -/
theorem tensor_ket_apply (a b : Fin 2) (x : Fin 2 → Fin 2) :
    (tensor (ket a) (ket b)).ofLp x =
      if x 0 = a ∧ x 1 = b then 1 else 0 := by
  by_cases ha : x 0 = a <;> by_cases hb : x 1 = b <;>
    simp [tensor, ket, ha, hb]

/-- Every element of `Fin 2` is either `0` or `1`. -/
lemma fin_two_eq_zero_or_one (x : Fin 2) :
    x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- Two functions from `Fin 2` are equal if and only if they agree at `0` and `1`. -/
lemma fin_two_fun_eq_iff (i j : Fin (1 + 1) → Fin 2) :
    i = j ↔ i 0 = j 0 ∧ i 1 = j 1 := by
  constructor
  · intro h
    subst j
    simp
  · rintro ⟨h0, h1⟩
    funext x
    fin_cases x
    · simpa using h0
    · simpa using h1

/- |00⟩⟨00| + |01⟩⟨01| + |10⟩⟨10| + |11⟩⟨11| = 1 --/
theorem computationalBasis_two_qubit_outerproduct_sum :
    outer (tensor ket0 ket0) (tensor ket0 ket0) +
    outer (tensor ket0 ket1) (tensor ket0 ket1) +
    outer (tensor ket1 ket0) (tensor ket1 ket0) +
    outer (tensor ket1 ket1) (tensor ket1 ket1) = 1 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.one_apply, outer, ket0, ket1,
    tensor_ket_apply, fin_two_fun_eq_iff]
  rcases fin_two_eq_zero_or_one (i 0) with hi0 | hi0 <;>
  rcases fin_two_eq_zero_or_one (i 1) with hi1 | hi1 <;>
  rcases fin_two_eq_zero_or_one (j 0) with hj0 | hj0 <;>
  rcases fin_two_eq_zero_or_one (j 1) with hj1 | hj1 <;>
  simp [hi0, hi1, hj0, hj1]

-- 以降はGate/Basic.leanに置くこと
/-
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
-/

end StateVector
