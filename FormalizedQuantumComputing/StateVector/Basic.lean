/-
Copyright (c) 2026 Haruna Imai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruna Imai
-/

import FormalizedQuantumComputing.StateVector.Defs

/-!
# Basic properties of state vectors

This file proves orthonormality of computational basis states, properties of tensor
products, matrix application and outer products, and completeness of computational bases.
-/

namespace StateVector

open Kronecker
open scoped Matrix

/-! ## Computational basis states -/

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

/-! ## Tensor products -/

/-- The tensor product is additive in its first argument.

`tensor (ψ₁ + ψ₂) φ = tensor ψ₁ φ + tensor ψ₂ φ` -/
theorem tensor_add_left {m n : ℕ}
    (ψ₁ ψ₂ : State m) (φ : State n) :
    tensor (ψ₁ + ψ₂) φ =
      tensor ψ₁ φ + tensor ψ₂ φ := by
  apply WithLp.ofLp_injective
  funext x
  simp [tensor, add_mul]

/-- The tensor product is additive in its second argument.

`tensor ψ (φ₁ + φ₂) = tensor ψ φ₁ + tensor ψ φ₂` -/
theorem tensor_add_right {m n : ℕ}
    (ψ : State m) (φ₁ φ₂ : State n) :
    tensor ψ (φ₁ + φ₂) =
      tensor ψ φ₁ + tensor ψ φ₂ := by
  apply WithLp.ofLp_injective
  funext x
  simp [tensor, mul_add]

/-- The tensor product is compatible with scalar multiplication
in its first argument.

`tensor (c • ψ) φ = c • tensor ψ φ` -/
theorem tensor_smul_left {m n : ℕ}
    (c : ℂ) (ψ : State m) (φ : State n) :
    tensor (c • ψ) φ = c • tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext x
  simp [tensor, smul_eq_mul, mul_assoc]

/-- The tensor product is compatible with scalar multiplication
in its second argument.

`tensor ψ (c • φ) = c • tensor ψ φ` -/
theorem tensor_smul_right {m n : ℕ}
    (c : ℂ) (ψ : State m) (φ : State n) :
    tensor ψ (c • φ) = c • tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext x
  simp [tensor, smul_eq_mul, ← mul_assoc, mul_comm]

/-- (Fin (m + n) → Fin 2) ≃ (Fin m → Fin 2) × (Fin n → Fin 2) -/
def basisIndexEquivProd (m n : ℕ) :
  (Fin (m + n) → Fin 2) ≃ (Fin m → Fin 2) × (Fin n → Fin 2) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl _)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) (Fin 2))

/-- inner product of tensor product -/
theorem inner_tensor {m n : ℕ}
    (ψ₁ φ₁ : State m) (ψ₂ φ₂ : State n) :
    inner ℂ (tensor ψ₁ ψ₂) (tensor φ₁ φ₂) =
      inner ℂ ψ₁ φ₁ * inner ℂ ψ₂ φ₂ := by
  unfold tensor
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, map_mul]
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
  simp only [RCLike.inner_apply]
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

/-! ## Matrix application -/

/-- Applying a sum of matrices to a state vector gives
 the sum of their applications.

`applyMatrix (A + B) v = applyMatrix A v + applyMatrix B v`
-/
theorem applyMatrix_add {n : ℕ}
    (A B : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (v : State n) :
    applyMatrix (A + B) v =
      applyMatrix A v + applyMatrix B v := by
  simp only [applyMatrix, Matrix.add_mulVec, WithLp.toLp_add]

/-- Applying a difference of matrices to a state vector gives
 the difference of their applications.

`applyMatrix (A - B) v = applyMatrix A v - applyMatrix B v`
-/
theorem applyMatrix_sub {n : ℕ}
    (A B : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (v : State n) :
    applyMatrix (A - B) v =
      applyMatrix A v - applyMatrix B v := by
  simp only [applyMatrix, Matrix.sub_mulVec, WithLp.toLp_sub]

/-- Applying a scalar multiple of a matrix to a state vector gives
the scalar multiple of its application.

`applyMatrix (c • A) v = c • applyMatrix A v`
-/
theorem applyMatrix_smul {n : ℕ}
    (c : ℂ)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (v : State n) :
    applyMatrix (c • A) v =
      c • applyMatrix A v := by
  simp only [applyMatrix, Matrix.smul_mulVec, WithLp.toLp_smul]

/-- Matrix application is additive in the state vector.

`applyMatrix A (v + w) = applyMatrix A v + applyMatrix A w` -/
theorem applyMatrix_add_state {n : ℕ}
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (v w : State n) :
    applyMatrix A (v + w) =
      applyMatrix A v + applyMatrix A w := by
  simp only [applyMatrix, WithLp.ofLp_add,
    Matrix.mulVec_add, WithLp.toLp_add]

/-- Applying a matrix to a scalar multiple of a state vector
equals the scalar multiple of the matrix application.

`applyMatrix A (c • v) = c • applyMatrix A v` -/
theorem applyMatrix_smul_state {n : ℕ}
    (c : ℂ)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (v : State n) :
    applyMatrix A (c • v) =
      c • applyMatrix A v := by
  simp only [applyMatrix, WithLp.ofLp_smul,
    Matrix.mulVec_smul, WithLp.toLp_smul]

/-! ## Outer products -/

/-- Applying the outer product `|ψ⟩⟨φ|` to a state `v` yields
the scalar multiple `⟨φ, v⟩ • ψ`. -/
theorem Matrix.outer_apply {n : ℕ} (ψ φ v : State n) :
  applyMatrix (outer ψ φ) v = (inner ℂ φ v) • ψ := by
    unfold outer applyMatrix
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- star (outer ψ φ) = outer φ ψ -/
theorem star_outer (ψ φ : State n) :
  star (outer ψ φ) = outer φ ψ := by
    unfold outer
    ext i j
    rw [Matrix.star_apply (fun i j ↦ ψ.ofLp i * (starRingEnd ((fun x ↦ ℂ) j)) (φ.ofLp j)) i j]
    rw [star_mul]
    simp

/-- Applying the outer product `|ψ_1⟩⟨ψ_2|` to a outer product `|φ_1⟩⟨φ_2|` yields
the scalar multiple `⟨ψ_2, φ_1⟩ • |ψ_1⟩⟨φ_2|`. -/
theorem outer_mul_outer (ψ_1 ψ_2 φ_1 φ_2 : State n) :
    (outer ψ_1 ψ_2) * (outer φ_1 φ_2) =
      (inner ℂ ψ_2 φ_1) • (outer ψ_1 φ_2) := by
  unfold outer
  ext i j
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
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

/-! ## Completeness of computational bases -/

/-- Every element of `Fin 2` is either `0` or `1`. -/
lemma fin_two_eq_zero_or_one (x : Fin 2) :
    x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

lemma fin_one_fun_eq_iff (i j : Fin 1 → Fin 2) :
    i = j ↔ i 0 = j 0 := by
  constructor
  · intro h
    rw [h]
  · intro h
    funext k
    have hk : k = 0 := Subsingleton.elim k 0
    subst k
    exact h

/-- |0⟩⟨0| + |1⟩⟨1| = 1 -/
theorem computationalBasis_one_qubit_outerproduct_sum :
    outer ket0 ket0 + outer ket1 ket1  = 1 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.one_apply, outer, ket0, ket1, fin_one_fun_eq_iff]
  rcases fin_two_eq_zero_or_one (i 0) with hi0 | hi0 <;>
  rcases fin_two_eq_zero_or_one (j 0) with hj0 | hj0 <;>
  simp [ket, hi0, hj0]

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

/-- |00⟩⟨00| + |01⟩⟨01| + |10⟩⟨10| + |11⟩⟨11| = 1 -/
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

end StateVector
