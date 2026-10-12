import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup


/-
# テンソル積を考える
-/

abbrev State (n : ℕ) :=
  EuclideanSpace ℂ (Fin n → Fin 2)

variable {m : ℕ}
variable {n : ℕ}
variable (ψ_1 : State m)
variable (ψ_2 : State n)
variable (i : Fin m → Fin 2)
variable (j : Fin n → Fin 2)

-- 振幅を取り出す
#check ψ_1.ofLp i
example : ℂ := ψ_1.ofLp i

-- テンソル積の行
-- ψ₁ ⊗ ψ₂ において、i と j を結合した計算基底に対応する振幅
example : ℂ := ψ_1.ofLp i * ψ_2.ofLp j

-- 参考 ket i を作るとき
/-- The computational basis state `|i⟩`. -/
def ket (i : Fin 2) : State 1 :=
  WithLp.toLp 2 (fun x =>
    if x 0 = i then 1 else 0)

-- sorryの部分を埋めれば良い
-- x : Fin (m + n) → Fin 2 に注意
-- def tensor : State (m + n) :=
  -- WithLp.toLp 2 (fun x => sorry)

-- ここで、Fin.castAddで前半の添字を取る
variable (x : Fin (m + n) → Fin 2)
example : Fin m → Fin 2 :=
  fun k => x (Fin.castAdd n k)

-- これより、前半の振幅をとるには
example : ℂ := ψ_1.ofLp (fun k => x (Fin.castAdd n k))

-- 同じく、後半の振幅を取るには
example : ℂ := ψ_2.ofLp (fun k => x (Fin.natAdd m k))

-- よって
def tensor (ψ_1 : State m) (ψ_2 : State n) : State (m + n) :=
  WithLp.toLp 2 (fun x =>
    ψ_1.ofLp (fun i : Fin m => x (Fin.castAdd n i)) *
    ψ_2.ofLp (fun j : Fin n => x (Fin.natAdd m j)))

-- 具体例
example : (State 2) := tensor (ket 0) (ket 1)

example :
    tensor (ket 0) (ket 1) =
      WithLp.toLp 2 (fun x =>
        if x 0 = 0 ∧ x 1 = 1 then 1 else 0) := by
  unfold tensor ket
  ext x
  simp
  by_cases h0 : x 0 = 0 <;>
  by_cases h1 : x 1 = 1 <;>
  simp [h0, h1]

/-
# 外積を考える
-/

/-
以下のようなouterを定義したい
outer :
  State n → State n →
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ
-/

open scoped ComplexConjugate
variable (z : ℂ)
#check conj z

-- 最終的な形
def outer (ψ φ : State n) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun i j =>
    ψ.ofLp i * conj (φ.ofLp j)

-- 具体例
#check outer (ket 0) (ket 1)

example :
    outer (ket 0) (ket 1)
      (fun _ : Fin 1 => 0)
      (fun _ : Fin 1 => 1) = 1 := by
  unfold outer ket
  simp

/-
# 外積による行列とベクトルの積
-/
open scoped Matrix

def Matrix.applyToState {n : ℕ}
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (ψ : State n) : State n :=
  WithLp.toLp 2 (A *ᵥ ψ.ofLp)

theorem outer_apply (ψ φ v : State n) :
  Matrix.applyToState (outer ψ φ) v = (inner ℂ φ v) • ψ := by
    unfold outer Matrix.applyToState
    ext i
    simp
    rw [PiLp.inner_apply]
    simp
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring

#check Finset.sum_mul
#check Finset.mul_sum

abbrev QuantumGate (n : ℕ) := Matrix.unitaryGroup (Fin n → Fin 2) ℂ

def Gate.apply
    (U : QuantumGate n) (ψ : State n) : State n :=
  Matrix.applyToState U ψ
