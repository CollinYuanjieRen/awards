import Mathlib

/-!
# JSP-000751 / Erdős #903 — the abstract positive-definite / rank lemma

This file is purely linear algebra over `ℝ`, independent of the combinatorics.

The point is the last theorem, `card_le_rank_add_one`: if `β i > 0` for every `i` and `α ≥ 0`,
then for every `c` the matrix `diagonal β - c • J + α • a aᵀ` (with `J` the all-ones matrix) has
rank at least `card n - 1`.  Indeed `X := diagonal β + α • a aᵀ` is positive definite, hence
invertible, hence of full rank; and `X = (X - c • J) + c • J` with `rank (c • J) ≤ 1`, so
subadditivity of the rank gives `card n = rank X ≤ rank (X - c • J) + 1`.
-/

open Matrix

namespace Erdos903

variable {n : Type*}

/-- `vecMulVec a a` is positive semidefinite over `ℝ`. -/
theorem posSemidef_vecMulVec_self [Fintype n] (a : n → ℝ) :
    (Matrix.vecMulVec a a).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star a
  simpa using h

/-- `diag β + α a aᵀ` is positive definite when all `β i > 0` and `α ≥ 0`. -/
theorem posDef_diagonal_add_vecMulVec [Fintype n] [DecidableEq n] (β : n → ℝ)
    (hβ : ∀ i, 0 < β i) (α : ℝ) (hα : 0 ≤ α) (a : n → ℝ) :
    (Matrix.diagonal β + α • Matrix.vecMulVec a a).PosDef :=
  (Matrix.posDef_diagonal_iff.mpr hβ).add_posSemidef ((posSemidef_vecMulVec_self a).smul hα)

/-- Its rank is full. -/
theorem rank_diagonal_add_vecMulVec [Fintype n] [DecidableEq n] (β : n → ℝ)
    (hβ : ∀ i, 0 < β i) (α : ℝ) (hα : 0 ≤ α) (a : n → ℝ) :
    (Matrix.diagonal β + α • Matrix.vecMulVec a a).rank = Fintype.card n :=
  Matrix.rank_of_isUnit _ (posDef_diagonal_add_vecMulVec β hβ α hα a).isUnit

/-- Rank is subadditive. -/
theorem rank_add_le' [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rw [Matrix.mulVecLin_add]
    exact LinearMap.range_add_le _ _
  calc (A + B).rank
      ≤ Module.finrank ℝ
          (LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule ℝ (n → ℝ)) :=
        Submodule.finrank_mono hle
    _ ≤ A.rank + B.rank := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- The constant matrix is a rank-one outer product. -/
theorem const_eq_vecMulVec (c : ℝ) :
    (Matrix.of fun (_ _ : n) => c) = Matrix.vecMulVec (fun _ => c) (fun _ => (1 : ℝ)) := by
  ext i j
  simp [Matrix.vecMulVec_apply]

/-- The all-ones matrix (scaled) has rank ≤ 1. -/
theorem rank_const_le_one [Fintype n] [DecidableEq n] (c : ℝ) :
    (Matrix.of fun (_ _ : n) => c).rank ≤ 1 := by
  rw [const_eq_vecMulVec]
  exact Matrix.rank_vecMulVec_le _ _

/-- A scalar multiple of the all-ones matrix is the constant matrix. -/
theorem smul_ones_eq_const (c : ℝ) :
    c • (Matrix.of fun (_ _ : n) => (1 : ℝ)) = Matrix.of fun (_ _ : n) => c := by
  ext i j
  simp

/-- Main abstract lemma: subtracting a multiple of the all-ones matrix from a positive definite
`diag β + α a aᵀ` leaves rank at least `card n − 1`. -/
theorem card_le_rank_add_one [Fintype n] [DecidableEq n] (β : n → ℝ) (hβ : ∀ i, 0 < β i)
    (α : ℝ) (hα : 0 ≤ α) (a : n → ℝ) (c : ℝ) :
    Fintype.card n ≤
      (Matrix.diagonal β - c • Matrix.of (fun (_ _ : n) => (1 : ℝ))
        + α • Matrix.vecMulVec a a).rank + 1 := by
  set Y : Matrix n n ℝ :=
    Matrix.diagonal β - c • Matrix.of (fun (_ _ : n) => (1 : ℝ))
      + α • Matrix.vecMulVec a a with hY
  have hsplit : Matrix.diagonal β + α • Matrix.vecMulVec a a
      = Y + c • Matrix.of (fun (_ _ : n) => (1 : ℝ)) := by
    rw [hY]; abel
  calc Fintype.card n = (Matrix.diagonal β + α • Matrix.vecMulVec a a).rank :=
        (rank_diagonal_add_vecMulVec β hβ α hα a).symm
    _ = (Y + c • Matrix.of (fun (_ _ : n) => (1 : ℝ))).rank := by rw [hsplit]
    _ ≤ Y.rank + (c • Matrix.of (fun (_ _ : n) => (1 : ℝ))).rank := rank_add_le' _ _
    _ ≤ Y.rank + 1 := by
        refine Nat.add_le_add_left ?_ _
        rw [smul_ones_eq_const]
        exact rank_const_le_one c

end Erdos903
