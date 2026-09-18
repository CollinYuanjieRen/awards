import Mathlib

/-!
# Algebraic objects for exterior power sums

The Luo--Yang--Zhu proof repeatedly uses the same finite power sums and the
polynomial `F(t) = product_j (1 - z_j t)`.  This module fixes those objects and
their elementary evaluation/degree facts independently of the analytic
estimates.
-/

open Finset Polynomial

namespace Erdos973

/-- The `k`-th power sum of a finite complex family. -/
def powerSum {n : ℕ} (z : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ j, z j ^ k

/-- `F_z(t) = product_j (1 - z_j t)` as a complex polynomial. -/
noncomputable def rootProduct {n : ℕ} (z : Fin n → ℂ) : ℂ[X] :=
  ∏ j, (1 - C (z j) * X)

@[simp] theorem eval_rootProduct {n : ℕ} (z : Fin n → ℂ) (t : ℂ) :
    (rootProduct z).eval t = ∏ j, (1 - z j * t) := by
  rw [rootProduct, eval_prod]
  simp

theorem degree_rootProduct_le {n : ℕ} (z : Fin n → ℂ) :
    (rootProduct z).degree ≤ n := by
  rw [rootProduct]
  calc
    (∏ j, (1 - C (z j) * X)).degree
        ≤ ∑ j : Fin n, (1 - C (z j) * X : ℂ[X]).degree :=
      degree_prod_le _ _
    _ ≤ ∑ _j : Fin n, (1 : WithBot ℕ) := by
      gcongr with j
      have hCX : (C (z j) * X : ℂ[X]).degree ≤ 1 := by
        calc
          (C (z j) * X : ℂ[X]).degree
              ≤ (C (z j) : ℂ[X]).degree + (X : ℂ[X]).degree := degree_mul_le _ _
          _ ≤ 0 + 1 := add_le_add degree_C_le (by simp)
          _ = 1 := by simp
      calc
        (1 - C (z j) * X : ℂ[X]).degree
            ≤ max (1 : ℂ[X]).degree (C (z j) * X).degree := degree_sub_le _ _
        _ ≤ 1 := max_le (by simp) hCX
    _ = n := by simp

theorem coeff_rootProduct_eq_zero_of_lt {n m : ℕ} (z : Fin n → ℂ)
    (h : n < m) : (rootProduct z).coeff m = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  apply lt_of_le_of_lt (natDegree_le_iff_degree_le.2 ?_) h
  exact degree_rootProduct_le z

end Erdos973
