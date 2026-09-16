import Mathlib
import Proof.Defs
import Proof.Exp
import Proof.Arith

/-!
# The coefficient identity

If `|A| = |B| = n` and the power sums `S_i(A) = S_i(B)` agree for `1 ≤ i < j`, then for every
`m` the coefficients of `x^i`, `i < j`, of `esym A m` and `esym B m` agree, and
`j! · (coeff_j (esym A m) - coeff_j (esym B m)) = acoef n j m · (S_j(A) - S_j(B))`.
Proof: strong induction on `m` through Newton's identity (`Exp.newton`), expanding the
coefficient of a product with `PowerSeries.coeff_mul` over `antidiagonal`, and using
`Arith.acoef_recursion`.
-/

open Finset PowerSeries

namespace Erdos494

/-- Newton's identity for `esym A m`, read off in the coefficient of `x ^ k`. -/
private theorem coeff_newton (A : Finset ℂ) (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    (m : ℂ) * PowerSeries.coeff k (esym A m) =
      ∑ i ∈ Finset.Icc 1 m, (-1 : ℂ) ^ (i - 1) *
        ∑ p ∈ antidiagonal k,
          PowerSeries.coeff p.1 (esym A (m - i)) * PowerSeries.coeff p.2 (pw A i) := by
  rw [← coeff_C_mul, map_natCast, newton A m hm, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← coeff_mul, ← coeff_C_mul, map_pow, map_neg, map_one]

/-- If the power sums of `A` and `B` agree below `j`, so do the low coefficients of `pw`. -/
private theorem coeff_pw_eq {A B : Finset ℂ} (hcard : A.card = B.card) {j : ℕ}
    (hS : ∀ i, 1 ≤ i → i < j → psum A i = psum B i) (i v : ℕ) (hv : v < j) :
    PowerSeries.coeff v (pw A i) = PowerSeries.coeff v (pw B i) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv0
  · rw [coeff_zero_pw, coeff_zero_pw, hcard]
  · have hA := coeff_pw A i v
    have hB := coeff_pw B i v
    rw [hS v hv0 hv] at hA
    exact mul_left_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero v)) (hA.trans hB.symm)

/-- Newton's identity in the coefficient of `x ^ k`, for the difference of `A` and `B`. -/
private theorem coeff_newton_sub (A B : Finset ℂ) (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (c : ℂ)
    (g : ℕ → ℂ) (hg : ∀ i ∈ Finset.Icc 1 m, c *
      ((∑ p ∈ antidiagonal k, PowerSeries.coeff p.1 (esym A (m - i)) *
          PowerSeries.coeff p.2 (pw A i)) -
        ∑ p ∈ antidiagonal k, PowerSeries.coeff p.1 (esym B (m - i)) *
          PowerSeries.coeff p.2 (pw B i)) = g i) :
    (m : ℂ) * (c * (PowerSeries.coeff k (esym A m) - PowerSeries.coeff k (esym B m))) =
      ∑ i ∈ Finset.Icc 1 m, (-1 : ℂ) ^ (i - 1) * g i := by
  have hexp : (m : ℂ) * (c * (PowerSeries.coeff k (esym A m) - PowerSeries.coeff k (esym B m))) =
      c * ((m : ℂ) * PowerSeries.coeff k (esym A m) -
        (m : ℂ) * PowerSeries.coeff k (esym B m)) := by
    ring
  rw [hexp, coeff_newton A m hm k, coeff_newton B m hm k, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← hg i hi]
  ring

/-- If `|A| = |B|` and the power sums of `A` and `B` agree below `j`, then the coefficients of
`x ^ i`, `i < j`, of `esym A m` and `esym B m` agree, and
`j! * (coeff_j (esym A m) - coeff_j (esym B m)) = acoef |A| j m * (S_j A - S_j B)`. -/
theorem coeff_diff (A B : Finset ℂ) (hcard : A.card = B.card) (j : ℕ) (hj : 1 ≤ j)
    (hS : ∀ i, 1 ≤ i → i < j → psum A i = psum B i) (m : ℕ) :
    (∀ i, i < j → PowerSeries.coeff i (esym A m) = PowerSeries.coeff i (esym B m)) ∧
      (j.factorial : ℂ) * (PowerSeries.coeff j (esym A m) - PowerSeries.coeff j (esym B m)) =
        (acoef A.card j m : ℂ) * (psum A j - psum B j) := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨fun i _ => by rw [esym_zero, esym_zero], ?_⟩
      rw [esym_zero, esym_zero, show acoef A.card j 0 = 0 by simp [acoef]]
      simp
    · have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hlt : ∀ i ∈ Finset.Icc 1 m, m - i < m := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        omega
      have hfirst : ∀ k, k < j →
          PowerSeries.coeff k (esym A m) = PowerSeries.coeff k (esym B m) := by
        intro k hk
        have hg : ∀ i ∈ Finset.Icc 1 m, (1 : ℂ) *
            ((∑ p ∈ antidiagonal k, PowerSeries.coeff p.1 (esym A (m - i)) *
                PowerSeries.coeff p.2 (pw A i)) -
              ∑ p ∈ antidiagonal k, PowerSeries.coeff p.1 (esym B (m - i)) *
                PowerSeries.coeff p.2 (pw B i)) = 0 := by
          intro i hi
          rw [one_mul]
          refine sub_eq_zero_of_eq (Finset.sum_congr rfl fun p hp => ?_)
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
          rw [(IH (m - i) (hlt i hi)).1 p.1 (by omega), coeff_pw_eq hcard hS i p.2 (by omega)]
        have h := coeff_newton_sub A B m hm k 1 (fun _ => 0) hg
        simp only [one_mul, mul_zero, Finset.sum_const_zero] at h
        exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hm0)
      refine ⟨hfirst, ?_⟩
      have key : ∀ i ∈ Finset.Icc 1 m, (j.factorial : ℂ) *
          ((∑ p ∈ antidiagonal j, PowerSeries.coeff p.1 (esym A (m - i)) *
              PowerSeries.coeff p.2 (pw A i)) -
            ∑ p ∈ antidiagonal j, PowerSeries.coeff p.1 (esym B (m - i)) *
              PowerSeries.coeff p.2 (pw B i)) =
          ((A.card.choose (m - i) : ℂ) * (i : ℂ) ^ j +
            (A.card : ℂ) * (acoef A.card j (m - i) : ℂ)) * (psum A j - psum B j) := by
        intro i hi
        have hne : ((0 : ℕ), j) ≠ (j, (0 : ℕ)) := by
          intro h
          rw [Prod.mk.injEq] at h
          omega
        have hsub : ({((0 : ℕ), j), (j, (0 : ℕ))} : Finset (ℕ × ℕ)) ⊆
            antidiagonal j := by
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> simp
        have hzero : ∀ p ∈ antidiagonal j,
            p ∉ ({((0 : ℕ), j), (j, (0 : ℕ))} : Finset (ℕ × ℕ)) →
            PowerSeries.coeff p.1 (esym A (m - i)) * PowerSeries.coeff p.2 (pw A i) -
              PowerSeries.coeff p.1 (esym B (m - i)) * PowerSeries.coeff p.2 (pw B i) = 0 := by
          rintro ⟨u, v⟩ hp hnp
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
          dsimp only at hp ⊢
          have hu : u ≠ 0 := by
            rintro rfl
            refine hnp ?_
            simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, true_and]
            omega
          have hv : v ≠ 0 := by
            rintro rfl
            refine hnp ?_
            simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true]
            omega
          rw [(IH (m - i) (hlt i hi)).1 u (by omega), coeff_pw_eq hcard hS i v (by omega),
            sub_self]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_subset hsub hzero, Finset.sum_pair hne]
        dsimp only
        have hpA := coeff_pw A i j
        have hpB := coeff_pw B i j
        have hIH := (IH (m - i) (hlt i hi)).2
        rw [coeff_zero_pw, coeff_zero_pw, coeff_zero_esym, coeff_zero_esym, ← hcard]
        linear_combination (A.card.choose (m - i) : ℂ) * hpA -
          (A.card.choose (m - i) : ℂ) * hpB + (A.card : ℂ) * hIH
      have hrec : (m : ℂ) * (acoef A.card j m : ℂ) =
          ∑ i ∈ Finset.Icc 1 m, (-1 : ℂ) ^ (i - 1) *
            ((A.card.choose (m - i) : ℂ) * (i : ℂ) ^ j +
              (A.card : ℂ) * (acoef A.card j (m - i) : ℂ)) := by
        have h := congrArg (fun z : ℤ => (z : ℂ)) (acoef_recursion A.card j m hj)
        push_cast at h
        exact h
      have hfin := coeff_newton_sub A B m hm j (j.factorial : ℂ)
        (fun i => ((A.card.choose (m - i) : ℂ) * (i : ℂ) ^ j +
          (A.card : ℂ) * (acoef A.card j (m - i) : ℂ)) * (psum A j - psum B j)) key
      have hR : (m : ℂ) * ((acoef A.card j m : ℂ) * (psum A j - psum B j)) =
          ∑ i ∈ Finset.Icc 1 m, (-1 : ℂ) ^ (i - 1) *
            (((A.card.choose (m - i) : ℂ) * (i : ℂ) ^ j +
              (A.card : ℂ) * (acoef A.card j (m - i) : ℂ)) * (psum A j - psum B j)) := by
        rw [← mul_assoc, hrec, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      exact mul_left_cancel₀ hm0 (hfin.trans hR.symm)

end Erdos494
