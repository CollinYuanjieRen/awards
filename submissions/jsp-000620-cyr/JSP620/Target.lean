import JSP620.Construction

/-!
# Erdős Problem 754 (JSP-000620): the two-sided answer `f(n) = n/2 + O(1)`

`Erdos754.f n` is the largest `k` such that some `n`-point set in `ℝ⁴` has, at every
point, at least `k` other points at one distance chosen for that point.

* Lower bounds (this development, following Avis–Erdős–Pach 1988): `⌊n/2⌋ ≤ f n` for every
  `n`, and `n/2 + 2 ≤ f n` whenever `8 ∣ n`.
* Upper bound (existing formalization `Erdos754.erdos_754` of Swanepoel's theorem, by
  Codex / GPT-5.6 Sol in plby/lean-proofs): `f n ≤ n/2 + 202`.

Together: `f n = n/2 + O(1)`, which is the answer to the catalog question.
-/

open Erdos754

namespace Erdos754Lower

/-- The two-sided resolution of Erdős Problem 754: the lower bounds of Avis, Erdős and
Pach and the upper bound `f n ≤ n/2 + O(1)`. -/
theorem erdos_754_two_sided :
    (∀ n : ℕ, n / 2 ≤ f n) ∧
    (∀ n : ℕ, n ≠ 0 → 8 ∣ n → n / 2 + 2 ≤ f n) ∧
    (∃ C : ℝ, ∀ n : ℕ, (f n : ℝ) ≤ (n : ℝ) / 2 + C) :=
  ⟨half_le_f, half_add_two_le_f_of_eight_dvd, erdos_754⟩

/-- `f n` differs from `n / 2` by a bounded amount. -/
theorem abs_f_sub_half_le : ∃ C : ℝ, ∀ n : ℕ, |(f n : ℝ) - (n : ℝ) / 2| ≤ C := by
  obtain ⟨C, hC⟩ := erdos_754
  refine ⟨max C 1, fun n => ?_⟩
  rw [abs_le]
  constructor
  · have h1 : ((n / 2 : ℕ) : ℝ) ≤ f n := by exact_mod_cast half_le_f n
    have hn : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod n 2).symm
    have hm : ((n % 2 : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt n two_pos)
    have h3 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
    linarith
  · have := hC n
    have h3 : C ≤ max C 1 := le_max_left _ _
    linarith

/-- The catalog answer in asymptotic notation: `f n = n / 2 + O(1)`. -/
theorem f_sub_half_isBigO :
    (fun n : ℕ => (f n : ℝ) - (n : ℝ) / 2) =O[Filter.atTop] (fun _ : ℕ => (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := abs_f_sub_half_le
  refine Asymptotics.IsBigO.of_bound C (Filter.Eventually.of_forall fun n => ?_)
  simpa [Real.norm_eq_abs] using hC n

end Erdos754Lower
