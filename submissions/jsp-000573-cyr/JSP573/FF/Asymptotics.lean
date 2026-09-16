import Mathlib

/-!
# Elementary binomial and growth estimates for the Frankl–Füredi endgame

Leaves used in the final comparison "exponential beats polynomial" of the proof of Theorem 1.3:

* `centralBinom_min_le_choose`: `C(N, k) ≥ C(2j, j)` with `j = min k (N - k)` (repeated Pascal:
  `C(N, k) ≥ C(N - 1, k - 1)` and `C(M, j)` is monotone in `M`);
* `four_pow_le_choose_mul`: `4 ^ j ≤ (2j + 1) · C(2j, j)` (Mathlib's central binomial bound);
* `sum_choose_Ioo_le`: `∑_{t < i < q} C(n, i) ≤ q · n ^ q` for `1 ≤ n`;
* `eventually_mul_pow_lt_two_pow`: for fixed `c, e`, `c · n ^ e < 2 ^ n` for all large `n`.
-/

open Finset

namespace FranklFuredi

/-- Repeated Pascal: `C(N, k) ≥ C(2j, j)` where `j = min k (N - k)`. -/
theorem centralBinom_min_le_choose (N k : ℕ) (hk : k ≤ N) :
    (2 * min k (N - k)).choose (min k (N - k)) ≤ N.choose k := by
  rcases le_total k (N - k) with h | h
  · rw [min_eq_left h]
    exact Nat.choose_le_choose k (by omega)
  · rw [min_eq_right h]
    calc (2 * (N - k)).choose (N - k) ≤ N.choose (N - k) := Nat.choose_le_choose _ (by omega)
      _ = N.choose k := Nat.choose_symm hk

/-- `4 ^ j ≤ (2j + 1) · C(2j, j)`. -/
theorem four_pow_le_choose_mul (j : ℕ) : 4 ^ j ≤ (2 * j + 1) * (2 * j).choose j :=
  Nat.four_pow_le_two_mul_add_one_mul_central_binom j

/-- `∑_{t < i < q} C(n, i) ≤ q · n ^ q` for `1 ≤ n`. -/
theorem sum_choose_Ioo_le (n t q : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Ioo t q, n.choose i ≤ q * n ^ q := by
  have hbd : ∀ i ∈ Finset.Ioo t q, n.choose i ≤ n ^ q := fun i hi =>
    (Nat.choose_le_pow n i).trans (Nat.pow_le_pow_right hn (le_of_lt (Finset.mem_Ioo.1 hi).2))
  have hcard : (Finset.Ioo t q).card ≤ q := by rw [Nat.card_Ioo]; omega
  calc ∑ i ∈ Finset.Ioo t q, n.choose i ≤ (Finset.Ioo t q).card • n ^ q :=
        Finset.sum_le_card_nsmul _ _ _ hbd
    _ = (Finset.Ioo t q).card * n ^ q := smul_eq_mul _ _
    _ ≤ q * n ^ q := Nat.mul_le_mul_right _ hcard

/-- Polynomials are eventually dominated by `2 ^ n`. -/
theorem eventually_mul_pow_lt_two_pow (c e : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → c * n ^ e < 2 ^ n := by
  have hlim : Filter.Tendsto (fun n : ℕ ↦ (c : ℝ) * ((n : ℝ) ^ e / 2 ^ n)) Filter.atTop
      (nhds 0) := by
    simpa using
      (tendsto_pow_const_div_const_pow_of_one_lt e (by norm_num : (1 : ℝ) < 2)).const_mul (c : ℝ)
  obtain ⟨n₀, hn₀⟩ :=
    Filter.eventually_atTop.1 (hlim.eventually (gt_mem_nhds (zero_lt_one' ℝ)))
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have h : (c : ℝ) * ((n : ℝ) ^ e / 2 ^ n) < 1 := hn₀ n hn
  rw [← mul_div_assoc, div_lt_one (by positivity)] at h
  exact_mod_cast h

end FranklFuredi
