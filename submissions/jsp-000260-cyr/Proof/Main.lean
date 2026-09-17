import Proof.Defs

/-!
# Erdős problem #311: the trivial lower bound `δ(N) ≥ 1/[1, …, N]`

The problem page for Erdős problem #311 calls this bound trivial, and this package proves
exactly it: with `δ(N)` defined (in `Proof.Defs`) as the minimum of the finite
set of non-zero deviations `|1 - ∑_{n ∈ A} 1/n|` over subsets `A ⊆ {1, …, N}`, we show
`1/[1, …, N] ≤ δ(N)` for every `N`.

The argument: writing `L = lcmUpTo N`, every `n ∈ {1, …, N}` divides `L`, so
`L · (1 - ∑_{n ∈ A} 1/n) = L - ∑_{n ∈ A} (L/n)` is an integer. If `1 - ∑_{n ∈ A} 1/n ≠ 0`
that integer is non-zero, hence has absolute value at least `1`, giving
`|1 - ∑_{n ∈ A} 1/n| ≥ 1/L`. Since `δ(N)` is attained by some such subset, `δ(N) ≥ 1/L`.

Not claimed here: the identification `1/[1, …, N] = e^{-(1+o(1))N}` (which needs the prime
number theorem), Tang's upper bound, Kovač's equivalence with the [ErGr80] formulation, and
the conjecture `δ(N) = e^{-(c+o(1))N}` of Erdős problem #311.
-/

namespace Erdos311

/-- Integrality: for `A ⊆ {1, …, N}` the rational number `[1, …, N] · (1 - ∑_{n ∈ A} 1/n)`
equals the integer `[1, …, N] - ∑_{n ∈ A} [1, …, N]/n`. -/
theorem exists_int_mul (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    ∃ z : ℤ, (lcmUpTo N : ℚ) * (1 - unitSum A) = z := by
  refine ⟨(lcmUpTo N : ℤ) - ∑ n ∈ A, ((lcmUpTo N / n : ℕ) : ℤ), ?_⟩
  have key : ∀ n ∈ A, (lcmUpTo N : ℚ) * (n : ℚ)⁻¹ = ((lcmUpTo N / n : ℕ) : ℚ) := by
    intro n hn
    have hmem := hA hn
    have h1 : 1 ≤ n := (Finset.mem_Icc.1 hmem).1
    have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hdvd : n ∣ lcmUpTo N := dvd_lcmUpTo hmem
    rw [Nat.cast_div hdvd hn0, div_eq_mul_inv]
  rw [unitSum, mul_sub, mul_one, Finset.mul_sum, Finset.sum_congr rfl key]
  simp only [Int.cast_sub, Int.cast_sum, Int.cast_natCast]

/-- (T2) For each subset `A ⊆ {1, …, N}` with non-zero deviation, that deviation is at
least `1/[1, …, N]`. -/
theorem one_div_lcm_le_abs (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) (h : 1 - unitSum A ≠ 0) : 1 / (lcmUpTo N : ℚ) ≤ |1 - unitSum A| := by
  obtain ⟨z, hz⟩ := exists_int_mul N A hA
  have hL : (0 : ℚ) < (lcmUpTo N : ℚ) := Nat.cast_pos.2 (lcmUpTo_pos N)
  have hprod : (lcmUpTo N : ℚ) * (1 - unitSum A) ≠ 0 := mul_ne_zero (ne_of_gt hL) h
  have hzne : z ≠ 0 := by
    rintro rfl
    exact hprod (by simpa using hz)
  have h1 : (1 : ℚ) ≤ |(z : ℚ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hzne
  have habs : |(lcmUpTo N : ℚ) * (1 - unitSum A)| = (lcmUpTo N : ℚ) * |1 - unitSum A| := by
    rw [abs_mul, abs_of_pos hL]
  have h2 : (1 : ℚ) ≤ (lcmUpTo N : ℚ) * |1 - unitSum A| := by
    rw [← habs, hz]
    exact h1
  rw [div_le_iff₀ hL, mul_comm]
  exact h2

/-- (T3) `δ(N)` is a lower bound for every non-zero deviation. -/
theorem delta_le (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) (h : 1 - unitSum A ≠ 0) : delta N ≤ |1 - unitSum A| :=
  Finset.min'_le _ _ ((mem_deviations N _).2 ⟨A, hA, h, rfl⟩)

/-- (T4) `δ(N)` is attained: some subset `A ⊆ {1, …, N}` with non-zero deviation realises it. -/
theorem exists_delta_eq (N : ℕ) : ∃ A ⊆ Finset.Icc 1 N, 1 - unitSum A ≠ 0 ∧ delta N = |1 - unitSum A| :=
  (mem_deviations N _).1 (Finset.min'_mem _ _)

/-- (T1) The trivial bound of Erdős problem #311: `δ(N) ≥ 1/[1, …, N]`. -/
theorem one_div_lcm_le_delta (N : ℕ) : 1 / (lcmUpTo N : ℚ) ≤ delta N := by
  obtain ⟨A, hA, h, heq⟩ := exists_delta_eq N
  rw [heq]
  exact one_div_lcm_le_abs N A hA h

/-- (T5) `δ(N)` is positive. -/
theorem delta_pos (N : ℕ) : 0 < delta N := by
  obtain ⟨A, hA, h, heq⟩ := exists_delta_eq N
  rw [heq]
  exact abs_pos.2 h

end Erdos311
