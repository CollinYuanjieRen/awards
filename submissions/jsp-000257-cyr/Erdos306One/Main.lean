import Mathlib

/-!
# Erdős Problem #306, the instance `a/b = 1`: Watanabe's 47-term certificate

Erdős and Graham asked whether every positive rational `a/b` with `b` squarefree is a sum of
distinct unit fractions whose denominators are products of two distinct primes.  The general
question is open.  For `a/b = 1` explicit decompositions are known; the shortest known ones,
with 47 terms, were found by Watanabe (arXiv:2009.03275, §3.3).  This file certifies the first
of Watanabe's 47-term decompositions.

The statement `erdos_306_one` is the instance `q = 1` of the formal-conjectures rendering of
Erdős Problem #306 (`n 0 = 1`, strictly increasing `n`, each `n i` with `ω (n i) = 2` and
`Ω (n i) = 2`, and `1 = ∑ 1 / n i`), so that it can be compared against the official target.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

/-- Watanabe's 47 semiprime denominators (arXiv:2009.03275, §3.3, first example), preceded by
the placeholder `n 0 = 1` used by the formal-conjectures statement. -/
def watanabeDenominators : Fin 48 → ℕ :=
  ![1, 6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62, 65, 69, 74, 82, 85,
    86, 87, 91, 93, 95, 106, 111, 123, 133, 145, 155, 159, 185, 203, 215, 253, 265, 287, 319, 493,
    583, 731, 851, 1073]

/-- A product of two distinct primes has exactly two prime factors, both with and without
multiplicity. -/
theorem cardDistinctFactors_and_cardFactors_prime_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : ω (p * q) = 2 ∧ Ω (p * q) = 2 := by
  refine ⟨?_, ?_⟩
  · rw [cardDistinctFactors_mul ((Nat.coprime_primes hp hq).2 hpq),
      cardDistinctFactors_apply_prime hp, cardDistinctFactors_apply_prime hq]
  · rw [cardFactors_mul hp.ne_zero hq.ne_zero, cardFactors_apply_prime hp,
      cardFactors_apply_prime hq]

/-- Each of Watanabe's denominators is a product of two distinct primes. -/
theorem watanabeDenominators_semiprime (i : Fin 48) (hi : i ∈ Finset.Icc 1 (Fin.last 47)) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ watanabeDenominators i = p * q := by
  fin_cases i
  · exact absurd hi (by decide)
  · exact ⟨2, 3, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨2, 5, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨2, 7, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 5, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 7, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨2, 11, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨2, 13, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 11, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨2, 17, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 7, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨2, 19, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 13, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨2, 23, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 17, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 11, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 19, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨2, 29, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨2, 31, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 13, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 23, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨2, 37, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨2, 41, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 17, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨2, 43, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 29, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨7, 13, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 31, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 19, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨2, 53, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 37, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 41, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨7, 19, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 29, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 31, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 53, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 37, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨7, 29, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 43, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨11, 23, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 53, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨7, 41, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨11, 29, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨17, 29, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨11, 53, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨17, 43, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨23, 37, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact ⟨29, 37, by norm_num, by norm_num, by norm_num, rfl⟩

/-- The reciprocals of Watanabe's 47 denominators sum to `1`. -/
theorem watanabeDenominators_sum :
    (1 : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last 47), (1 : ℚ) / watanabeDenominators i := by
  have h0 : Finset.Icc (1 : Fin 48) (Fin.last 47) = Finset.univ.erase 0 := by decide
  have h1 : ∑ i : Fin 48, (1 : ℚ) / watanabeDenominators i = 2 := by
    norm_num [Fin.sum_univ_succ, watanabeDenominators]
  have h2 : (1 : ℚ) / watanabeDenominators 0 +
      ∑ i ∈ Finset.univ.erase (0 : Fin 48), (1 : ℚ) / watanabeDenominators i =
      ∑ i : Fin 48, (1 : ℚ) / watanabeDenominators i :=
    Finset.add_sum_erase _ (fun i : Fin 48 ↦ (1 : ℚ) / watanabeDenominators i)
      (Finset.mem_univ 0)
  have h3 : (1 : ℚ) / watanabeDenominators 0 = 1 := by
    norm_num [watanabeDenominators]
  rw [h0]
  rw [h1, h3] at h2
  linarith

/-- **Erdős Problem #306 for `a/b = 1`.**  There are `1 = n 0 < n 1 < ⋯ < n 47`, each `n i`
(`i ≥ 1`) a product of exactly two distinct primes (`ω (n i) = 2 ∧ Ω (n i) = 2`), with
`1 = ∑_{i=1}^{47} 1 / n i`.  This is the instance `q = 1` of the formal-conjectures statement of
the problem; the general question for arbitrary `a/b` with `b` squarefree remains open. -/
theorem erdos_306_one :
    ∃ k : ℕ, ∃ n : Fin (k + 1) → ℕ, n 0 = 1 ∧ StrictMono n ∧
      (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
      (1 : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) := by
  refine ⟨47, watanabeDenominators, rfl, Fin.strictMono_iff_lt_succ.2 ?_, ?_,
    watanabeDenominators_sum⟩
  · decide
  · intro i hi
    obtain ⟨p, q, hp, hq, hpq, h⟩ := watanabeDenominators_semiprime i hi
    rw [h]
    exact cardDistinctFactors_and_cardFactors_prime_mul hp hq hpq.ne
