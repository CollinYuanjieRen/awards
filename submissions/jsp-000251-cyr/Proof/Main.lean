import Proof.Bound

/-!
# Erdős Problem 295: the Erdős–Straus lower bound `k(N) ≥ (e - 1)(N - 1)`

If `1 = ∑_{d ∈ D} 1 / d` with `k` distinct denominators `≥ N ≥ 1`, then
`1 ≤ 1 / N + log ((N + k - 1) / N)`, so `(N + k - 1) / N ≥ exp (1 - 1 / N) ≥ e (1 - 1 / N)`,
i.e. `k ≥ (e - 1)(N - 1)`.  (For `N = 0` the bound is negative and trivial.)
-/

namespace Erdos295

/-- **Erdős–Straus (1971), lower bound, universal form.** Every representation of `1` by
distinct unit fractions with denominators `≥ N` uses at least `(e - 1)(N - 1)` of them. -/
theorem card_ge_of_isUnitRepr (N : ℕ) (D : Finset ℕ) (hD : IsUnitRepr N D) :
    (Real.exp 1 - 1) * ((N : ℝ) - 1) ≤ D.card := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hcard0 : (0 : ℝ) ≤ (D.card : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos N with hN0 | hN1
  · subst hN0
    push_cast
    nlinarith
  · have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hkpos : 0 < D.card := Finset.card_pos.mpr hD.nonempty
    have hkR : (1 : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast hkpos
    have h1 : ∑ d ∈ D, (1 : ℝ) / d = 1 := hD.sum_real
    have h2 := sum_inv_le_harmonic N hN1 D hD.1
    have h3 := harmonic_le_log N D.card hN1 hkpos
    have hchain : (1 : ℝ) ≤ 1 / N + Real.log ((N : ℝ) + D.card - 1) - Real.log N := by
      linarith
    have hLpos : (0 : ℝ) < (N : ℝ) + D.card - 1 := by linarith
    have hlog : (1 : ℝ) - 1 / N ≤ Real.log (((N : ℝ) + D.card - 1) / N) := by
      rw [Real.log_div (ne_of_gt hLpos) (ne_of_gt hNpos)]
      linarith
    have hexp : Real.exp 1 * (1 - 1 / (N : ℝ)) ≤ ((N : ℝ) + D.card - 1) / N := by
      have h4 : Real.exp (1 - 1 / (N : ℝ)) ≤ ((N : ℝ) + D.card - 1) / N := by
        calc Real.exp (1 - 1 / (N : ℝ)) ≤ Real.exp (Real.log (((N : ℝ) + D.card - 1) / N)) :=
              Real.exp_le_exp.mpr hlog
          _ = ((N : ℝ) + D.card - 1) / N := Real.exp_log (div_pos hLpos hNpos)
      have h5 : Real.exp 1 * (1 - 1 / (N : ℝ)) ≤ Real.exp (1 - 1 / (N : ℝ)) := by
        have h6 : 1 - 1 / (N : ℝ) ≤ Real.exp (-(1 / (N : ℝ))) := by
          have h7 := Real.add_one_le_exp (-(1 / (N : ℝ)))
          linarith
        have h8 : Real.exp (1 - 1 / (N : ℝ)) = Real.exp 1 * Real.exp (-(1 / (N : ℝ))) := by
          rw [← Real.exp_add]
          ring_nf
        rw [h8]
        exact mul_le_mul_of_nonneg_left h6 (le_of_lt (Real.exp_pos 1))
      linarith
    have key : Real.exp 1 * ((N : ℝ) - 1) ≤ (N : ℝ) + D.card - 1 := by
      have h9 := (le_div_iff₀ hNpos).mp hexp
      have h10 : Real.exp 1 * (1 - 1 / (N : ℝ)) * N = Real.exp 1 * ((N : ℝ) - 1) := by
        field_simp
      linarith [h10 ▸ h9]
    nlinarith

/-- The lower bound for Erdős's `k(N)`, whenever some representation exists. -/
theorem le_kmin (N : ℕ) (h : ∃ D : Finset ℕ, IsUnitRepr N D) :
    (Real.exp 1 - 1) * ((N : ℝ) - 1) ≤ kmin N := by
  obtain ⟨D, hD⟩ := h
  have hne : {m : ℕ | ∃ D : Finset ℕ, IsUnitRepr N D ∧ D.card = m}.Nonempty :=
    ⟨D.card, D, hD, rfl⟩
  obtain ⟨D', hD', hcard⟩ := Nat.sInf_mem hne
  have hk : D'.card = kmin N := hcard
  rw [← hk]
  exact card_ge_of_isUnitRepr N D' hD'

end Erdos295
