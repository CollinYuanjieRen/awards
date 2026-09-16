import Proof.Phase

/-!
# Erdős Problem 1147: the negative answer (Konieczny 2016, Proposition 1.3)

For every threshold function `ε : ℕ → ℝ` with `ε n → 0`, the set `{n ≥ 1 : ‖√2 n²‖ ≤ ε n}` is not
an asymptotic additive basis of order `2`: none of the Pell numbers `N_j` (for `j` large) is a sum
of two of its elements.  In particular the set `{n ≥ 1 : ‖α n²‖ < 1 / log n}` is not a basis of
order `2` for `α = √2`, which answers Erdős's question negatively.
-/

open Filter

namespace Erdos1147

/-- The second horn of the argument: if a split `a + b = N_j` has `‖√2 a²‖ > 1/5`, then `a` is
below the threshold `M` where `ε` has dropped under `1/5`, hence `a` is one of finitely many
values; for those, `‖√2 b²‖ = ‖√2 (N_j - a)²‖` is bounded below by `nd (θ a) / 2`, which `ε b`
has already dropped under.  So `b` cannot lie in the recurrence set. -/
private theorem bad_summand {ε : ℕ → ℝ} {J M₂ : ℕ → ℕ} {M Ms j a b : ℕ} (hab : a + b = pN j)
    (ha : nd (Real.sqrt 2 * (a : ℝ) ^ 2) ≤ ε a) (hb : nd (Real.sqrt 2 * (b : ℝ) ^ 2) ≤ ε b)
    (hbig : 1 / 5 < nd (Real.sqrt 2 * (a : ℝ) ^ 2))
    (hJ : ∀ n₁ i : ℕ, J n₁ ≤ i →
      nd (theta n₁) / 2 ≤ nd (Real.sqrt 2 * ((pN i - n₁ : ℕ) : ℝ) ^ 2))
    (hjJ : ∀ n₁ : ℕ, n₁ < M → J n₁ ≤ j) (hM : ∀ n : ℕ, M ≤ n → ε n < 1 / 5)
    (hM₂ : ∀ n₁ n : ℕ, M₂ n₁ ≤ n → ε n < nd (theta n₁) / 2)
    (hsup : ∀ n₁ : ℕ, n₁ < M → M₂ n₁ ≤ Ms) (hNj : M + Ms ≤ pN j) : False := by
  have haM : a < M := by
    by_contra hcon
    have hlt : ε a < 1 / 5 := hM a (not_lt.1 hcon)
    linarith
  have hMb : M₂ a ≤ b := by
    have := hsup a haM
    omega
  have key : nd (theta a) / 2 ≤ nd (Real.sqrt 2 * (b : ℝ) ^ 2) := by
    have h := hJ a j (hjJ a haM)
    rwa [show (pN j - a : ℕ) = b from by omega] at h
  have hlt : ε b < nd (theta a) / 2 := hM₂ a b hMb
  linarith

/-- **Konieczny, Proposition 1.3 (case `ε n → 0`).** -/
theorem sqrtTwo_recSet_not_basis (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0)) :
    ¬ IsAsymptoticBasis2 (recSet (Real.sqrt 2) ε) := by
  rintro ⟨n₀, hbasis⟩
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hε).2 (1 / 5) (by norm_num))
  choose J hJ using nd_second_summand_ge
  have hthr : ∀ n₁ : ℕ, ∃ K : ℕ, ∀ n : ℕ, K ≤ n → ε n < nd (theta n₁) / 2 := fun n₁ =>
    Filter.eventually_atTop.1 ((tendsto_order.1 hε).2 _ (by linarith [nd_theta_pos n₁]))
  choose M₂ hM₂ using hthr
  obtain ⟨Ms, hsup⟩ : ∃ Ms : ℕ, ∀ n₁ : ℕ, n₁ < M → M₂ n₁ ≤ Ms :=
    ⟨(Finset.range M).sup M₂, fun _ h => Finset.le_sup (Finset.mem_range.2 h)⟩
  obtain ⟨j, hjJ, hjle⟩ : ∃ j : ℕ, (∀ n₁ : ℕ, n₁ < M → J n₁ ≤ j) ∧ n₀ + M + Ms ≤ j :=
    ⟨max ((Finset.range M).sup J) (n₀ + M + Ms),
      fun _ h => le_trans (Finset.le_sup (Finset.mem_range.2 h)) (le_max_left _ _),
      le_max_right _ _⟩
  have hpN : j + 1 ≤ pN j := succ_le_pN j
  obtain ⟨a, ha, b, hb, hab⟩ := hbasis (pN j) (by omega)
  obtain ⟨-, ha2⟩ := ha
  obtain ⟨-, hb2⟩ := hb
  by_cases h₁ : nd (Real.sqrt 2 * (a : ℝ) ^ 2) ≤ 1 / 5
  · by_cases h₂ : nd (Real.sqrt 2 * (b : ℝ) ^ 2) ≤ 1 / 5
    · exact not_both_close j a (by omega) (le_refl ((1 : ℝ) / 5)) h₁
        (by rwa [show (pN j - a : ℕ) = b from by omega])
    · exact bad_summand (by omega) hb2 ha2 (not_le.1 h₂) hJ hjJ hM hM₂ hsup (by omega)
  · exact bad_summand hab ha2 hb2 (not_le.1 h₁) hJ hjJ hM hM₂ hsup (by omega)

/-- The recurrence set with threshold `1 / log n` for `α = √2` is not an asymptotic basis. -/
theorem sqrtTwo_recSet_log_not_basis :
    ¬ IsAsymptoticBasis2 (recSet (Real.sqrt 2) (fun n => 1 / Real.log n)) := by
  refine sqrtTwo_recSet_not_basis _ ?_
  have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  simpa [Function.comp_def, Pi.inv_def, one_div] using h

/-- The set displayed in Erdős Problem 1147 with `α = √2` is not an asymptotic basis of
order `2`. -/
theorem sqrtTwo_erdosSet_not_basis : ¬ IsAsymptoticBasis2 (erdosSet (Real.sqrt 2)) := by
  intro h
  exact sqrtTwo_recSet_log_not_basis (h.mono (erdosSet_subset_recSet _))

/-- **Erdős Problem 1147 has a negative answer** (`≤`-threshold reading): it is not the case
that for every positive irrational `α` the set `{n ≥ 1 : ‖α n²‖ ≤ 1 / log n}` is an asymptotic
basis of order `2`. -/
theorem not_erdos_1147_le :
    ¬ ∀ α : ℝ, 0 < α → Irrational α →
      IsAsymptoticBasis2 (recSet α (fun n => 1 / Real.log n)) := by
  intro h
  exact sqrtTwo_recSet_log_not_basis (h (Real.sqrt 2) (by positivity) irrational_sqrt_two)

/-- **Erdős Problem 1147 has a negative answer**: it is not the case that for every positive
irrational `α` the set `{n ≥ 1 : ‖α n²‖ < 1 / log n}` is an asymptotic basis of order `2`. -/
theorem not_erdos_1147 :
    ¬ ∀ α : ℝ, 0 < α → Irrational α → IsAsymptoticBasis2 (erdosSet α) := by
  intro h
  exact sqrtTwo_erdosSet_not_basis (h (Real.sqrt 2) (by positivity) irrational_sqrt_two)

end Erdos1147
