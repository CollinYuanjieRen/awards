import Erdos673Divisors.Moments
import Erdos673Divisors.Average

/-!
# Erdős Problem 673 — main theorems

`G(n) → ∞` for almost all `n`: for every threshold `T` the exceptional set `{n | G n ≤ T}` has
natural density zero.  Fix `T` and `ε > 0`.  Choose a finite set `Q` of primes with
`∑_{p ∈ Q} 1/p` so large that `exp(−∑_{p∈Q} 1/p) ≤ ε/3`, put `P := max Q` and `T' := ⌈2·P·T⌉₊`.
If `n ≥ 1` has some prime factor `p ∈ Q`, then `τ(n)/(2p) ≤ G(n) ≤ T`, so `τ(n) ≤ 2PT ≤ T'`;
hence
`{n | G n ≤ T} ⊆ {n | ∀ p ∈ Q, ¬ p ∣ n} ∪ {n | τ n ≤ T'}`.
The first set has counting function `≤ (ε/3)X + φ(∏Q)` (`card_no_prime_factor_le`), the second
has density zero (`densityZero_card_divisors_le`), and `φ(∏Q) ≤ (ε/3)X` for large `X`.
Together with the average statement `erdos_673_average` this gives the closed root.
-/

namespace Erdos673

open Filter Topology

/-- For every threshold `T`, the set of `n` with `G n ≤ T` has natural density zero:
`G(n) → ∞` for almost all `n`. -/
theorem erdos_673 : ∀ T : ℝ, DensityZero {n : ℕ | G n ≤ T} := by
  intro T
  rw [densityZero_iff]
  intro ε hε
  rcases le_or_gt 0 T with hT0 | hT0
  · -- Main case: `0 ≤ T`.
    obtain ⟨Q, hQ, hQsum⟩ := exists_finset_primes_sum_gt (max 1 (Real.log (3 / ε)))
    have hε3 : (0 : ℝ) < ε / 3 := by linarith
    -- `exp(−S) ≤ ε/3` where `S = ∑_{p ∈ Q} 1/p`.
    have hexp : Real.exp (-(∑ p ∈ Q, (1 : ℝ) / p)) ≤ ε / 3 := by
      have hSlog : Real.log (3 / ε) < ∑ p ∈ Q, (1 : ℝ) / p :=
        lt_of_le_of_lt (le_max_right _ _) hQsum
      have hlog : Real.log (ε / 3) = -Real.log (3 / ε) := by
        rw [← Real.log_inv]
        congr 1
        rw [inv_div]
      have h1 : Real.exp (-(∑ p ∈ Q, (1 : ℝ) / p)) ≤ Real.exp (Real.log (ε / 3)) :=
        Real.exp_le_exp.2 (by rw [hlog]; linarith)
      rwa [Real.exp_log hε3] at h1
    -- A bound `P` for the primes of `Q`, and the divisor threshold `T'`.
    obtain ⟨P, hP⟩ : ∃ P : ℕ, ∀ p ∈ Q, p ≤ P :=
      ⟨Q.sup id, fun p hp => Finset.le_sup (f := id) hp⟩
    obtain ⟨T', hT'⟩ : ∃ T' : ℕ, 2 * (P : ℝ) * T ≤ (T' : ℝ) :=
      ⟨⌈2 * (P : ℝ) * T⌉₊, Nat.le_ceil _⟩
    -- The set `{n | τ n ≤ T'}` has density zero.
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
      ((densityZero_iff {n : ℕ | (Nat.divisors n).card ≤ T'}).1
        (densityZero_card_divisors_le T') (ε / 3) hε3)
    refine Filter.eventually_atTop.2
      ⟨max N₁ ⌈3 * (Nat.totient (∏ p ∈ Q, p) : ℝ) / ε⌉₊, fun X hX => ?_⟩
    have hXN₁ : N₁ ≤ X := le_trans (le_max_left _ _) hX
    have hXc : ⌈3 * (Nat.totient (∏ p ∈ Q, p) : ℝ) / ε⌉₊ ≤ X := le_trans (le_max_right _ _) hX
    have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
    -- The three pieces of the estimate.
    have hB : (((Finset.Icc 1 X).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n)).card : ℝ) ≤
        ε / 3 * X + Nat.totient (∏ p ∈ Q, p) := by
      have h := card_no_prime_factor_le Q hQ X
      have h2 : Real.exp (-(∑ p ∈ Q, (1 : ℝ) / p)) * X ≤ ε / 3 * X :=
        mul_le_mul_of_nonneg_right hexp hXnn
      linarith
    have hC : (((Finset.Icc 1 X).filter (fun n => (Nat.divisors n).card ≤ T')).card : ℝ) ≤
        ε / 3 * X := by
      refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (hN₁ X hXN₁)
      intro n hn
      simp only [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, hn.2⟩
    have hphi : (Nat.totient (∏ p ∈ Q, p) : ℝ) ≤ ε / 3 * X := by
      have h1 : 3 * (Nat.totient (∏ p ∈ Q, p) : ℝ) / ε ≤ (X : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast hXc)
      have h2 := (div_le_iff₀ hε).mp h1
      have h3 : ε / 3 * (X : ℝ) = (X : ℝ) * ε / 3 := by ring
      rw [h3]
      linarith
    -- The key inclusion, stated for an arbitrary decidability instance.
    have hfinal : ∀ inst : DecidablePred (fun n : ℕ => n ∈ {n : ℕ | G n ≤ T}),
        ((@Finset.filter ℕ (fun n => n ∈ {n : ℕ | G n ≤ T}) inst (Finset.Icc 1 X)).card : ℝ) ≤
          ε * X := by
      intro inst
      have hsplit :
          (@Finset.filter ℕ (fun n => n ∈ {n : ℕ | G n ≤ T}) inst (Finset.Icc 1 X)).card ≤
            ((Finset.Icc 1 X).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n)).card +
              ((Finset.Icc 1 X).filter (fun n => (Nat.divisors n).card ≤ T')).card := by
        refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_union] at hn ⊢
        obtain ⟨hn1, hn2⟩ := hn
        have hGn : G n ≤ T := hn2
        have hn0 : 0 < n := (Finset.mem_Icc.mp hn1).1
        by_cases hex : ∃ p ∈ Q, p ∣ n
        · obtain ⟨p, hpQ, hpn⟩ := hex
          refine Or.inr ⟨hn1, ?_⟩
          have hp := hQ p hpQ
          have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
          have hppos : (0 : ℝ) < 2 * (p : ℝ) := by linarith
          have hkey := card_divisors_le_mul_G hn0 hp hpn
          rw [div_le_iff₀ hppos] at hkey
          have h2 : G n * (2 * (p : ℝ)) ≤ T * (2 * (p : ℝ)) :=
            mul_le_mul_of_nonneg_right hGn hppos.le
          have hpP : (p : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP p hpQ
          have h3 : T * (2 * (p : ℝ)) ≤ 2 * (P : ℝ) * T := by nlinarith
          have h4 : ((Nat.divisors n).card : ℝ) ≤ (T' : ℝ) := by linarith
          exact_mod_cast h4
        · exact Or.inl ⟨hn1, fun p hp hpn => hex ⟨p, hp, hpn⟩⟩
      have hcast :
          ((@Finset.filter ℕ (fun n => n ∈ {n : ℕ | G n ≤ T}) inst (Finset.Icc 1 X)).card : ℝ) ≤
            (((Finset.Icc 1 X).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n)).card : ℝ) +
              (((Finset.Icc 1 X).filter (fun n => (Nat.divisors n).card ≤ T')).card : ℝ) := by
        exact_mod_cast hsplit
      linarith
    exact hfinal _
  · -- Degenerate case: `T < 0`, where the exceptional set is empty since `G n ≥ 0`.
    refine Filter.Eventually.of_forall (fun X => ?_)
    have key : ∀ inst : DecidablePred (fun n : ℕ => n ∈ {n : ℕ | G n ≤ T}),
        ((@Finset.filter ℕ (fun n => n ∈ {n : ℕ | G n ≤ T}) inst (Finset.Icc 1 X)).card : ℝ) ≤
          ε * X := by
      intro inst
      have hz : (@Finset.filter ℕ (fun n => n ∈ {n : ℕ | G n ≤ T}) inst (Finset.Icc 1 X)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro n _ hmem
        have h1 : G n ≤ T := hmem
        have h2 := G_nonneg n
        linarith
      rw [hz, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hε.le (Nat.cast_nonneg X)
    exact key _

/-- The closed form of Erdős problem 673: `G(n) → ∞` for almost all `n`, and `G` grows without
bound on average. -/
theorem erdos_673_closed : (∀ T : ℝ, DensityZero {n : ℕ | G n ≤ T}) ∧
    Filter.Tendsto (fun X : ℕ => (∑ n ∈ Finset.Icc 1 X, G n) / X) Filter.atTop Filter.atTop :=
  ⟨erdos_673, erdos_673_average⟩

end Erdos673
