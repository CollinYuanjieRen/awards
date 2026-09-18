import Erdos673Divisors.Definitions

/-!
# Erdős Problem 673 — density toolkit

Basic manipulations of natural density zero, plus the counting estimates for integers with no
prime factor in a given finite set of primes, and the divergence of `∑ 1/p`.
-/

namespace Erdos673

open Filter Topology

open scoped Classical in
theorem densityZero_iff (S : Set ℕ) : DensityZero S ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.Icc 1 X).filter (· ∈ S)).card : ℝ) ≤ ε * X := by
  unfold DensityZero
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    rw [Filter.eventually_atTop]
    refine ⟨max N 1, fun X hX => ?_⟩
    have hN' : N ≤ X := le_trans (le_max_left _ _) hX
    have hX1 : (1 : ℕ) ≤ X := le_trans (le_max_right _ _) hX
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
    have := hN X hN'
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    rw [div_lt_iff₀ hXpos] at this
    linarith
  · intro h ε hε
    have hhalf : (0 : ℝ) < ε / 2 := by linarith
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h (ε / 2) hhalf)
    refine ⟨max N 1, fun X hX => ?_⟩
    have hN' : N ≤ X := le_trans (le_max_left _ _) hX
    have hX1 : (1 : ℕ) ≤ X := le_trans (le_max_right _ _) hX
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
    have hb := hN X hN'
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hXpos]
    have : ε / 2 * X < ε * X := by
      have : (0 : ℝ) < ε / 2 := hhalf
      nlinarith
    linarith

open scoped Classical in
theorem DensityZero.mono {S T : Set ℕ} (h : DensityZero T) (hST : S ⊆ T) : DensityZero S := by
  rw [densityZero_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with X hX
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) hX
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hST hn.2⟩

open scoped Classical in
theorem DensityZero.union {S T : Set ℕ} (hS : DensityZero S) (hT : DensityZero T) :
    DensityZero (S ∪ T) := by
  rw [densityZero_iff] at hS hT ⊢
  intro ε hε
  have hhalf : (0 : ℝ) < ε / 2 := by linarith
  filter_upwards [hS (ε / 2) hhalf, hT (ε / 2) hhalf] with X hXS hXT
  have key : ∀ inst : DecidablePred (fun n : ℕ => n ∈ S ∪ T),
      ((@Finset.filter ℕ (fun n => n ∈ S ∪ T) inst (Finset.Icc 1 X)).card : ℝ) ≤ ε * X := by
    intro inst
    have hcard : (@Finset.filter ℕ (fun n => n ∈ S ∪ T) inst (Finset.Icc 1 X)).card ≤
        ((Finset.Icc 1 X).filter (· ∈ S)).card + ((Finset.Icc 1 X).filter (· ∈ T)).card := by
      refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union] at hn ⊢
      rcases hn.2 with h1 | h1
      · exact Or.inl ⟨hn.1, h1⟩
      · exact Or.inr ⟨hn.1, h1⟩
    have hcast : ((@Finset.filter ℕ (fun n => n ∈ S ∪ T) inst (Finset.Icc 1 X)).card : ℝ) ≤
        (((Finset.Icc 1 X).filter (· ∈ S)).card : ℝ) +
          (((Finset.Icc 1 X).filter (· ∈ T)).card : ℝ) := by exact_mod_cast hcard
    linarith
  exact key _

/-- Counting integers coprime to `m` in `[1, X]`. -/
theorem card_coprime_le (m X : ℕ) (hm : 0 < m) :
    ((Finset.Icc 1 X).filter (fun n => Nat.Coprime n m)).card ≤ (X / m + 1) * Nat.totient m := by
  classical
  have hsub : Finset.Icc 1 X ⊆
      (Finset.range (X / m + 1)).biUnion (fun k => Finset.Ico (k * m) (k * m + m)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ico]
    refine ⟨n / m, Nat.lt_succ_of_le (Nat.div_le_div_right hn.2), Nat.div_mul_le_self n m,
      Nat.lt_div_mul_add hm⟩
  have hblock : ∀ k : ℕ,
      ((Finset.Ico (k * m) (k * m + m)).filter (fun n => Nat.Coprime n m)).card
        = Nat.totient m := by
    intro k
    have hcongr : (Finset.Ico (k * m) (k * m + m)).filter (fun n => Nat.Coprime n m)
        = (Finset.Ico (k * m) (k * m + m)).filter (fun x => Nat.Coprime m x) :=
      Finset.filter_congr (fun x _ => by rw [Nat.coprime_comm])
    rw [hcongr]
    exact Nat.filter_coprime_Ico_eq_totient m (k * m)
  calc ((Finset.Icc 1 X).filter (fun n => Nat.Coprime n m)).card
      ≤ (((Finset.range (X / m + 1)).biUnion
            (fun k => Finset.Ico (k * m) (k * m + m))).filter (fun n => Nat.Coprime n m)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ hsub)
    _ = ((Finset.range (X / m + 1)).biUnion
            (fun k => (Finset.Ico (k * m) (k * m + m)).filter (fun n => Nat.Coprime n m))).card := by
        rw [Finset.filter_biUnion]
    _ ≤ ∑ _k ∈ Finset.range (X / m + 1), Nat.totient m := by
        refine le_trans (Finset.card_biUnion_le) ?_
        exact Finset.sum_le_sum (fun k _ => le_of_eq (hblock k))
    _ = (X / m + 1) * Nat.totient m := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]


/-- `φ(∏Q)/∏Q ≤ exp(−∑_{p∈Q} 1/p)` for a finset of primes. -/
theorem totient_div_le_exp (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    ((Nat.totient (∏ p ∈ Q, p) : ℝ) / (∏ p ∈ Q, p : ℕ)) ≤ Real.exp (-(∑ p ∈ Q, (1 : ℝ) / p)) := by
  have hppos : ∀ p ∈ Q, 0 < p := fun p hp => (hQ p hp).pos
  have hmpos : 0 < ∏ p ∈ Q, p := Finset.prod_pos hppos
  have hpf : (∏ p ∈ Q, p).primeFactors = Q := Nat.primeFactors_prod hQ
  -- `φ(∏Q) = ∏ (p - 1)`
  have hkey := Nat.totient_mul_prod_primeFactors (∏ p ∈ Q, p)
  rw [hpf] at hkey
  have htot : Nat.totient (∏ p ∈ Q, p) = ∏ p ∈ Q, (p - 1) := by
    refine Nat.eq_of_mul_eq_mul_right hmpos ?_
    rw [hkey, mul_comm]
  -- cast to `ℝ`
  have hcast : ((∏ p ∈ Q, (p - 1) : ℕ) : ℝ) = ∏ p ∈ Q, ((p : ℝ) - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have : (1 : ℕ) ≤ p := (hQ p hp).one_lt.le
    push_cast [Nat.cast_sub this]
    ring
  have hmcast : ((∏ p ∈ Q, p : ℕ) : ℝ) = ∏ p ∈ Q, (p : ℝ) := Nat.cast_prod _ _
  rw [htot, hcast, hmcast, ← Finset.prod_div_distrib]
  calc ∏ p ∈ Q, (((p : ℝ) - 1) / p) ≤ ∏ p ∈ Q, Real.exp (-((1 : ℝ) / p)) := by
        refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
        · have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hQ p hp).one_lt.le
          have h0 : (0 : ℝ) < (p : ℝ) := by linarith
          positivity
        · have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hQ p hp).one_lt.le
          have h0 : (0 : ℝ) < (p : ℝ) := by linarith
          have hexp := Real.add_one_le_exp (-((1 : ℝ) / p))
          have heq : ((p : ℝ) - 1) / p = -((1 : ℝ) / p) + 1 := by
            field_simp
            ring
          rw [heq]
          exact hexp
    _ = Real.exp (-(∑ p ∈ Q, (1 : ℝ) / p)) := by
        rw [← Real.exp_sum, ← Finset.sum_neg_distrib]


/-- The integers with no prime factor in `Q` are sparse: count `≤ exp(−S)·X + φ(∏Q)`. -/
theorem card_no_prime_factor_le (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (X : ℕ) :
    (((Finset.Icc 1 X).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n)).card : ℝ) ≤
      Real.exp (-(∑ p ∈ Q, (1 : ℝ) / p)) * X + Nat.totient (∏ p ∈ Q, p) := by
  classical
  set m : ℕ := ∏ p ∈ Q, p with hmdef
  have hmpos : 0 < m := Finset.prod_pos (fun p hp => (hQ p hp).pos)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  -- every `n` with no prime factor in `Q` is coprime to `m`
  have hstep : ((Finset.Icc 1 X).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n)).card ≤
      ((Finset.Icc 1 X).filter (fun n => Nat.Coprime n m)).card := by
    refine Finset.card_le_card ?_
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    refine ⟨hn.1, ?_⟩
    exact Nat.Coprime.prod_right (fun p hp =>
      Nat.Coprime.symm (((hQ p hp).coprime_iff_not_dvd).mpr (hn.2 p hp)))
  have hcount := card_coprime_le m X hmpos
  have hnat : ((Finset.Icc 1 X).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n)).card ≤
      (X / m + 1) * Nat.totient m := le_trans hstep hcount
  have hR : (((Finset.Icc 1 X).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n)).card : ℝ) ≤
      ((X / m : ℕ) : ℝ) * Nat.totient m + Nat.totient m := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this
    calc (((Finset.Icc 1 X).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n)).card : ℝ)
        ≤ (((X / m : ℕ) : ℝ) + 1) * (Nat.totient m : ℝ) := this
      _ = ((X / m : ℕ) : ℝ) * Nat.totient m + Nat.totient m := by ring
  have htotnn : (0 : ℝ) ≤ Nat.totient m := by positivity
  have hdiv : ((X / m : ℕ) : ℝ) ≤ (X : ℝ) / m := Nat.cast_div_le
  have h1 : ((X / m : ℕ) : ℝ) * Nat.totient m ≤ (X : ℝ) / m * Nat.totient m :=
    mul_le_mul_of_nonneg_right hdiv htotnn
  have h2 : (X : ℝ) / m * Nat.totient m = (X : ℝ) * ((Nat.totient m : ℝ) / m) := by
    field_simp
  have h3 : ((Nat.totient m : ℝ) / m) ≤ Real.exp (-(∑ p ∈ Q, (1 : ℝ) / p)) := by
    rw [hmdef]
    exact totient_div_le_exp Q hQ
  have hXnn : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have h4 : (X : ℝ) * ((Nat.totient m : ℝ) / m) ≤
      Real.exp (-(∑ p ∈ Q, (1 : ℝ) / p)) * X := by
    rw [mul_comm (Real.exp _) (X : ℝ)]
    exact mul_le_mul_of_nonneg_left h3 hXnn
  linarith

/-- The coercion `Nat.Primes → ℕ` as an embedding. -/
def primesEmb : Nat.Primes ↪ ℕ := ⟨fun p => (p : ℕ), fun _ _ h => Subtype.ext h⟩

/-- Divergence of `∑ 1/p`: every bound is exceeded by some finset of primes. -/
theorem exists_finset_primes_sum_gt (S₀ : ℝ) :
    ∃ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) ∧ S₀ < ∑ p ∈ Q, (1 : ℝ) / p := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  refine Nat.Primes.not_summable_one_div ?_
  refine summable_of_sum_le (c := S₀) (fun p => by positivity) (fun u => ?_)
  have hemb : ∀ p ∈ u.map primesEmb, Nat.Prime p := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hp
    exact q.2
  have hb := hcon (u.map primesEmb) hemb
  rw [Finset.sum_map] at hb
  exact hb


end Erdos673
