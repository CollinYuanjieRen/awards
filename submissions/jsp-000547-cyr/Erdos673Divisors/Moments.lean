import Erdos673Divisors.Basic
import Erdos673Divisors.Density

/-!
# Erdős Problem 673 — first and second moments of `ω_Q`

For a finite set of primes `Q` we count, for each `n`, how many members of `Q` divide `n`.  The
first two moments of this counting function over `[1, X]` are controlled by `S := ∑_{p ∈ Q} 1/p`,
and Chebyshev's inequality then shows that few `n ≤ X` have `ω_Q(n) ≤ S/2`.  Since
`2 ^ ω_Q(n) ≤ τ(n)`, this gives that `{n | τ(n) ≤ T}` has natural density zero.
-/

namespace Erdos673

open Filter Topology

/-- `ω_Q(n)`: the number of primes of `Q` dividing `n`. -/
def omega (Q : Finset ℕ) (n : ℕ) : ℕ := (Q.filter (· ∣ n)).card

/-! ### Counting multiples in `[1, X]` -/

/-- The multiples of `d` in `[1, X]` number `X / d`. -/
theorem card_Icc_filter_dvd (d X : ℕ) :
    ((Finset.Icc 1 X).filter (fun n => d ∣ n)).card = X / d := by
  have h : Finset.Icc 1 X = Finset.Ioc 0 X := rfl
  rw [h]
  exact Nat.Ioc_filter_dvd_card_eq_div X d

/-- The real-valued indicator sum over `[1, X]` of divisibility by `d`. -/
theorem sum_indicator_dvd (d X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, (if d ∣ n then (1 : ℝ) else 0) = ((X / d : ℕ) : ℝ) := by
  rw [Finset.sum_boole, card_Icc_filter_dvd]

/-- `X / d` loses at most one unit when compared with the real quotient. -/
theorem sub_one_le_cast_div (X d : ℕ) (hd : 0 < d) : (X : ℝ) / d - 1 ≤ ((X / d : ℕ) : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : X < d * (X / d) + d := by
    have h2 := Nat.div_add_mod X d
    have h3 := Nat.mod_lt X hd
    omega
  have h1R : (X : ℝ) < (d : ℝ) * ((X / d : ℕ) : ℝ) + d := by exact_mod_cast h1
  rw [sub_le_iff_le_add, div_le_iff₀ hdR]
  nlinarith

/-- `ω_Q(n)` as a sum of indicators. -/
theorem omega_cast (Q : Finset ℕ) (n : ℕ) :
    (omega Q n : ℝ) = ∑ p ∈ Q, (if p ∣ n then (1 : ℝ) else 0) := by
  rw [omega, ← Finset.sum_boole]

/-! ### First moment -/

theorem sum_omega_ge (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (X : ℕ) :
    (X : ℝ) * (∑ p ∈ Q, (1 : ℝ) / p) - Q.card ≤ ∑ n ∈ Finset.Icc 1 X, (omega Q n : ℝ) := by
  have hswap : ∑ n ∈ Finset.Icc 1 X, (omega Q n : ℝ) = ∑ p ∈ Q, ((X / p : ℕ) : ℝ) := by
    calc ∑ n ∈ Finset.Icc 1 X, (omega Q n : ℝ)
        = ∑ n ∈ Finset.Icc 1 X, ∑ p ∈ Q, (if p ∣ n then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl (fun n _ => omega_cast Q n)
      _ = ∑ p ∈ Q, ∑ n ∈ Finset.Icc 1 X, (if p ∣ n then (1 : ℝ) else 0) := Finset.sum_comm
      _ = ∑ p ∈ Q, ((X / p : ℕ) : ℝ) := Finset.sum_congr rfl (fun p _ => sum_indicator_dvd p X)
  rw [hswap]
  calc (X : ℝ) * (∑ p ∈ Q, (1 : ℝ) / p) - Q.card
      = ∑ p ∈ Q, ((X : ℝ) / p - 1) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun p _ => by ring)
    _ ≤ ∑ p ∈ Q, ((X / p : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun p hp => sub_one_le_cast_div X p (hQ p hp).pos)

/-! ### Second moment -/

theorem sum_omega_sq_le (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, (omega Q n : ℝ) ^ 2 ≤
      (X : ℝ) * (∑ p ∈ Q, (1 : ℝ) / p) ^ 2 + (X : ℝ) * (∑ p ∈ Q, (1 : ℝ) / p) := by
  classical
  set S : ℝ := ∑ p ∈ Q, (1 : ℝ) / p with hSdef
  -- expand the square as a double sum of indicator products
  have hsq : ∀ n : ℕ, (omega Q n : ℝ) ^ 2 =
      ∑ p ∈ Q, ∑ q ∈ Q, (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
    intro n
    rw [sq, omega_cast Q n, Finset.sum_mul_sum]
  have hstep : ∑ n ∈ Finset.Icc 1 X, (omega Q n : ℝ) ^ 2 =
      ∑ p ∈ Q, ∑ q ∈ Q, ∑ n ∈ Finset.Icc 1 X,
        (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
    calc ∑ n ∈ Finset.Icc 1 X, (omega Q n : ℝ) ^ 2
        = ∑ n ∈ Finset.Icc 1 X, ∑ p ∈ Q, ∑ q ∈ Q,
            (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl (fun n _ => hsq n)
      _ = ∑ p ∈ Q, ∑ n ∈ Finset.Icc 1 X, ∑ q ∈ Q,
            (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := Finset.sum_comm
      _ = ∑ p ∈ Q, ∑ q ∈ Q, ∑ n ∈ Finset.Icc 1 X,
            (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
  -- bound each inner sum
  have hbound : ∀ p ∈ Q, ∀ q ∈ Q,
      (∑ n ∈ Finset.Icc 1 X,
          (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)) ≤
        (X : ℝ) * (1 / p) * (1 / q) + (if p = q then (X : ℝ) * (1 / p) else 0) := by
    intro p hp q hq
    have hpp : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).pos
    have hqq : (0 : ℝ) < q := by exact_mod_cast (hQ q hq).pos
    by_cases hpq : p = q
    · subst hpq
      have hid : ∀ n : ℕ, (if p ∣ n then (1 : ℝ) else 0) * (if p ∣ n then (1 : ℝ) else 0)
          = (if p ∣ n then (1 : ℝ) else 0) := by
        intro n
        by_cases h1 : p ∣ n <;> simp [h1]
      have hdiag : (if p = p then (X : ℝ) * (1 / p) else 0) = (X : ℝ) * (1 / p) := by simp
      rw [Finset.sum_congr rfl (fun n _ => hid n), sum_indicator_dvd, hdiag]
      have h2 : ((X / p : ℕ) : ℝ) ≤ (X : ℝ) / p := Nat.cast_div_le
      have h3 : (X : ℝ) / p = (X : ℝ) * (1 / p) := by field_simp
      have h4 : (0 : ℝ) ≤ (X : ℝ) * (1 / p) * (1 / p) := by positivity
      linarith
    · have hcop : Nat.Coprime p q := (Nat.coprime_primes (hQ p hp) (hQ q hq)).2 hpq
      have hmul : ∀ n : ℕ, (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
          = (if p * q ∣ n then (1 : ℝ) else 0) := by
        intro n
        by_cases h1 : p ∣ n
        · by_cases h2 : q ∣ n
          · simp [h1, h2, hcop.mul_dvd_of_dvd_of_dvd h1 h2]
          · have h3 : ¬ (p * q ∣ n) := fun h => h2 ((dvd_mul_left q p).trans h)
            simp [h1, h2, h3]
        · have h3 : ¬ (p * q ∣ n) := fun h => h1 ((dvd_mul_right p q).trans h)
          simp [h1, h3]
      have hoff : (if p = q then (X : ℝ) * (1 / p) else 0) = 0 := by simp [hpq]
      rw [Finset.sum_congr rfl (fun n _ => hmul n), sum_indicator_dvd, hoff, add_zero]
      have h2 : ((X / (p * q) : ℕ) : ℝ) ≤ (X : ℝ) / ((p * q : ℕ) : ℝ) := Nat.cast_div_le
      have h3 : (X : ℝ) / ((p * q : ℕ) : ℝ) = (X : ℝ) * (1 / p) * (1 / q) := by
        push_cast
        field_simp
      rw [h3] at h2
      exact h2
  -- sum the bounds
  have h2 : ∑ p ∈ Q, (X : ℝ) * (1 / p) = (X : ℝ) * S := by rw [hSdef, Finset.mul_sum]
  have hfinal : ∑ p ∈ Q, ∑ q ∈ Q,
      ((X : ℝ) * (1 / p) * (1 / q) + (if p = q then (X : ℝ) * (1 / p) else 0)) =
      (X : ℝ) * S ^ 2 + (X : ℝ) * S := by
    have h1 : ∀ p ∈ Q, (∑ q ∈ Q,
        ((X : ℝ) * (1 / p) * (1 / q) + (if p = q then (X : ℝ) * (1 / p) else 0))) =
        (X : ℝ) * (1 / p) * S + (X : ℝ) * (1 / p) := by
      intro p hp
      have e1 : ∑ q ∈ Q, (X : ℝ) * (1 / p) * (1 / q) = (X : ℝ) * (1 / p) * S := by
        rw [hSdef, Finset.mul_sum]
      have e2 : ∑ q ∈ Q, (if p = q then (X : ℝ) * (1 / p) else 0) = (X : ℝ) * (1 / p) := by
        rw [Finset.sum_ite_eq Q p (fun _ => (X : ℝ) * (1 / p))]
        simp [hp]
      rw [Finset.sum_add_distrib, e1, e2]
    have h3 : ∑ p ∈ Q, (X : ℝ) * (1 / p) * S = (X : ℝ) * S * S := by
      rw [← Finset.sum_mul, h2]
    calc ∑ p ∈ Q, ∑ q ∈ Q,
          ((X : ℝ) * (1 / p) * (1 / q) + (if p = q then (X : ℝ) * (1 / p) else 0))
        = ∑ p ∈ Q, ((X : ℝ) * (1 / p) * S + (X : ℝ) * (1 / p)) := Finset.sum_congr rfl h1
      _ = (∑ p ∈ Q, (X : ℝ) * (1 / p) * S) + ∑ p ∈ Q, (X : ℝ) * (1 / p) := Finset.sum_add_distrib
      _ = (X : ℝ) * S * S + (X : ℝ) * S := by rw [h3, h2]
      _ = (X : ℝ) * S ^ 2 + (X : ℝ) * S := by ring
  calc ∑ n ∈ Finset.Icc 1 X, (omega Q n : ℝ) ^ 2
      = ∑ p ∈ Q, ∑ q ∈ Q, ∑ n ∈ Finset.Icc 1 X,
          (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := hstep
    _ ≤ ∑ p ∈ Q, ∑ q ∈ Q,
          ((X : ℝ) * (1 / p) * (1 / q) + (if p = q then (X : ℝ) * (1 / p) else 0)) :=
        Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => hbound p hp q hq))
    _ = (X : ℝ) * S ^ 2 + (X : ℝ) * S := hfinal

/-! ### Chebyshev -/

theorem card_omega_le_half (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (X : ℕ)
    (hS : 0 < ∑ p ∈ Q, (1 : ℝ) / p) :
    (((Finset.Icc 1 X).filter (fun n => (omega Q n : ℝ) ≤ (∑ p ∈ Q, (1 : ℝ) / p) / 2)).card : ℝ) ≤
      4 * X / (∑ p ∈ Q, (1 : ℝ) / p) + 8 * Q.card / (∑ p ∈ Q, (1 : ℝ) / p) := by
  classical
  set S : ℝ := ∑ p ∈ Q, (1 : ℝ) / p with hSdef
  set A := (Finset.Icc 1 X).filter (fun n => (omega Q n : ℝ) ≤ S / 2) with hAdef
  have hAsub : A ⊆ Finset.Icc 1 X := Finset.filter_subset _ _
  -- lower bound for the variance sum over `A`
  have hlow : (A.card : ℝ) * (S / 2) ^ 2 ≤ ∑ n ∈ A, ((omega Q n : ℝ) - S) ^ 2 := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum A _ _ (fun n hn => ?_)
    have hn' : (omega Q n : ℝ) ≤ S / 2 := (Finset.mem_filter.mp hn).2
    have hnn : (0 : ℝ) ≤ (omega Q n : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ S / 2 - (omega Q n : ℝ))
      (by linarith : (0 : ℝ) ≤ 3 * S / 2 - (omega Q n : ℝ))]
  have hmono : ∑ n ∈ A, ((omega Q n : ℝ) - S) ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 X, ((omega Q n : ℝ) - S) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hAsub (fun n _ _ => sq_nonneg _)
  -- expand the variance sum
  have hcard : (Finset.Icc 1 X).card = X := by simp [Nat.card_Icc]
  have hexp : ∑ n ∈ Finset.Icc 1 X, ((omega Q n : ℝ) - S) ^ 2 =
      (∑ n ∈ Finset.Icc 1 X, (omega Q n : ℝ) ^ 2) -
        2 * S * (∑ n ∈ Finset.Icc 1 X, (omega Q n : ℝ)) + X * S ^ 2 := by
    calc ∑ n ∈ Finset.Icc 1 X, ((omega Q n : ℝ) - S) ^ 2
        = ∑ n ∈ Finset.Icc 1 X,
            (((omega Q n : ℝ) ^ 2 - 2 * S * (omega Q n : ℝ)) + S ^ 2) :=
          Finset.sum_congr rfl (fun n _ => by ring)
      _ = (∑ n ∈ Finset.Icc 1 X, ((omega Q n : ℝ) ^ 2 - 2 * S * (omega Q n : ℝ))) +
            ∑ _n ∈ Finset.Icc 1 X, S ^ 2 := Finset.sum_add_distrib
      _ = (∑ n ∈ Finset.Icc 1 X, (omega Q n : ℝ) ^ 2) -
            2 * S * (∑ n ∈ Finset.Icc 1 X, (omega Q n : ℝ)) + X * S ^ 2 := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul]
  have hup : ∑ n ∈ Finset.Icc 1 X, ((omega Q n : ℝ) - S) ^ 2 ≤ X * S + 2 * S * Q.card := by
    rw [hexp]
    have h1 := sum_omega_sq_le Q hQ X
    have h2 := sum_omega_ge Q hQ X
    rw [← hSdef] at h1 h2
    nlinarith [hS.le, h1, h2]
  have hkey : (A.card : ℝ) * (S / 2) ^ 2 ≤ X * S + 2 * S * Q.card := by linarith
  have hexpand : 4 * (X : ℝ) / S + 8 * (Q.card : ℝ) / S = (4 * X + 8 * Q.card) / S := by
    rw [← add_div]
  rw [hexpand, le_div_iff₀ hS]
  have h5 : ((A.card : ℝ) * S / 4) * S ≤ ((X : ℝ) + 2 * Q.card) * S := by nlinarith [hkey]
  have h6 : (A.card : ℝ) * S / 4 ≤ (X : ℝ) + 2 * Q.card := le_of_mul_le_mul_right h5 hS
  linarith

/-! ### Integers with few divisors are sparse -/

theorem densityZero_card_divisors_le (T : ℕ) :
    DensityZero {n : ℕ | (Nat.divisors n).card ≤ T} := by
  rw [densityZero_iff]
  intro ε hε
  obtain ⟨Q, hQ, hQsum⟩ := exists_finset_primes_sum_gt (max (2 * (T : ℝ) + 2) (8 / ε))
  set S : ℝ := ∑ p ∈ Q, (1 : ℝ) / p with hSdef
  have hT : 2 * (T : ℝ) + 2 < S := lt_of_le_of_lt (le_max_left _ _) hQsum
  have hEps : 8 / ε < S := lt_of_le_of_lt (le_max_right _ _) hQsum
  have hTnn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hSpos : 0 < S := by linarith
  have h8 : 8 ≤ ε * S := by
    have h := (div_lt_iff₀ hε).mp hEps
    linarith
  refine Filter.eventually_atTop.2 ⟨⌈16 * (Q.card : ℝ) / (ε * S)⌉₊, fun X hX => ?_⟩
  have hXR : 16 * (Q.card : ℝ) / (ε * S) ≤ (X : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hX)
  have hεS : (0 : ℝ) < ε * S := by positivity
  have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hQtail : 8 * (Q.card : ℝ) / S ≤ ε / 2 * X := by
    rw [div_le_iff₀ hSpos]
    have h := (div_le_iff₀ hεS).mp hXR
    linarith
  have hmain : 4 * (X : ℝ) / S ≤ ε / 2 * X := by
    rw [div_le_iff₀ hSpos]
    nlinarith [mul_nonneg hXnn (by linarith : (0 : ℝ) ≤ ε * S - 8)]
  have hcount := card_omega_le_half Q hQ X hSpos
  rw [← hSdef] at hcount
  refine le_trans (le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) hcount) ?_
  · intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    obtain ⟨hn1, hn2⟩ := hn
    have hn2' : (Nat.divisors n).card ≤ T := hn2
    refine ⟨hn1, ?_⟩
    have hn0 : n ≠ 0 := by
      have h := (Finset.mem_Icc.mp hn1).1
      omega
    have h1 : 2 ^ omega Q n ≤ (Nat.divisors n).card := two_pow_le_card_divisors hn0 Q hQ
    have h2 : omega Q n < 2 ^ omega Q n := Nat.lt_two_pow_self
    have h3 : omega Q n ≤ T := by omega
    have h4 : (omega Q n : ℝ) ≤ (T : ℝ) := by exact_mod_cast h3
    linarith
  · linarith

end Erdos673
