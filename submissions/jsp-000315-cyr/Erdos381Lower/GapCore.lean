import Erdos381Lower.Blocks
import Erdos381Lower.Trial
import Erdos381Lower.Dirichlet

/-!
# Erdős #381, lower bound: the core of the gap construction (§3.4–§3.7)

This module carries out the part of Erdős's gap argument that does not mention highly
composite structure theory: given the four prime blocks of §3.3 attached to `n` (packaged as
`FourBlocks n p q s t εp εq`), it builds the two trial numbers of §3.4

  `n₁ = n · (∏ P_i) / (∏ q'_i)`,   `n₂ = n · (∏ Q_i) / (∏ p'_i)`,

proves the two divisor-count identities

  `τ(n₁) · ∏ (κᵢ + 1) = τ(n) · ∏ κᵢ · 2 ^ t`,   `τ(n₂) · 2 ^ (t + s) = τ(n) · 3 ^ s`
  (`κᵢ := vₚ n` at the `i`-th prime just below `q`, so `κᵢ ≥ 2`),

deduces the **dichotomy of §3.6** — at least one of `τ(n₁)`, `τ(n₂)` is *strictly* larger than
`τ(n)` — and records the **size estimate of §3.5** in the logarithmic form

  `|log nᵢ − log n| ≤ t·εp + s·εq + |t·log p − s·log q|`.

The `≥`/`>` gap in Erdős's paper (digest §3.6, risk 6) is repaired here: assuming both trial
numbers fail forces `3 ^ s = 2 ^ (t + s)`, impossible by parity since `s ≥ 1`.

Finally §3.7 (Lemma C1) turns a trial number with more divisors into an honest highly composite
number in `(n, nᵢ]`, and `exists_highlyComposite_lt_of_fourBlocks` packages everything into the
statement consumed by `Gap.lean`.
-/

namespace Erdos381Lower

open Erdos381 Filter

/-! ### Elementary analytic helpers -/

/-- On `[0, 1/2]` the exponential is dominated by `1 + 2x`; this converts the logarithmic size
estimate of §3.5 into the multiplicative bound `nᵢ ≤ n(1 + 2E)`. -/
theorem exp_le_one_add_two_mul {E : ℝ} (h0 : 0 ≤ E) (h1 : E ≤ 1 / 2) :
    Real.exp E ≤ 1 + 2 * E := by
  have hpos : (0 : ℝ) < Real.exp E := Real.exp_pos E
  have hkey : 1 - E ≤ (Real.exp E)⁻¹ := by
    have h := Real.add_one_le_exp (-E)
    rw [Real.exp_neg] at h
    linarith
  have h2 : (1 - E) * Real.exp E ≤ 1 := by
    have h3 := mul_le_mul_of_nonneg_right hkey hpos.le
    rwa [inv_mul_cancel₀ hpos.ne'] at h3
  nlinarith

/-- From `|log m − log n| ≤ E` with `E ≤ 1/2` and `2E < D` one gets `m < n + n·D`. -/
theorem lt_add_mul_of_abs_log_sub_le {m n : ℕ} {E D : ℝ} (hn : 0 < n) (hm : 0 < m)
    (h : |Real.log m - Real.log n| ≤ E) (hE0 : 0 ≤ E) (hE : E ≤ 1 / 2) (hED : 2 * E < D) :
    (m : ℝ) < n + n * D := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h1 : (m : ℝ) ≤ (n : ℝ) * Real.exp E := le_mul_exp_of_abs_log_sub_le hnR hmR h
  have h2 : Real.exp E ≤ 1 + 2 * E := exp_le_one_add_two_mul hE0 hE
  nlinarith

/-- A block of `m` numbers each within logarithmic distance `ε` of `x` has log-sum within
`m·ε` of `m·log x`. -/
theorem abs_sum_log_sub_le {m : ℕ} {f : Fin m → ℕ} {x ε : ℝ}
    (h : ∀ i, |Real.log (f i) - Real.log x| ≤ ε) :
    |(∑ i : Fin m, Real.log (f i)) - (m : ℝ) * Real.log x| ≤ (m : ℝ) * ε := by
  have key : (∑ i : Fin m, Real.log (f i)) - (m : ℝ) * Real.log x
      = ∑ i : Fin m, (Real.log (f i) - Real.log x) := by
    rw [Finset.sum_sub_distrib]
    simp [Finset.card_univ]
  rw [key]
  calc |∑ i : Fin m, (Real.log (f i) - Real.log x)|
      ≤ ∑ i : Fin m, |Real.log (f i) - Real.log x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, ε := Finset.sum_le_sum fun i _ ↦ h i
    _ = (m : ℝ) * ε := by simp [Finset.card_univ, mul_comm]

/-! ### From a good trial number to the next highly composite number (§3.7) -/

/-- **Lemma C1 (§3.7).**  If `n` is highly composite, `m > n` and `τ(m) > τ(n)`, then there is a
highly composite number in the interval `(n, m]`: the least `k > n` with `τ(k) > τ(n)` is a
strict record for `τ`. -/
theorem exists_highlyComposite_mem_Ioc {n m : ℕ} (hn : HighlyComposite n) (hnm : n < m)
    (htau : tau n < tau m) :
    ∃ n' : ℕ, HighlyComposite n' ∧ n < n' ∧ n' ≤ m := by
  have hex : ∃ k : ℕ, n < k ∧ tau n < tau k := ⟨m, hnm, htau⟩
  refine ⟨Nat.find hex, ⟨?_, ?_⟩, (Nat.find_spec hex).1, Nat.find_min' hex ⟨hnm, htau⟩⟩
  · exact lt_of_le_of_lt (Nat.zero_le n) (Nat.find_spec hex).1
  · intro j hj hjfind
    rcases Nat.lt_or_ge n j with hnj | hjn
    · have hmin : tau j ≤ tau n :=
        not_lt.1 (not_and.1 (Nat.find_min hex hjfind) hnj)
      exact lt_of_le_of_lt hmin (Nat.find_spec hex).2
    · rcases eq_or_lt_of_le hjn with rfl | hlt
      · exact (Nat.find_spec hex).2
      · exact lt_trans (hn.2 j hj hlt) (Nat.find_spec hex).2

/-! ### The two trial numbers of §3.4 -/

namespace FourBlocks

variable {n p q s t : ℕ} {εp εq : ℝ} (FB : FourBlocks n p q s t εp εq)

/-- The `t` primes just above `p`, as a finset. -/
def upP : Finset ℕ := Finset.image FB.P Finset.univ

/-- The `s` primes just below `q`, as a finset. -/
def dnq : Finset ℕ := Finset.image FB.q' Finset.univ

/-- The `s` primes just above `q`, as a finset. -/
def upQ : Finset ℕ := Finset.image FB.Q Finset.univ

/-- The `t` primes just below `p`, as a finset. -/
def dnp : Finset ℕ := Finset.image FB.p' Finset.univ

/-- The first trial number `n₁ = n · V / u` of §3.4. -/
def trialOne : ℕ := trial n FB.upP FB.dnq

/-- The second trial number `n₂ = n · U / v` of §3.4. -/
def trialTwo : ℕ := trial n FB.upQ FB.dnp

/-- Products over the block above `p` are products over `Fin t`. -/
theorem prod_upP (g : ℕ → ℕ) : ∏ r ∈ FB.upP, g r = ∏ i : Fin t, g (FB.P i) :=
  Finset.prod_image fun _ _ _ _ h ↦ FB.P_injective h

/-- Products over the block below `q` are products over `Fin s`. -/
theorem prod_dnq (g : ℕ → ℕ) : ∏ r ∈ FB.dnq, g r = ∏ i : Fin s, g (FB.q' i) :=
  Finset.prod_image fun _ _ _ _ h ↦ FB.q'_injective h

/-- Products over the block above `q` are products over `Fin s`. -/
theorem prod_upQ (g : ℕ → ℕ) : ∏ r ∈ FB.upQ, g r = ∏ i : Fin s, g (FB.Q i) :=
  Finset.prod_image fun _ _ _ _ h ↦ FB.Q_injective h

/-- Products over the block below `p` are products over `Fin t`. -/
theorem prod_dnp (g : ℕ → ℕ) : ∏ r ∈ FB.dnp, g r = ∏ i : Fin t, g (FB.p' i) :=
  Finset.prod_image fun _ _ _ _ h ↦ FB.p'_injective h

/-- Real sums over the block above `p` are sums over `Fin t`. -/
theorem sum_upP (g : ℕ → ℝ) : ∑ r ∈ FB.upP, g r = ∑ i : Fin t, g (FB.P i) :=
  Finset.sum_image fun _ _ _ _ h ↦ FB.P_injective h

/-- Real sums over the block below `q` are sums over `Fin s`. -/
theorem sum_dnq (g : ℕ → ℝ) : ∑ r ∈ FB.dnq, g r = ∑ i : Fin s, g (FB.q' i) :=
  Finset.sum_image fun _ _ _ _ h ↦ FB.q'_injective h

/-- Real sums over the block above `q` are sums over `Fin s`. -/
theorem sum_upQ (g : ℕ → ℝ) : ∑ r ∈ FB.upQ, g r = ∑ i : Fin s, g (FB.Q i) :=
  Finset.sum_image fun _ _ _ _ h ↦ FB.Q_injective h

/-- Real sums over the block below `p` are sums over `Fin t`. -/
theorem sum_dnp (g : ℕ → ℝ) : ∑ r ∈ FB.dnp, g r = ∑ i : Fin t, g (FB.p' i) :=
  Finset.sum_image fun _ _ _ _ h ↦ FB.p'_injective h

/-- The block above `p` consists of primes. -/
theorem upP_prime : ∀ r ∈ FB.upP, r.Prime := by
  intro r hr
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hr
  exact FB.P_prime i

/-- The block below `q` consists of primes. -/
theorem dnq_prime : ∀ r ∈ FB.dnq, r.Prime := by
  intro r hr
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hr
  exact FB.q'_prime i

/-- The block above `q` consists of primes. -/
theorem upQ_prime : ∀ r ∈ FB.upQ, r.Prime := by
  intro r hr
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hr
  exact FB.Q_prime i

/-- The block below `p` consists of primes. -/
theorem dnp_prime : ∀ r ∈ FB.dnp, r.Prime := by
  intro r hr
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hr
  exact FB.p'_prime i

/-- Every prime just below `q` divides `n`. -/
theorem dnq_one_le : ∀ r ∈ FB.dnq, 1 ≤ n.factorization r := by
  intro r hr
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hr
  exact le_trans (by norm_num) (FB.q'_factorization i)

/-- Every prime just below `p` divides `n`. -/
theorem dnp_one_le : ∀ r ∈ FB.dnp, 1 ≤ n.factorization r := by
  intro r hr
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hr
  exact le_of_eq (FB.p'_factorization i).symm

/-- The primes above `p` and the primes below `q` are distinct. -/
theorem disjoint_upP_dnq (hqp : q < p) : Disjoint FB.upP FB.dnq := by
  refine Finset.disjoint_left.2 fun r hr hr' ↦ ?_
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hr
  obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hr'
  have h1 : p < FB.P i := FB.lt_P i
  have h2 : FB.q' j < q := FB.q'_lt j
  omega

/-- The primes above `q` and the primes below `p` are distinct. -/
theorem disjoint_upQ_dnp : Disjoint FB.upQ FB.dnp := by
  refine Finset.disjoint_left.2 fun r hr hr' ↦ ?_
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hr
  obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hr'
  have h := FB.Q_lt_p' i j
  omega

/-- The first trial number is positive. -/
theorem trialOne_pos (hn : 0 < n) : 0 < FB.trialOne :=
  trial_pos hn FB.upP_prime FB.dnq_prime FB.dnq_one_le

/-- The second trial number is positive. -/
theorem trialTwo_pos (hn : 0 < n) : 0 < FB.trialTwo :=
  trial_pos hn FB.upQ_prime FB.dnp_prime FB.dnp_one_le

/-- **The `τ`-identity for `n₁` (§3.4).**  Raising the `t` primes just above `p` from exponent
`0` to `1` multiplies `τ` by `2 ^ t`; lowering the `s` primes just below `q` from `κᵢ` to
`κᵢ − 1` multiplies it by `∏ κᵢ / (κᵢ + 1)`. -/
theorem tau_trialOne_mul (hn : 0 < n) (hqp : q < p) :
    tau FB.trialOne * ∏ i : Fin s, (n.factorization (FB.q' i) + 1) =
      tau n * (∏ i : Fin s, n.factorization (FB.q' i)) * 2 ^ t := by
  have h := tau_trial_mul hn FB.upP_prime FB.dnq_prime (FB.disjoint_upP_dnq hqp) FB.dnq_one_le
  have e1 : (∏ r ∈ FB.upP, (n.factorization r + 1)) = 1 := by
    rw [FB.prod_upP fun r ↦ n.factorization r + 1]
    exact Finset.prod_eq_one fun i _ ↦ by simp [FB.P_factorization i]
  have e2 : (∏ r ∈ FB.upP, (n.factorization r + 2)) = 2 ^ t := by
    rw [FB.prod_upP fun r ↦ n.factorization r + 2]
    simp [FB.P_factorization]
  rw [e1, e2, FB.prod_dnq fun r ↦ n.factorization r + 1,
    FB.prod_dnq fun r ↦ n.factorization r, mul_one] at h
  exact h

/-- **The `τ`-identity for `n₂` (§3.4).**  The `s` primes just above `q` go from exponent `1`
to `2` (factor `(3/2) ^ s`) and the `t` primes just below `p` from `1` to `0`
(factor `(1/2) ^ t`). -/
theorem tau_trialTwo_mul (hn : 0 < n) :
    tau FB.trialTwo * 2 ^ (t + s) = tau n * 3 ^ s := by
  have h := tau_trial_mul hn FB.upQ_prime FB.dnp_prime FB.disjoint_upQ_dnp FB.dnp_one_le
  have e1 : (∏ r ∈ FB.dnp, (n.factorization r + 1)) = 2 ^ t := by
    rw [FB.prod_dnp fun r ↦ n.factorization r + 1]
    simp [FB.p'_factorization]
  have e2 : (∏ r ∈ FB.dnp, n.factorization r) = 1 := by
    rw [FB.prod_dnp fun r ↦ n.factorization r]
    exact Finset.prod_eq_one fun i _ ↦ FB.p'_factorization i
  have e3 : (∏ r ∈ FB.upQ, (n.factorization r + 1)) = 2 ^ s := by
    rw [FB.prod_upQ fun r ↦ n.factorization r + 1]
    simp [FB.Q_factorization]
  have e4 : (∏ r ∈ FB.upQ, (n.factorization r + 2)) = 3 ^ s := by
    rw [FB.prod_upQ fun r ↦ n.factorization r + 2]
    simp [FB.Q_factorization]
  rw [e1, e2, e3, e4, mul_one] at h
  rw [pow_add, ← mul_assoc]
  exact h

/-- **The dichotomy of §3.6, with Erdős's `≥` repaired.**  At least one trial number has
strictly more divisors than `n`.  If both failed, the two `τ`-identities and `3κ ≥ 2(κ + 1)`
(valid since every `κᵢ ≥ 2`) would force `3 ^ s = 2 ^ (t + s)`, impossible by parity for
`s ≥ 1`. -/
theorem lt_tau_trialOne_or_trialTwo (hn : 0 < n) (hqp : q < p) (hs : 0 < s) :
    tau n < tau FB.trialOne ∨ tau n < tau FB.trialTwo := by
  rcases Nat.lt_or_ge (tau n) (tau FB.trialOne) with hgood | h1
  · exact Or.inl hgood
  rcases Nat.lt_or_ge (tau n) (tau FB.trialTwo) with hgood | h2
  · exact Or.inr hgood
  exfalso
  have hκ : ∀ i : Fin s, 2 ≤ n.factorization (FB.q' i) := FB.q'_factorization
  set K0 : ℕ := ∏ i : Fin s, n.factorization (FB.q' i) with hK0
  set K1 : ℕ := ∏ i : Fin s, (n.factorization (FB.q' i) + 1) with hK1
  have hK0pos : 0 < K0 := Finset.prod_pos fun i _ ↦ by have := hκ i; omega
  have htaun : 0 < tau n := Erdos381.tau_pos hn.ne'
  have id1 := FB.tau_trialOne_mul hn hqp
  rw [← hK0, ← hK1] at id1
  have id2 := FB.tau_trialTwo_mul hn
  have step1 : K0 * 2 ^ t ≤ K1 := by
    refine Nat.le_of_mul_le_mul_left ?_ htaun
    calc tau n * (K0 * 2 ^ t) = tau FB.trialOne * K1 := by rw [id1]; ring
      _ ≤ tau n * K1 := Nat.mul_le_mul_right _ h1
  have step2 : 3 ^ s ≤ 2 ^ (t + s) := by
    refine Nat.le_of_mul_le_mul_left ?_ htaun
    calc tau n * 3 ^ s = tau FB.trialTwo * 2 ^ (t + s) := id2.symm
      _ ≤ tau n * 2 ^ (t + s) := Nat.mul_le_mul_right _ h2
  have step3 : 2 ^ s * K1 ≤ 3 ^ s * K0 := by
    have hprod : ∏ i : Fin s, (2 * (n.factorization (FB.q' i) + 1)) ≤
        ∏ i : Fin s, (3 * n.factorization (FB.q' i)) := by
      refine Finset.prod_le_prod' fun i _ ↦ ?_
      have := hκ i
      omega
    simpa [Finset.prod_mul_distrib, hK0, hK1] using hprod
  have key : 3 ^ s * K0 = 2 ^ (t + s) * K0 := by
    refine le_antisymm (Nat.mul_le_mul_right _ step2) ?_
    calc 2 ^ (t + s) * K0 = 2 ^ s * (K0 * 2 ^ t) := by rw [pow_add]; ring
      _ ≤ 2 ^ s * K1 := Nat.mul_le_mul_left _ step1
      _ ≤ 3 ^ s * K0 := step3
  have h3s : (3 : ℕ) ^ s = 2 ^ (t + s) := Nat.eq_of_mul_eq_mul_right hK0pos key
  have hdvd : (2 : ℕ) ∣ 3 ^ s := by
    rw [h3s]
    exact dvd_pow_self 2 (by omega)
  have h23 : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
  norm_num at h23

/-- **The size estimate of §3.5 for `n₁`.**  The logarithm moves by the Dirichlet defect
`|t·log p − s·log q|` plus the block errors `t·εp` and `s·εq`. -/
theorem abs_log_trialOne_sub (hn : 0 < n) :
    |Real.log FB.trialOne - Real.log n| ≤
      (t : ℝ) * εp + (s : ℝ) * εq + |(t : ℝ) * Real.log p - (s : ℝ) * Real.log q| := by
  have hlog := log_trial hn FB.upP_prime FB.dnq_prime FB.dnq_one_le
  rw [FB.sum_upP fun r ↦ Real.log r, FB.sum_dnq fun r ↦ Real.log r] at hlog
  have hP := abs_le.1 (abs_sum_log_sub_le (x := (p : ℝ)) (ε := εp) FB.P_log_error)
  have hq := abs_le.1 (abs_sum_log_sub_le (x := (q : ℝ)) (ε := εq) FB.q'_log_error)
  have hd1 := neg_abs_le ((t : ℝ) * Real.log p - (s : ℝ) * Real.log q)
  have hd2 := le_abs_self ((t : ℝ) * Real.log p - (s : ℝ) * Real.log q)
  have hsplit : Real.log FB.trialOne - Real.log n =
      ((∑ i : Fin t, Real.log (FB.P i)) - (t : ℝ) * Real.log p) -
        ((∑ i : Fin s, Real.log (FB.q' i)) - (s : ℝ) * Real.log q) +
        ((t : ℝ) * Real.log p - (s : ℝ) * Real.log q) := by
    rw [show Real.log (FB.trialOne : ℕ) = Real.log (trial n FB.upP FB.dnq) from rfl, hlog]
    ring
  rw [hsplit, abs_le]
  constructor <;> linarith [hP.1, hP.2, hq.1, hq.2]

/-- **The size estimate of §3.5 for `n₂`.** -/
theorem abs_log_trialTwo_sub (hn : 0 < n) :
    |Real.log FB.trialTwo - Real.log n| ≤
      (t : ℝ) * εp + (s : ℝ) * εq + |(t : ℝ) * Real.log p - (s : ℝ) * Real.log q| := by
  have hlog := log_trial hn FB.upQ_prime FB.dnp_prime FB.dnp_one_le
  rw [FB.sum_upQ fun r ↦ Real.log r, FB.sum_dnp fun r ↦ Real.log r] at hlog
  have hQ := abs_le.1 (abs_sum_log_sub_le (x := (q : ℝ)) (ε := εq) FB.Q_log_error)
  have hp := abs_le.1 (abs_sum_log_sub_le (x := (p : ℝ)) (ε := εp) FB.p'_log_error)
  have hd1 := neg_abs_le ((t : ℝ) * Real.log p - (s : ℝ) * Real.log q)
  have hd2 := le_abs_self ((t : ℝ) * Real.log p - (s : ℝ) * Real.log q)
  have hsplit : Real.log FB.trialTwo - Real.log n =
      ((∑ i : Fin s, Real.log (FB.Q i)) - (s : ℝ) * Real.log q) -
        ((∑ i : Fin t, Real.log (FB.p' i)) - (t : ℝ) * Real.log p) -
        ((t : ℝ) * Real.log p - (s : ℝ) * Real.log q) := by
    rw [show Real.log (FB.trialTwo : ℕ) = Real.log (trial n FB.upQ FB.dnp) from rfl, hlog]
    ring
  rw [hsplit, abs_le]
  constructor <;> linarith [hQ.1, hQ.2, hp.1, hp.2]

end FourBlocks

/-- **The core of the gap theorem (§3.4–§3.7).**  From the four blocks of §3.3, the Dirichlet
defect bound `D` and the smallness of the total error, one of the two trial numbers exceeds `n`
with strictly more divisors, and Lemma C1 produces a highly composite number in the resulting
short interval above `n`. -/
theorem exists_highlyComposite_lt_of_fourBlocks {n p q s t : ℕ} {εp εq D c : ℝ}
    (hn : HighlyComposite n) (FB : FourBlocks n p q s t εp εq) (hqp : q < p) (hs : 0 < s)
    (hεp : 0 ≤ εp) (hεq : 0 ≤ εq)
    (hD : |(t : ℝ) * Real.log p - (s : ℝ) * Real.log q| ≤ D)
    (hhalf : (t : ℝ) * εp + (s : ℝ) * εq + D ≤ 1 / 2)
    (hlt : 2 * ((t : ℝ) * εp + (s : ℝ) * εq + D) < Real.log n ^ (-c)) :
    ∃ n' : ℕ, HighlyComposite n' ∧ n < n' ∧ (n' : ℝ) < n + n * Real.log n ^ (-c) := by
  set E : ℝ := (t : ℝ) * εp + (s : ℝ) * εq + D with hE
  have hE0 : 0 ≤ E := by
    have h0 : (0 : ℝ) ≤ |(t : ℝ) * Real.log p - (s : ℝ) * Real.log q| := abs_nonneg _
    have h1 : (0 : ℝ) ≤ (t : ℝ) * εp := mul_nonneg (Nat.cast_nonneg _) hεp
    have h2 : (0 : ℝ) ≤ (s : ℝ) * εq := mul_nonneg (Nat.cast_nonneg _) hεq
    have : (0 : ℝ) ≤ D := le_trans h0 hD
    simp only [hE]
    linarith
  have main : ∀ m : ℕ, 0 < m → tau n < tau m → |Real.log m - Real.log n| ≤ E →
      ∃ n' : ℕ, HighlyComposite n' ∧ n < n' ∧ (n' : ℝ) < n + n * Real.log n ^ (-c) := by
    intro m hm htau habs
    have hnm : n < m := by
      rcases lt_trichotomy m n with h | h | h
      · exact absurd (hn.2 m hm h) (not_lt.2 htau.le)
      · exact absurd htau (by rw [h]; exact lt_irrefl _)
      · exact h
    obtain ⟨n', hn'HC, hn'1, hn'2⟩ := exists_highlyComposite_mem_Ioc hn hnm htau
    refine ⟨n', hn'HC, hn'1, lt_of_le_of_lt (b := (m : ℝ)) ?_ ?_⟩
    · exact_mod_cast hn'2
    · exact lt_add_mul_of_abs_log_sub_le hn.1 hm habs hE0 (by linarith) hlt
  rcases FB.lt_tau_trialOne_or_trialTwo hn.1 hqp hs with h | h
  · exact main _ (FB.trialOne_pos hn.1) h
      (le_trans (FB.abs_log_trialOne_sub hn.1) (by simp only [hE]; linarith))
  · exact main _ (FB.trialTwo_pos hn.1) h
      (le_trans (FB.abs_log_trialTwo_sub hn.1) (by simp only [hE]; linarith))

end Erdos381Lower
