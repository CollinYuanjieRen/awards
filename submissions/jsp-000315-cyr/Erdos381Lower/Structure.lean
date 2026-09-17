import Erdos381Lower.Defs
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev

/-!
# Quantitative structure of a large highly composite number

This file formalizes Erdős's Lemmas 1, 2 and 3 from *On highly composite and similar numbers*
(1944) for a general highly composite number `n`, with `P = largestPrimeFactor n`:

* `pow_factorization_lt_pow_six` — `q ^ v_q(n) < P ^ 6` for every prime `q ≤ P` (Lemma 1a);
* `eventually_log_lt_and_lt_log` — `log n / 18 < P ≤ 3 log n` eventually (Lemma 1);
* `eventually_factorization_eq_one_of_half_lt` — `v_q(n) = 1` for `P/2 < q ≤ P` (Lemma 2′);
* `factorization_largest_eq_one` — `v_P(n) = 1` (Corollary 2″);
* `eventually_two_le_factorization_of_lt_four_sqrt` — `v_q(n) ≥ 2` for `q < 4√P` (Lemma 3(ii)).

Every proof is a *trial number* comparison: the exponent vector of `n` is modified on a finite
set of primes so that the resulting integer is smaller while its divisor count is larger,
contradicting the minimality built into `Erdos381.HighlyComposite`.  The auxiliary primes are
produced by iterating Bertrand's postulate, upwards and downwards.
-/

namespace Erdos381Lower

open Filter Finset

open scoped Nat

section Basic

/-- The largest prime factor of `n > 1` is prime. -/
theorem largestPrimeFactor_prime {n : ℕ} (hn : 1 < n) : (largestPrimeFactor n).Prime := by
  have h : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
  rw [largestPrimeFactor, dif_pos h]
  exact Nat.prime_of_mem_primeFactors (Finset.max'_mem _ h)

/-- The largest prime factor of `n > 1` divides `n`. -/
theorem largestPrimeFactor_dvd {n : ℕ} (hn : 1 < n) : largestPrimeFactor n ∣ n := by
  have h : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
  rw [largestPrimeFactor, dif_pos h]
  exact Nat.dvd_of_mem_primeFactors (Finset.max'_mem _ h)

/-- Every prime factor of `n` is at most the largest prime factor. -/
theorem le_largestPrimeFactor {n q : ℕ} (hn : n ≠ 0) (hq : q.Prime) (hqn : q ∣ n) :
    q ≤ largestPrimeFactor n := by
  have hmem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, hn⟩
  have h : n.primeFactors.Nonempty := ⟨q, hmem⟩
  rw [largestPrimeFactor, dif_pos h]
  exact Finset.le_max' _ q hmem

/-- A number with a positive largest prime factor is greater than one. -/
theorem one_lt_of_largestPrimeFactor_pos {n : ℕ} (h : 0 < largestPrimeFactor n) : 1 < n := by
  by_contra hcon
  have hne : ¬ n.primeFactors.Nonempty := fun hx ↦
    hcon (Nat.nonempty_primeFactors.mp hx)
  rw [largestPrimeFactor, dif_neg hne] at h
  exact absurd h (lt_irrefl 0)

/-- Primes above the largest prime factor do not occur in the factorization. -/
theorem factorization_eq_zero_of_largestPrimeFactor_lt {n q : ℕ} (hn : n ≠ 0) (hq : q.Prime)
    (hlt : largestPrimeFactor n < q) : n.factorization q = 0 := by
  by_contra hcon
  exact absurd (le_largestPrimeFactor hn hq (Nat.dvd_of_factorization_pos hcon))
    (not_le.mpr hlt)

/-- For a highly composite number the primes `≤ P` are exactly the prime divisors: this is the
"initial segment" half of Erdős's unnumbered Lemma 0, in the form used below. -/
theorem prime_dvd_of_le_largest {n q : ℕ} (hn : Erdos381.HighlyComposite n) (hq : q.Prime)
    (hqP : q ≤ largestPrimeFactor n) : q ∣ n := by
  have hPpos : 0 < largestPrimeFactor n := lt_of_lt_of_le hq.pos hqP
  have hn1 : 1 < n := one_lt_of_largestPrimeFactor_pos hPpos
  have hP : (largestPrimeFactor n).Prime := largestPrimeFactor_prime hn1
  rcases eq_or_lt_of_le hqP with h | h
  · exact h ▸ largestPrimeFactor_dvd hn1
  · exact Erdos381.prime_dvd_of_lt_prime_dvd hn hq hP h (largestPrimeFactor_dvd hn1)

/-- Every prime `≤ P` has exponent at least one in a highly composite number. -/
theorem one_le_factorization_of_le_largest {n q : ℕ} (hn : Erdos381.HighlyComposite n)
    (hq : q.Prime) (hqP : q ≤ largestPrimeFactor n) : 1 ≤ n.factorization q :=
  hq.factorization_pos_of_dvd hn.1.ne' (prime_dvd_of_le_largest hn hq hqP)

end Basic

section Trial

/-- **The trial-number engine.**  Modify the exponent vector of a highly composite number `n`
on a finite set `T` of primes.  If the product of the modified prime powers drops while the
product of the modified local divisor counts rises, minimality of `n` is contradicted.  Every
quantitative lemma below is an instance of this. -/
private theorem no_smaller_trial {n : ℕ} (hn : Erdos381.HighlyComposite n) {T : Finset ℕ}
    (hT : ∀ r ∈ T, r.Prime) (g : ℕ → ℕ)
    (hsize : ∏ r ∈ T, r ^ g r < ∏ r ∈ T, r ^ n.factorization r)
    (htau : ∏ r ∈ T, (n.factorization r + 1) < ∏ r ∈ T, (g r + 1)) : False := by
  classical
  set S : Finset ℕ := n.primeFactors ∪ T with hSdef
  have hTS : T ⊆ S := Finset.subset_union_right
  have hPS : n.primeFactors ⊆ S := Finset.subset_union_left
  have hSprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact hT p h
  set G : ℕ → ℕ := fun p ↦ if p ∈ T then g p else n.factorization p with hGdef
  have hGmem : ∀ a, G a ≠ 0 → a ∈ S := by
    intro a ha
    by_cases h : a ∈ T
    · exact hTS h
    · simp only [hGdef, if_neg h] at ha
      refine hPS ?_
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr ha
  set F : ℕ →₀ ℕ := Finsupp.onFinset S G hGmem with hFdef
  have hFsupp : F.support ⊆ S := Finsupp.support_onFinset_subset
  have hFprime : ∀ p ∈ F.support, p.Prime := fun p hp ↦ hSprime p (hFsupp hp)
  have hFapply : ∀ p, F p = G p := fun p ↦ rfl
  set m : ℕ := Erdos381.fromFactorization F with hmdef
  have hmpos : 0 < m := Erdos381.fromFactorization_pos hFprime
  have hmval : m = ∏ p ∈ S, p ^ G p := by
    rw [hmdef, Erdos381.fromFactorization,
      Finsupp.prod_of_support_subset F hFsupp _ (by simp)]
    exact Finset.prod_congr rfl fun p _ ↦ by rw [hFapply]
  have htaum : Erdos381.tau m = ∏ p ∈ S, (G p + 1) := by
    rw [hmdef, Erdos381.tau_fromFactorization hFprime, Erdos381.divisorProduct,
      Finsupp.prod_of_support_subset F hFsupp _ (by simp)]
    exact Finset.prod_congr rfl fun p _ ↦ by rw [hFapply]
  have hsuppn : n.factorization.support ⊆ S := by
    rw [Nat.support_factorization]; exact hPS
  have hnval : n = ∏ p ∈ S, p ^ n.factorization p := by
    conv_lhs => rw [← Erdos381.fromFactorization_factorization hn.1.ne']
    rw [Erdos381.fromFactorization,
      Finsupp.prod_of_support_subset n.factorization hsuppn _ (by simp)]
  have htaun : Erdos381.tau n = ∏ p ∈ S, (n.factorization p + 1) := by
    rw [Erdos381.tau_eq_divisorProduct_factorization hn.1.ne', Erdos381.divisorProduct,
      Finsupp.prod_of_support_subset n.factorization hsuppn _ (by simp)]
  have hoff : ∀ p ∈ S \ T, G p = n.factorization p := by
    intro p hp
    simp only [hGdef, if_neg (Finset.mem_sdiff.mp hp).2]
  have hCpos : 0 < ∏ p ∈ S \ T, p ^ n.factorization p :=
    Finset.prod_pos fun p hp ↦ pow_pos (hSprime p (Finset.mem_sdiff.mp hp).1).pos _
  have hDpos : 0 < ∏ p ∈ S \ T, (n.factorization p + 1) :=
    Finset.prod_pos fun _ _ ↦ Nat.succ_pos _
  have hmlt : m < n := by
    rw [hmval, hnval, ← Finset.prod_sdiff (f := fun p ↦ p ^ G p) hTS,
      ← Finset.prod_sdiff (f := fun p ↦ p ^ n.factorization p) hTS]
    have h1 : (∏ p ∈ S \ T, p ^ G p) = ∏ p ∈ S \ T, p ^ n.factorization p :=
      Finset.prod_congr rfl fun p hp ↦ by rw [hoff p hp]
    have h2 : (∏ p ∈ T, p ^ G p) = ∏ p ∈ T, p ^ g p :=
      Finset.prod_congr rfl fun p hp ↦ by simp only [hGdef, if_pos hp]
    rw [h1, h2]
    exact mul_lt_mul_of_pos_left hsize hCpos
  have htault : Erdos381.tau n < Erdos381.tau m := by
    rw [htaum, htaun, ← Finset.prod_sdiff (f := fun p ↦ G p + 1) hTS,
      ← Finset.prod_sdiff (f := fun p ↦ n.factorization p + 1) hTS]
    have h1 : (∏ p ∈ S \ T, (G p + 1)) = ∏ p ∈ S \ T, (n.factorization p + 1) :=
      Finset.prod_congr rfl fun p hp ↦ by rw [hoff p hp]
    have h2 : (∏ p ∈ T, (G p + 1)) = ∏ p ∈ T, (g p + 1) :=
      Finset.prod_congr rfl fun p hp ↦ by simp only [hGdef, if_pos hp]
    rw [h1, h2]
    exact mul_lt_mul_of_pos_left htau hDpos
  exact absurd (hn.2 m hmpos hmlt) (not_lt.mpr htault.le)

end Trial

section LemmaOneA

/-- **Erdős's Lemma 1a.**  In a highly composite number every prime power `q ^ v_q(n)` with
`q ≤ P := largestPrimeFactor n` is smaller than `P ^ 6`.

The trial number is `n · P₁ / q ^ α`, where `α` is minimal with `q ^ α > 2 P` and `P₁` is a
prime in `(P, 2P]` supplied by Bertrand's postulate.  Only Bertrand is used; there is no
largeness hypothesis. -/
theorem pow_factorization_lt_pow_six {n q : ℕ} (hn : Erdos381.HighlyComposite n)
    (hq : q.Prime) (hqp : q ≤ largestPrimeFactor n) :
    q ^ n.factorization q < (largestPrimeFactor n) ^ 6 := by
  classical
  set P : ℕ := largestPrimeFactor n with hPdef
  have hPpos : 0 < P := lt_of_lt_of_le hq.pos hqp
  have hn1 : 1 < n := one_lt_of_largestPrimeFactor_pos hPpos
  have hP : P.Prime := largestPrimeFactor_prime hn1
  have hP2 : 2 ≤ P := hP.two_le
  by_contra hcon
  rw [not_lt] at hcon
  set κ : ℕ := n.factorization q with hκdef
  -- the minimal exponent `α` with `q ^ α > 2 P`
  have hex : ∃ j : ℕ, 2 * P < q ^ j := by
    refine ⟨2 * P, lt_of_lt_of_le Nat.lt_two_pow_self ?_⟩
    exact Nat.pow_le_pow_left hq.two_le _
  set α : ℕ := Nat.find hex with hαdef
  have hαspec : 2 * P < q ^ α := Nat.find_spec hex
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, pow_zero] at hαspec
    omega
  have hαprev : q ^ (α - 1) ≤ 2 * P := by
    have := Nat.find_min hex (m := α - 1) (by omega)
    omega
  have hαpow : q ^ α ≤ P ^ 3 := by
    have hsplit : q ^ α = q ^ (α - 1) * q := by
      rw [← pow_succ]
      congr 1
      omega
    calc q ^ α = q ^ (α - 1) * q := hsplit
      _ ≤ (2 * P) * P := Nat.mul_le_mul hαprev hqp
      _ ≤ P * P * P := by
          have : 2 * P ≤ P * P := Nat.mul_le_mul_right P hP2
          exact Nat.mul_le_mul_right P this
      _ = P ^ 3 := by ring
  have hκα : 2 * α ≤ κ := by
    have h1 : q ^ (2 * α) ≤ q ^ κ := by
      calc q ^ (2 * α) = (q ^ α) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
        _ ≤ (P ^ 3) ^ 2 := Nat.pow_le_pow_left hαpow 2
        _ = P ^ 6 := by ring
        _ ≤ q ^ κ := hcon
    exact (Nat.pow_le_pow_iff_right hq.one_lt).mp h1
  -- the Bertrand prime just above `P`
  obtain ⟨P₁, hP₁, hPP₁, hP₁le⟩ := Nat.exists_prime_lt_and_le_two_mul P hPpos.ne'
  have hqP₁ : q ≠ P₁ := by omega
  have hP₁fact : n.factorization P₁ = 0 :=
    factorization_eq_zero_of_largestPrimeFactor_lt hn.1.ne' hP₁ hPP₁
  refine no_smaller_trial hn (T := ({q, P₁} : Finset ℕ)) ?_ (fun r ↦ if r = q then κ - α else 1)
    ?_ ?_
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hq
    · exact hP₁
  · rw [Finset.prod_pair hqP₁, Finset.prod_pair hqP₁]
    simp only [if_true, if_neg (Ne.symm hqP₁), ← hκdef, hP₁fact, pow_zero,
      pow_one, mul_one]
    have hsplit : q ^ κ = q ^ (κ - α) * q ^ α := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    exact mul_lt_mul_of_pos_left (by omega) (pow_pos hq.pos (κ - α))
  · rw [Finset.prod_pair hqP₁, Finset.prod_pair hqP₁]
    simp only [if_true, if_neg (Ne.symm hqP₁), ← hκdef, hP₁fact]
    omega

end LemmaOneA

section BertrandChains

/-- The least prime strictly larger than `m`. -/
private noncomputable def nextPrime (m : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (m + 1))

private theorem nextPrime_prime (m : ℕ) : (nextPrime m).Prime :=
  (Nat.find_spec (Nat.exists_infinite_primes (m + 1))).2

private theorem lt_nextPrime (m : ℕ) : m < nextPrime m :=
  (Nat.find_spec (Nat.exists_infinite_primes (m + 1))).1

private theorem nextPrime_le_two_mul {m : ℕ} (hm : m ≠ 0) : nextPrime m ≤ 2 * m := by
  obtain ⟨p, hp, hmp, hple⟩ := Nat.exists_prime_lt_and_le_two_mul m hm
  exact le_trans (Nat.find_min' _ ⟨hmp, hp⟩) hple

private theorem div_lt_div_succ (a : ℕ) {b : ℕ} (hb : 0 < b) :
    (a : ℝ) / b < ((a / b : ℕ) : ℝ) + 1 := by
  have hbR : (0 : ℝ) < (b : ℕ) := by exact_mod_cast hb
  rw [div_lt_iff₀ hbR, mul_comm]
  exact_mod_cast Nat.lt_mul_div_succ a hb

/-- The ascending Bertrand chain started at `y`: `y`, then the least prime above it, and so on. -/
private noncomputable def ascChain (y : ℕ) : ℕ → ℕ
  | 0 => y
  | j + 1 => nextPrime (ascChain y j)

private theorem ascChain_prime {y : ℕ} (hy : y.Prime) : ∀ j : ℕ, (ascChain y j).Prime
  | 0 => hy
  | _ + 1 => nextPrime_prime _

private theorem le_ascChain {y : ℕ} : ∀ j : ℕ, y ≤ ascChain y j
  | 0 => le_rfl
  | j + 1 => le_trans (le_ascChain j) (lt_nextPrime _).le

private theorem ascChain_lt_succ (y : ℕ) (j : ℕ) : ascChain y j < ascChain y (j + 1) :=
  lt_nextPrime _

private theorem ascChain_le {y : ℕ} (hy : 2 ≤ y) : ∀ j : ℕ, ascChain y j ≤ y * 2 ^ j
  | 0 => by simp [ascChain]
  | j + 1 => by
      have hpos : ascChain y j ≠ 0 := by
        have := le_ascChain (y := y) j
        omega
      calc ascChain y (j + 1) = nextPrime (ascChain y j) := rfl
        _ ≤ 2 * ascChain y j := nextPrime_le_two_mul hpos
        _ ≤ 2 * (y * 2 ^ j) := by
            exact Nat.mul_le_mul_left 2 (ascChain_le hy j)
        _ = y * 2 ^ (j + 1) := by ring

/-- **Bertrand chain upwards.**  For a prime `y` there are `k` primes `y = f 0 < f 1 < … `
with `f i ≤ y · 2 ^ i`.  (The digest states the hypothesis as `2 ≤ y`; the conclusion forces
`f 0 = y`, so `y` must be prime.) -/
theorem exists_ascending_primes (k : ℕ) {y : ℕ} (hy : y.Prime) :
    ∃ f : Fin k → ℕ, StrictMono f ∧
      ∀ i : Fin k, (f i).Prime ∧ y ≤ f i ∧ (f i : ℝ) ≤ y * 2 ^ (i : ℕ) := by
  refine ⟨fun i ↦ ascChain y i.1, ?_, ?_⟩
  · intro i j hij
    exact strictMono_nat_of_lt_succ (ascChain_lt_succ y) hij
  · intro i
    refine ⟨ascChain_prime hy i.1, le_ascChain i.1, ?_⟩
    have := ascChain_le hy.two_le i.1
    exact_mod_cast this

/-- **Bertrand chain downwards.**  If `y ≥ 2 ^ (k + 5)` there are `k` primes
`f 0 > f 1 > … ` below `y` with `y / 2 ^ (i+1) < f i`. -/
theorem exists_descending_primes (k : ℕ) {y : ℕ} (hy : 2 ^ (k + 5) ≤ y) :
    ∃ f : Fin k → ℕ, StrictAnti f ∧
      ∀ i : Fin k, (f i).Prime ∧ f i < y ∧ (y : ℝ) / 2 ^ ((i : ℕ) + 1) < f i := by
  set g : ℕ → ℕ := fun j ↦ nextPrime (y / 2 ^ (j + 1)) with hgdef
  have hy32 : 32 ≤ y := by
    refine le_trans ?_ hy
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (k + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdivpos : ∀ j : ℕ, j < k → 0 < y / 2 ^ (j + 1) := by
    intro j hj
    refine Nat.div_pos (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hy)
      (pow_pos (by norm_num : (0:ℕ) < 2) _)
  have hupper : ∀ j : ℕ, j < k → g j ≤ y / 2 ^ j := by
    intro j hj
    have h1 : g j ≤ 2 * (y / 2 ^ (j + 1)) := nextPrime_le_two_mul (hdivpos j hj).ne'
    have h2 : y / 2 ^ (j + 1) = (y / 2 ^ j) / 2 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    omega
  have hlow : ∀ j : ℕ, y / 2 ^ (j + 1) < g j := fun j ↦ lt_nextPrime _
  refine ⟨fun i ↦ g i.1, ?_, ?_⟩
  · intro i j hij
    show g j.1 < g i.1
    have hji : (i : ℕ) + 1 ≤ (j : ℕ) := hij
    calc g j.1 ≤ y / 2 ^ (j : ℕ) := hupper j.1 j.2
      _ ≤ y / 2 ^ ((i : ℕ) + 1) :=
          Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hji)
            (pow_pos (by norm_num : (0:ℕ) < 2) _)
      _ < g i.1 := hlow i.1
  · intro i
    show (g i.1).Prime ∧ g i.1 < y ∧ (y : ℝ) / 2 ^ ((i : ℕ) + 1) < (g i.1 : ℝ)
    refine ⟨nextPrime_prime _, ?_, ?_⟩
    · have h1 : g i.1 ≤ 2 * (y / 2 ^ ((i : ℕ) + 1)) :=
        nextPrime_le_two_mul (hdivpos i.1 i.2).ne'
      have h2 : y / 2 ^ ((i : ℕ) + 1) ≤ y / 2 :=
        Nat.div_le_div_left (by
          calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ ((i : ℕ) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
          (by norm_num)
      by_cases hyp : y.Prime
      · have hyodd : y % 2 = 1 := by
          rcases hyp.eq_two_or_odd with h | h
          · omega
          · exact h
        omega
      · have hne : g i.1 ≠ y := fun h ↦ hyp (h ▸ nextPrime_prime _)
        omega
    · have hb : (0 : ℕ) < 2 ^ ((i : ℕ) + 1) := pow_pos (by norm_num) _
      have h1 := div_lt_div_succ y hb
      have h2 : ((y / 2 ^ ((i : ℕ) + 1) : ℕ) : ℝ) + 1 ≤ (g i.1 : ℝ) := by
        exact_mod_cast hlow i.1
      have h3 : (y : ℝ) / ((2 ^ ((i : ℕ) + 1) : ℕ) : ℝ) < (g i.1 : ℝ) :=
        lt_of_lt_of_le h1 h2
      push_cast at h3
      exact h3

end BertrandChains

section TrialShapes

/-- Trial shape used for Lemma 2′: introduce a block `U` of primes not dividing `n` with
exponent one, and lower the exponent of a block `D` by one. -/
private theorem no_trial_raise_lower {n : ℕ} (hn : Erdos381.HighlyComposite n)
    {U D : Finset ℕ} (hU : ∀ r ∈ U, r.Prime) (hD : ∀ r ∈ D, r.Prime)
    (hdisj : Disjoint U D) (hU0 : ∀ r ∈ U, n.factorization r = 0)
    (hD1 : ∀ r ∈ D, 1 ≤ n.factorization r)
    (hsize : ∏ r ∈ U, r < ∏ r ∈ D, r)
    (htau : (∏ r ∈ D, (n.factorization r + 1)) < 2 ^ U.card * ∏ r ∈ D, n.factorization r) :
    False := by
  classical
  have hDpos : 0 < ∏ r ∈ D, r ^ (n.factorization r - 1) :=
    Finset.prod_pos fun r hr ↦ pow_pos (hD r hr).pos _
  have hnotU : ∀ r ∈ D, r ∉ U := fun r hr ↦ Finset.disjoint_right.mp hdisj hr
  refine no_smaller_trial hn (T := U ∪ D) ?_
    (fun r ↦ if r ∈ U then 1 else n.factorization r - 1) ?_ ?_
  · intro r hr
    rcases Finset.mem_union.mp hr with h | h
    · exact hU r h
    · exact hD r h
  · rw [Finset.prod_union hdisj, Finset.prod_union hdisj]
    have e1 : (∏ r ∈ U, r ^ (if r ∈ U then 1 else n.factorization r - 1)) = ∏ r ∈ U, r :=
      Finset.prod_congr rfl fun r hr ↦ by rw [if_pos hr, pow_one]
    have e2 : (∏ r ∈ U, r ^ n.factorization r) = 1 :=
      Finset.prod_eq_one fun r hr ↦ by rw [hU0 r hr, pow_zero]
    have e3 : (∏ r ∈ D, r ^ (if r ∈ U then 1 else n.factorization r - 1))
        = ∏ r ∈ D, r ^ (n.factorization r - 1) :=
      Finset.prod_congr rfl fun r hr ↦ by rw [if_neg (hnotU r hr)]
    have e4 : (∏ r ∈ D, r ^ n.factorization r)
        = (∏ r ∈ D, r ^ (n.factorization r - 1)) * ∏ r ∈ D, r := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun r hr ↦ ?_
      rw [← pow_succ]
      congr 1
      have := hD1 r hr
      omega
    rw [e1, e2, e3, e4, one_mul]
    calc (∏ r ∈ U, r) * ∏ r ∈ D, r ^ (n.factorization r - 1)
        = (∏ r ∈ D, r ^ (n.factorization r - 1)) * ∏ r ∈ U, r := mul_comm _ _
      _ < (∏ r ∈ D, r ^ (n.factorization r - 1)) * ∏ r ∈ D, r :=
          mul_lt_mul_of_pos_left hsize hDpos
  · rw [Finset.prod_union hdisj, Finset.prod_union hdisj]
    have e1 : (∏ r ∈ U, (n.factorization r + 1)) = 1 :=
      Finset.prod_eq_one fun r hr ↦ by simp [hU0 r hr]
    have e2 : (∏ r ∈ U, ((if r ∈ U then 1 else n.factorization r - 1) + 1)) = 2 ^ U.card := by
      rw [Finset.prod_congr rfl fun r hr ↦ (by rw [if_pos hr] : _ = 2), Finset.prod_const]
    have e3 : (∏ r ∈ D, ((if r ∈ U then 1 else n.factorization r - 1) + 1))
        = ∏ r ∈ D, n.factorization r := by
      refine Finset.prod_congr rfl fun r hr ↦ ?_
      rw [if_neg (hnotU r hr)]
      have := hD1 r hr
      omega
    rw [e1, e2, e3, one_mul]
    exact htau

/-- Trial shape used for Lemma 3(ii): double the exponent on a block `U` of primes with
exponent one, and delete a block `D` of primes with exponent one. -/
private theorem no_trial_double_drop {n : ℕ} (hn : Erdos381.HighlyComposite n)
    {U D : Finset ℕ} (hU : ∀ r ∈ U, r.Prime) (hD : ∀ r ∈ D, r.Prime)
    (hdisj : Disjoint U D) (hU1 : ∀ r ∈ U, n.factorization r = 1)
    (hD1 : ∀ r ∈ D, n.factorization r = 1)
    (hsize : ∏ r ∈ U, r < ∏ r ∈ D, r)
    (htau : 2 ^ U.card * 2 ^ D.card < 3 ^ U.card) : False := by
  classical
  have hUpos : 0 < ∏ r ∈ U, r := Finset.prod_pos fun r hr ↦ (hU r hr).pos
  have hnotU : ∀ r ∈ D, r ∉ U := fun r hr ↦ Finset.disjoint_right.mp hdisj hr
  refine no_smaller_trial hn (T := U ∪ D) ?_ (fun r ↦ if r ∈ U then 2 else 0) ?_ ?_
  · intro r hr
    rcases Finset.mem_union.mp hr with h | h
    · exact hU r h
    · exact hD r h
  · rw [Finset.prod_union hdisj, Finset.prod_union hdisj]
    have e1 : (∏ r ∈ U, r ^ (if r ∈ U then 2 else 0)) = (∏ r ∈ U, r) * ∏ r ∈ U, r := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun r hr ↦ by rw [if_pos hr, sq]
    have e2 : (∏ r ∈ D, r ^ (if r ∈ U then 2 else 0)) = 1 :=
      Finset.prod_eq_one fun r hr ↦ by rw [if_neg (hnotU r hr), pow_zero]
    have e3 : (∏ r ∈ U, r ^ n.factorization r) = ∏ r ∈ U, r :=
      Finset.prod_congr rfl fun r hr ↦ by rw [hU1 r hr, pow_one]
    have e4 : (∏ r ∈ D, r ^ n.factorization r) = ∏ r ∈ D, r :=
      Finset.prod_congr rfl fun r hr ↦ by rw [hD1 r hr, pow_one]
    rw [e1, e2, e3, e4, mul_one]
    exact mul_lt_mul_of_pos_left hsize hUpos
  · rw [Finset.prod_union hdisj, Finset.prod_union hdisj]
    have e1 : (∏ r ∈ U, (n.factorization r + 1)) = 2 ^ U.card := by
      rw [Finset.prod_congr rfl fun r hr ↦ (by rw [hU1 r hr] : _ = 2), Finset.prod_const]
    have e2 : (∏ r ∈ D, (n.factorization r + 1)) = 2 ^ D.card := by
      rw [Finset.prod_congr rfl fun r hr ↦ (by rw [hD1 r hr] : _ = 2), Finset.prod_const]
    have e3 : (∏ r ∈ U, ((if r ∈ U then 2 else 0) + 1)) = 3 ^ U.card := by
      rw [Finset.prod_congr rfl fun r hr ↦ (by rw [if_pos hr] : _ = 3), Finset.prod_const]
    have e4 : (∏ r ∈ D, ((if r ∈ U then 2 else 0) + 1)) = 1 :=
      Finset.prod_eq_one fun r hr ↦ by simp [if_neg (hnotU r hr)]
    rw [e1, e2, e3, e4, mul_one]
    exact htau

end TrialShapes

section LemmaTwo

private theorem prod_image_fin {M : Type*} [CommMonoid M] {k : ℕ} {a : Fin k → ℕ}
    (hinj : Function.Injective a) (f : ℕ → M) :
    ∏ r ∈ Finset.image a Finset.univ, f r = ∏ i, f (a i) :=
  Finset.prod_image fun _ _ _ _ h ↦ hinj h

private theorem card_image_fin {k : ℕ} {a : Fin k → ℕ} (hinj : Function.Injective a) :
    (Finset.image a (Finset.univ : Finset (Fin k))).card = k := by
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **Erdős's Lemma 2′.**  In a highly composite number with `P := largestPrimeFactor n > 4096`
every prime `q` with `P / 2 < q ≤ P` has exponent exactly one.

The trial number is `n · P₁ P₂ / (q₁ q₂ q₃)` with `P₁ < P₂` the two Bertrand primes above `P`
and `q₁ > q₂ > q₃` a descending Bertrand chain below `q`. -/
theorem factorization_eq_one_of_half_lt {n q : ℕ} (hn : Erdos381.HighlyComposite n)
    (hPbig : 4096 < largestPrimeFactor n) (hq : q.Prime)
    (hqlow : (largestPrimeFactor n : ℝ) / 2 < q) (hqP : q ≤ largestPrimeFactor n) :
    n.factorization q = 1 := by
  classical
  set P : ℕ := largestPrimeFactor n with hPdef
  have hn1 : 1 < n := one_lt_of_largestPrimeFactor_pos (by omega)
  have hκ1 : 1 ≤ n.factorization q := one_le_factorization_of_le_largest hn hq hqP
  by_contra hcon
  have hκ2 : 2 ≤ n.factorization q := by omega
  have hPq : P < 2 * q := by
    have h : (P : ℝ) < 2 * q := by linarith
    exact_mod_cast h
  have hq2048 : 2048 < q := by omega
  obtain ⟨d, hdanti, hd⟩ := exists_descending_primes 3 (y := q) (by norm_num; omega)
  obtain ⟨P₁, hP₁, hPP₁, hP₁le⟩ := Nat.exists_prime_lt_and_le_two_mul P (by omega)
  obtain ⟨P₂, hP₂, hP₁P₂, hP₂le⟩ := Nat.exists_prime_lt_and_le_two_mul P₁ (by omega)
  set D : Finset ℕ := Finset.image d Finset.univ with hDdef
  set U : Finset ℕ := ({P₁, P₂} : Finset ℕ) with hUdef
  have hdinj : Function.Injective d := hdanti.injective
  have hdlt : ∀ i : Fin 3, d i < q := fun i ↦ (hd i).2.1
  have hdprime : ∀ i : Fin 3, (d i).Prime := fun i ↦ (hd i).1
  have hDmem : ∀ r ∈ D, ∃ i : Fin 3, d i = r := by
    intro r hr
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hr
    exact ⟨i, hi⟩
  have hDprime : ∀ r ∈ D, r.Prime := by
    intro r hr
    obtain ⟨i, rfl⟩ := hDmem r hr
    exact hdprime i
  have hDexp : ∀ r ∈ D, 2 ≤ n.factorization r := by
    intro r hr
    obtain ⟨i, rfl⟩ := hDmem r hr
    exact le_trans hκ2
      (Erdos381.highlyComposite_factorization_antitone hn (hdprime i) hq (hdlt i))
  have hUprime : ∀ r ∈ U, r.Prime := by
    intro r hr
    simp only [hUdef, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hP₁
    · exact hP₂
  have hU0 : ∀ r ∈ U, n.factorization r = 0 := by
    intro r hr
    simp only [hUdef, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact factorization_eq_zero_of_largestPrimeFactor_lt hn.1.ne' hP₁ hPP₁
    · exact factorization_eq_zero_of_largestPrimeFactor_lt hn.1.ne' hP₂ (by omega)
  have hdisj : Disjoint U D := by
    refine Finset.disjoint_left.mpr ?_
    intro r hrU hrD
    obtain ⟨i, rfl⟩ := hDmem r hrD
    simp only [hUdef, Finset.mem_insert, Finset.mem_singleton] at hrU
    have := hdlt i
    rcases hrU with h | h <;> omega
  refine no_trial_raise_lower hn hUprime hDprime hdisj hU0
    (fun r hr ↦ le_trans (by norm_num) (hDexp r hr)) ?_ ?_
  · -- size: `P₁ P₂ < q₁ q₂ q₃`
    have hP₁P₂ne : P₁ ≠ P₂ := by omega
    rw [Finset.prod_pair hP₁P₂ne, prod_image_fin hdinj (fun r ↦ r), Fin.prod_univ_three]
    have hPR : (4096 : ℝ) < P := by exact_mod_cast hPbig
    have hqR : (P : ℝ) / 2 < q := hqlow
    have h0 : (q : ℝ) / 2 ^ (1 : ℕ) < d 0 := (hd 0).2.2
    have h1 : (q : ℝ) / 2 ^ (2 : ℕ) < d 1 := (hd 1).2.2
    have h2 : (q : ℝ) / 2 ^ (3 : ℕ) < d 2 := (hd 2).2.2
    have hqpos : (0 : ℝ) < q := by positivity
    have e1 : ((q : ℝ) / 2) * ((q : ℝ) / 4) < (d 0 : ℝ) * (d 1 : ℝ) := by
      refine mul_lt_mul'' (by simpa using h0) (by norm_num at h1 ⊢; linarith) ?_ ?_ <;> positivity
    have e2 : (((q : ℝ) / 2) * ((q : ℝ) / 4)) * ((q : ℝ) / 8)
        < ((d 0 : ℝ) * (d 1 : ℝ)) * (d 2 : ℝ) := by
      refine mul_lt_mul'' e1 (by norm_num at h2 ⊢; linarith) ?_ ?_ <;> positivity
    have hP₁R : (P₁ : ℝ) ≤ 2 * P := by exact_mod_cast hP₁le
    have hP₂R : (P₂ : ℝ) ≤ 4 * P := by
      have : (P₂ : ℝ) ≤ 2 * P₁ := by exact_mod_cast hP₂le
      linarith
    have hP₁pos : (0 : ℝ) < P₁ := by exact_mod_cast hP₁.pos
    have hgoal : (P₁ : ℝ) * P₂ < (d 0 : ℝ) * (d 1 : ℝ) * (d 2 : ℝ) := by
      have hmul : (P₁ : ℝ) * P₂ ≤ 8 * (P : ℝ) ^ 2 := by nlinarith
      have hcube : 8 * (P : ℝ) ^ 2 < ((q : ℝ) / 2) * ((q : ℝ) / 4) * ((q : ℝ) / 8) := by
        have : ((q : ℝ) / 2) * ((q : ℝ) / 4) * ((q : ℝ) / 8) = (q : ℝ) ^ 3 / 64 := by ring
        rw [this]
        nlinarith [sq_nonneg ((P : ℝ)), sq_nonneg ((q : ℝ))]
      linarith
    exact_mod_cast hgoal
  · -- divisor count: `∏ (κ_i + 1) < 4 ∏ κ_i`
    have hcardU : U.card = 2 := by
      rw [hUdef]
      exact Finset.card_pair (by omega)
    rw [hcardU, prod_image_fin hdinj (fun r ↦ n.factorization r + 1),
      prod_image_fin hdinj (fun r ↦ n.factorization r), Fin.prod_univ_three, Fin.prod_univ_three]
    have ha : 2 ≤ n.factorization (d 0) :=
      hDexp _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    have hb : 2 ≤ n.factorization (d 1) :=
      hDexp _ (Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩)
    have hc : 2 ≤ n.factorization (d 2) :=
      hDexp _ (Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩)
    set a := n.factorization (d 0)
    set b := n.factorization (d 1)
    set c := n.factorization (d 2)
    have hkey : 8 * ((a + 1) * (b + 1) * (c + 1)) ≤ 27 * (a * b * c) := by
      calc 8 * ((a + 1) * (b + 1) * (c + 1)) = (2 * (a + 1)) * ((2 * (b + 1)) * (2 * (c + 1))) :=
            by ring
        _ ≤ (3 * a) * ((3 * b) * (3 * c)) :=
            Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
        _ = 27 * (a * b * c) := by ring
    have hpos : 0 < a * b * c := by positivity
    set X := (a + 1) * (b + 1) * (c + 1) with hX
    set Y := a * b * c with hY
    omega

end LemmaTwo

section Growth

/-- A highly composite number is bounded by an explicit function of its largest prime factor:
`n ≤ P ^ (6 (P + 1))`, since every prime power in `n` is `< P ^ 6` and `n` has at most `P + 1`
prime factors. -/
theorem le_pow_largestPrimeFactor {n : ℕ} (hn : Erdos381.HighlyComposite n) (hn1 : 1 < n) :
    n ≤ (largestPrimeFactor n) ^ (6 * (largestPrimeFactor n + 1)) := by
  classical
  set P : ℕ := largestPrimeFactor n with hPdef
  have hcard : n.primeFactors.card ≤ P + 1 := by
    have hsub : n.primeFactors ⊆ Finset.range (P + 1) := by
      intro p hp
      refine Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
      exact le_largestPrimeFactor hn.1.ne' (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
    simpa using Finset.card_le_card hsub
  calc n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
        Nat.prod_primeFactors_pow_factorization hn.1.ne'
    _ ≤ ∏ _p ∈ n.primeFactors, P ^ 6 := by
        refine Finset.prod_le_prod' fun p hp ↦ le_of_lt ?_
        exact pow_factorization_lt_pow_six hn (Nat.prime_of_mem_primeFactors hp)
          (le_largestPrimeFactor hn.1.ne' (Nat.prime_of_mem_primeFactors hp)
            (Nat.dvd_of_mem_primeFactors hp))
    _ = (P ^ 6) ^ n.primeFactors.card := by rw [Finset.prod_const]
    _ ≤ (P ^ 6) ^ (P + 1) := by
        refine Nat.pow_le_pow_right ?_ hcard
        exact Nat.one_le_pow _ _ (largestPrimeFactor_prime hn1).pos
    _ = P ^ (6 * (P + 1)) := by rw [← pow_mul]

/-- The largest prime factor of a highly composite number tends to infinity. -/
theorem eventually_lt_largestPrimeFactor (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, Erdos381.HighlyComposite n → B < largestPrimeFactor n := by
  filter_upwards [eventually_ge_atTop ((B + 2) ^ (6 * (B + 3)) + 1)] with n hge hHC
  by_contra hcon
  rw [not_lt] at hcon
  have hone : 1 ≤ (B + 2) ^ (6 * (B + 3)) := Nat.one_le_pow _ _ (by omega)
  have hn1 : 1 < n := by omega
  have hbound := le_pow_largestPrimeFactor hHC hn1
  have hstep : (largestPrimeFactor n) ^ (6 * (largestPrimeFactor n + 1))
      ≤ (B + 2) ^ (6 * (B + 3)) := by
    calc (largestPrimeFactor n) ^ (6 * (largestPrimeFactor n + 1))
        ≤ (B + 2) ^ (6 * (largestPrimeFactor n + 1)) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (B + 2) ^ (6 * (B + 3)) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

end Growth

section CorollaryTwo

/-- **Erdős's Corollary 2″.**  The largest prime factor of a highly composite number with
`largestPrimeFactor n > 4096` occurs to the first power.  (Ramanujan's sharp statement is that
`4` and `36` are the only highly composite exceptions; the crude threshold is all that is used
downstream.) -/
theorem factorization_largest_eq_one {n : ℕ} (hn : Erdos381.HighlyComposite n)
    (hPbig : 4096 < largestPrimeFactor n) :
    n.factorization (largestPrimeFactor n) = 1 := by
  refine factorization_eq_one_of_half_lt hn hPbig (largestPrimeFactor_prime ?_) ?_ le_rfl
  · exact one_lt_of_largestPrimeFactor_pos (by omega)
  · have : (0 : ℝ) < largestPrimeFactor n := by
      have : (4096 : ℝ) < largestPrimeFactor n := by exact_mod_cast hPbig
      linarith
    linarith

/-- Eventual form of Corollary 2″. -/
theorem eventually_factorization_largest_eq_one :
    ∀ᶠ n : ℕ in atTop, Erdos381.HighlyComposite n →
      n.factorization (largestPrimeFactor n) = 1 := by
  filter_upwards [eventually_lt_largestPrimeFactor 4096] with n hn hHC
  exact factorization_largest_eq_one hHC (hn hHC)

/-- **Lemma 2′, eventual form** (the frozen statement of the decomposition plan). -/
theorem eventually_factorization_eq_one_of_half_lt :
    ∀ᶠ n : ℕ in atTop, Erdos381.HighlyComposite n → ∀ q : ℕ, q.Prime →
      (largestPrimeFactor n : ℝ) / 2 < q → q ≤ largestPrimeFactor n →
      n.factorization q = 1 := by
  filter_upwards [eventually_lt_largestPrimeFactor 4096] with n hn hHC q hq h1 h2
  exact factorization_eq_one_of_half_lt hHC (hn hHC) hq h1 h2

end CorollaryTwo

section LemmaThree

/-- **Erdős's Lemma 3(ii).**  For a highly composite number with `P := largestPrimeFactor n`
beyond the absolute threshold `2 ^ 82`, every prime `q < 4 √P` has exponent at least two.

If some prime had exponent one, the least such prime `q₀` would satisfy `q₀ < 4 √P`, and then
every prime in `[q₀, P]` has exponent exactly one.  The trial number `n · Q₁⋯Q₇ / (p₁p₂p₃p₄)`,
built from the seven smallest primes `≥ q₀` and the four largest primes `≤ P`, multiplies `τ`
by `(3/2)^7 (1/2)^4 = 2187/2048 > 1` while Bertrand's postulate keeps it below `n`. -/
theorem two_le_factorization_of_lt_four_sqrt {n q : ℕ} (hn : Erdos381.HighlyComposite n)
    (hPbig : 2 ^ 82 < largestPrimeFactor n) (hq : q.Prime)
    (hqlt : (q : ℝ) < 4 * Real.sqrt (largestPrimeFactor n)) :
    2 ≤ n.factorization q := by
  classical
  set P : ℕ := largestPrimeFactor n with hPdef
  have hn1 : 1 < n := one_lt_of_largestPrimeFactor_pos (by omega)
  have hP : P.Prime := largestPrimeFactor_prime hn1
  set x : ℝ := Real.sqrt P with hxdef
  have hxsq : x ^ 2 = (P : ℝ) := Real.sq_sqrt (by positivity)
  have hPRbig : (2 : ℝ) ^ 82 < (P : ℝ) := by exact_mod_cast hPbig
  have hx41 : (2 : ℝ) ^ 41 < x := by
    rw [hxdef, show ((2 : ℝ) ^ 41) = Real.sqrt ((2 : ℝ) ^ 82) by
      rw [show ((2 : ℝ) ^ 82) = ((2 : ℝ) ^ 41) ^ 2 by ring, Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_lt_sqrt (by positivity) hPRbig
  have hxbig : (2048 : ℝ) < x := by nlinarith [hx41]
  have hx0 : (0 : ℝ) < x := by linarith
  have h4x : 4 * x < (P : ℝ) := by nlinarith [hxsq]
  have hqP : q ≤ P := by
    have h : (q : ℝ) < (P : ℝ) := lt_trans hqlt h4x
    exact le_of_lt (by exact_mod_cast h)
  by_contra hcon
  have hκ : n.factorization q = 1 := by
    have := one_le_factorization_of_le_largest hn hq hqP
    omega
  -- the least prime with exponent one
  have hex : ∃ r : ℕ, r.Prime ∧ n.factorization r = 1 := ⟨q, hq, hκ⟩
  set q₀ : ℕ := Nat.find hex with hq₀def
  have hq₀p : q₀.Prime := (Nat.find_spec hex).1
  have hq₀1 : n.factorization q₀ = 1 := (Nat.find_spec hex).2
  have hq₀le : q₀ ≤ q := Nat.find_min' hex ⟨hq, hκ⟩
  have hq₀R : (q₀ : ℝ) < 4 * x := by
    refine lt_of_le_of_lt ?_ hqlt
    exact_mod_cast hq₀le
  have hq₀0 : (0 : ℝ) ≤ (q₀ : ℝ) := by positivity
  -- every prime between `q₀` and `P` has exponent exactly one
  have hclaim : ∀ r : ℕ, r.Prime → q₀ ≤ r → r ≤ P → n.factorization r = 1 := by
    intro r hr hlow hhigh
    rcases eq_or_lt_of_le hlow with h | h
    · rw [← h]; exact hq₀1
    · have h1 : n.factorization r ≤ n.factorization q₀ :=
        Erdos381.highlyComposite_factorization_antitone hn hq₀p hr h
      have h2 : 1 ≤ n.factorization r := one_le_factorization_of_le_largest hn hr hhigh
      omega
  -- the two prime blocks
  obtain ⟨Q, hQmono, hQ⟩ := exists_ascending_primes 7 hq₀p
  obtain ⟨dd, hdanti, hdd⟩ := exists_descending_primes 3 (y := P)
    (le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hPbig.le)
  have hQ256 : ∀ i : Fin 7, (Q i : ℝ) ≤ 256 * x := by
    intro i
    have h1 := (hQ i).2.2
    have hi := i.2
    have h2 : (2 : ℝ) ^ ((i : ℕ)) ≤ 64 := by
      calc (2 : ℝ) ^ ((i : ℕ)) ≤ 2 ^ 6 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 64 := by norm_num
    nlinarith [hq₀R, hq₀0, h1, h2]
  have h256x : 256 * x < (P : ℝ) := by nlinarith [hxsq]
  have hQP : ∀ i : Fin 7, Q i ≤ P := by
    intro i
    have h : (Q i : ℝ) < (P : ℝ) := lt_of_le_of_lt (hQ256 i) h256x
    exact le_of_lt (by exact_mod_cast h)
  have hddlow : ∀ i : Fin 3, (P : ℝ) / 8 < (dd i : ℝ) := by
    intro i
    have h1 := (hdd i).2.2
    have hi := i.2
    have h2 : (2 : ℝ) ^ ((i : ℕ) + 1) ≤ 8 := by
      calc (2 : ℝ) ^ ((i : ℕ) + 1) ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 8 := by norm_num
    have hpow : (0 : ℝ) < 2 ^ ((i : ℕ) + 1) := by positivity
    have : (P : ℝ) / 8 ≤ (P : ℝ) / 2 ^ ((i : ℕ) + 1) := by
      apply div_le_div_of_nonneg_left (by positivity) hpow h2
    linarith
  have hPdiv8 : 256 * x < (P : ℝ) / 8 := by nlinarith [hxsq]
  have hq₀dd : ∀ i : Fin 3, q₀ ≤ dd i := by
    intro i
    have h : (q₀ : ℝ) < (dd i : ℝ) := by
      have := hddlow i
      linarith [hq₀R]
    exact le_of_lt (by exact_mod_cast h)
  -- the Finsets
  set U : Finset ℕ := Finset.image Q Finset.univ with hUdef
  set D : Finset ℕ := insert P (Finset.image dd Finset.univ) with hDdef
  have hQinj : Function.Injective Q := hQmono.injective
  have hddinj : Function.Injective dd := hdanti.injective
  have hUmem : ∀ r ∈ U, ∃ i : Fin 7, Q i = r := by
    intro r hr
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hr
    exact ⟨i, hi⟩
  have hDmem : ∀ r ∈ D, r = P ∨ ∃ i : Fin 3, dd i = r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with h | h
    · exact Or.inl h
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨i, hi⟩
  have hUprime : ∀ r ∈ U, r.Prime := by
    intro r hr; obtain ⟨i, rfl⟩ := hUmem r hr; exact (hQ i).1
  have hDprime : ∀ r ∈ D, r.Prime := by
    intro r hr
    rcases hDmem r hr with rfl | ⟨i, rfl⟩
    · exact hP
    · exact (hdd i).1
  have hU1 : ∀ r ∈ U, n.factorization r = 1 := by
    intro r hr
    obtain ⟨i, rfl⟩ := hUmem r hr
    exact hclaim _ (hQ i).1 (hQ i).2.1 (hQP i)
  have hD1 : ∀ r ∈ D, n.factorization r = 1 := by
    intro r hr
    rcases hDmem r hr with rfl | ⟨i, rfl⟩
    · exact hclaim _ hP (le_trans hq₀le hqP) le_rfl
    · exact hclaim _ (hdd i).1 (hq₀dd i) (le_of_lt (hdd i).2.1)
  have hdisj : Disjoint U D := by
    refine Finset.disjoint_left.mpr ?_
    intro r hrU hrD
    obtain ⟨i, rfl⟩ := hUmem r hrU
    have hup : (Q i : ℝ) ≤ 256 * x := hQ256 i
    rcases hDmem _ hrD with heq | ⟨j, hj⟩
    · have : (Q i : ℝ) = (P : ℝ) := by exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℝ)) heq
      linarith
    · have hlow : (P : ℝ) / 8 < (dd j : ℝ) := hddlow j
      have : (Q i : ℝ) = (dd j : ℝ) := by
        exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℝ)) hj.symm
      linarith
  refine no_trial_double_drop hn hUprime hDprime hdisj hU1 hD1 ?_ ?_
  · -- size: `Q₁⋯Q₇ < p₁p₂p₃p₄`
    have hPnotmem : P ∉ Finset.image dd (Finset.univ : Finset (Fin 3)) := by
      intro hmem
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
      exact absurd hi (hdd i).2.1.ne
    rw [hUdef, hDdef, prod_image_fin hQinj (fun r ↦ r),
      Finset.prod_insert hPnotmem, prod_image_fin hddinj (fun r ↦ r)]
    have hQprodR : (∏ i : Fin 7, (Q i : ℝ)) ≤ (q₀ : ℝ) ^ 7 * 2 ^ 21 := by
      have hstep : (∏ i : Fin 7, (Q i : ℝ)) ≤ ∏ i : Fin 7, ((q₀ : ℝ) * 2 ^ ((i : ℕ))) := by
        refine Finset.prod_le_prod (fun i _ ↦ by positivity) (fun i _ ↦ (hQ i).2.2)
      refine le_trans hstep (le_of_eq ?_)
      rw [Fin.prod_univ_seven]
      norm_num
      ring
    have hQprodlt : (q₀ : ℝ) ^ 7 * 2 ^ 21 < 2 ^ 35 * x ^ 7 := by
      have h1 : (q₀ : ℝ) ^ 7 < (4 * x) ^ 7 := by gcongr
      nlinarith [h1]
    have hddprodR : ((P : ℝ) / 2) * ((P : ℝ) / 4) * ((P : ℝ) / 8)
        < ∏ i : Fin 3, (dd i : ℝ) := by
      rw [Fin.prod_univ_three]
      have h0 : (P : ℝ) / 2 < (dd 0 : ℝ) := by
        have := (hdd 0).2.2; norm_num at this ⊢; linarith
      have h1 : (P : ℝ) / 4 < (dd 1 : ℝ) := by
        have := (hdd 1).2.2; norm_num at this ⊢; linarith
      have h2 : (P : ℝ) / 8 < (dd 2 : ℝ) := by
        have := (hdd 2).2.2; norm_num at this ⊢; linarith
      have e1 : ((P : ℝ) / 2) * ((P : ℝ) / 4) < (dd 0 : ℝ) * (dd 1 : ℝ) :=
        mul_lt_mul'' h0 h1 (by positivity) (by positivity)
      exact mul_lt_mul'' e1 h2 (by positivity) (by positivity)
    have hbig : (2 : ℝ) ^ 35 * x ^ 7
        ≤ (P : ℝ) * (((P : ℝ) / 2) * ((P : ℝ) / 4) * ((P : ℝ) / 8)) := by
      have heq : (P : ℝ) * (((P : ℝ) / 2) * ((P : ℝ) / 4) * ((P : ℝ) / 8)) = x ^ 8 / 64 := by
        rw [← hxsq]; ring
      rw [heq]
      have hkey : 0 < x ^ 7 * (x - 2 ^ 41) := mul_pos (pow_pos hx0 7) (by linarith)
      nlinarith [hkey, pow_succ x 7]
    have hPR0 : (0 : ℝ) < (P : ℝ) := by positivity
    have hfinal : (∏ i : Fin 7, (Q i : ℝ))
        < (P : ℝ) * ∏ i : Fin 3, (dd i : ℝ) := by
      have hstep : (P : ℝ) * (((P : ℝ) / 2) * ((P : ℝ) / 4) * ((P : ℝ) / 8))
          < (P : ℝ) * ∏ i : Fin 3, (dd i : ℝ) := mul_lt_mul_of_pos_left hddprodR hPR0
      linarith
    have hcast : ((∏ i : Fin 7, Q i : ℕ) : ℝ) < ((P * ∏ i : Fin 3, dd i : ℕ) : ℝ) := by
      push_cast
      exact hfinal
    exact_mod_cast hcast
  · -- divisor count: `2 ^ 7 · 2 ^ 4 < 3 ^ 7`
    have hcardU : U.card = 7 := card_image_fin hQinj
    have hcardD : D.card = 4 := by
      have hPnotmem : P ∉ Finset.image dd (Finset.univ : Finset (Fin 3)) := by
        intro hmem
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
        exact absurd hi (hdd i).2.1.ne
      rw [hDdef, Finset.card_insert_of_notMem hPnotmem, card_image_fin hddinj]
    rw [hcardU, hcardD]
    norm_num

end LemmaThree

section LemmaOne

/-- `√x · log x` is eventually below any fixed positive multiple of `x`.  Elementary proof:
with `u = √√x` one has `log x = 4 log u ≤ 4 (u - 1)` and `√x · log x ≤ 4 u ^ 3 ≤ c u ^ 4`. -/
private theorem eventually_sqrt_mul_log_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x * Real.log x ≤ c * x := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop ((4 / c) ^ 4)]
    with x hx1 hx2
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set u : ℝ := Real.sqrt (Real.sqrt x) with hudef
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have husq : Real.sqrt x = u ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg x)).symm
  have hux : u ^ 4 = x := by
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = Real.sqrt x ^ 2 := by rw [← husq]
      _ = x := Real.sq_sqrt hx0
  have hlogx : Real.log x = 4 * Real.log u := by
    rw [hudef, Real.log_sqrt (Real.sqrt_nonneg x), Real.log_sqrt hx0]
    ring
  have hs1 : (1 : ℝ) ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx1
  have hu1 : (1 : ℝ) ≤ u := by
    rw [hudef]
    simpa using Real.sqrt_le_sqrt hs1
  have hlogu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hu4c : 4 / c ≤ u := by
    by_contra hcon
    rw [not_le] at hcon
    have hlt : u ^ 4 < (4 / c) ^ 4 := by gcongr
    rw [hux] at hlt
    linarith
  have hcu : 4 ≤ c * u := by
    rw [div_le_iff₀ hc] at hu4c
    linarith
  calc Real.sqrt x * Real.log x = u ^ 2 * (4 * Real.log u) := by rw [husq, hlogx]
    _ ≤ u ^ 2 * (4 * (u - 1)) := by nlinarith [sq_nonneg u]
    _ ≤ c * u ^ 4 := by
        nlinarith [mul_nonneg (pow_nonneg hu0 3) (by linarith : (0 : ℝ) ≤ c * u - 4),
          sq_nonneg u]
    _ = c * x := by rw [hux]

/-- Chebyshev's lower bound in the crude form Lemma 1c needs. -/
private theorem eventually_third_le_theta :
    ∀ᶠ x : ℝ in atTop, x / 3 ≤ Chebyshev.theta x := by
  filter_upwards [eventually_sqrt_mul_log_le (c := 1 / 20) (by norm_num),
    eventually_ge_atTop (100 : ℝ)] with x hsl hx100
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hge := Chebyshev.theta_ge' hx1
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogxpos : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx1
  have hlogle : Real.log x ≤ Real.sqrt x * Real.log x := by nlinarith
  have hlogx2 : Real.log (x + 2) ≤ 2 * Real.log x := by
    have hx2 : x + 2 ≤ x ^ 2 := by nlinarith
    have h1 : Real.log (x + 2) ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) hx2
    rwa [Real.log_pow, show ((2 : ℕ) : ℝ) = 2 by norm_num] at h1
  have hmul : (x - 1) * 0.6931471803 ≤ (x - 1) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2lo.le (by linarith)
  linarith

/-- Chebyshev's upper bound in the crude form Lemma 1b needs. -/
private theorem eventually_primeCounting_mul_log_le :
    ∀ᶠ x : ℝ in atTop, ((⌊x⌋₊.primeCounting : ℝ)) * Real.log x ≤ 2.9 * x := by
  filter_upwards [eventually_sqrt_mul_log_le (c := 1 / 10) (by norm_num),
    eventually_ge_atTop (10 : ℝ)] with x hsl hx10
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hlogxpos : 0 < Real.log x := Real.log_pos hx1
  have h := Chebyshev.pi_le_log4_mul_div hx1
  rw [Real.log_sqrt hx0] at h
  have hdiv : Real.log 4 * x / (Real.log x / 2) = 2 * Real.log 4 * x / Real.log x := by
    field_simp
  rw [hdiv] at h
  have hmul := mul_le_mul_of_nonneg_right h hlogxpos.le
  rw [add_mul, div_mul_cancel₀ _ hlogxpos.ne'] at hmul
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [hlog4] at hmul
  have hb : 2 * (2 * Real.log 2) * x ≤ 2.7725887232 * x := by nlinarith [hlog2hi, hx0]
  linarith

/-- Lemma 1c, arithmetic half: `θ(P) ≤ log n`, since every prime `≤ P` divides `n`. -/
theorem theta_largestPrimeFactor_le_log {n : ℕ} (hn : Erdos381.HighlyComposite n) :
    Chebyshev.theta (largestPrimeFactor n) ≤ Real.log n := by
  classical
  set P : ℕ := largestPrimeFactor n with hPdef
  have hdvd : primorial P ∣ n := by
    have heq : primorial P = ∏ p ∈ Nat.primesLE P, p := by
      simp [primorial, Nat.primesLE, Nat.primesBelow]
    rw [heq]
    refine Finset.prod_primes_dvd n (fun a ha ↦ ?_) (fun a ha ↦ ?_)
    · simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range,
        Nat.lt_succ_iff] at ha
      exact ha.2.prime
    · simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range,
        Nat.lt_succ_iff] at ha
      exact prime_dvd_of_le_largest hn ha.2 ha.1
  have hle : (primorial P : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hn.1 hdvd
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  exact Real.log_le_log (by exact_mod_cast primorial_pos P) hle

/-- Lemma 1b, arithmetic half: `log n ≤ 6 π(P) log P`, by Lemma 1a applied to each prime. -/
theorem log_le_six_mul_primeCounting_mul_log {n : ℕ} (hn : Erdos381.HighlyComposite n)
    (hn1 : 1 < n) :
    Real.log n ≤ 6 * ((largestPrimeFactor n).primeCounting : ℝ)
      * Real.log (largestPrimeFactor n) := by
  classical
  set P : ℕ := largestPrimeFactor n with hPdef
  have hP : P.Prime := largestPrimeFactor_prime hn1
  have hPR1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP.one_lt.le
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg hPR1
  have hmem : ∀ p ∈ Nat.primesLE P, p.Prime ∧ p ≤ P := by
    intro p hp
    simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range,
      Nat.lt_succ_iff] at hp
    exact ⟨hp.2, hp.1⟩
  have hsub : n.primeFactors ⊆ Nat.primesLE P := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hple : p ≤ P :=
      le_largestPrimeFactor hn.1.ne' hpp (Nat.dvd_of_mem_primeFactors hp)
    simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range,
      Nat.lt_succ_iff]
    exact ⟨hple, hpp⟩
  rw [Erdos381.log_nat_eq_sum_factorization_on n (Nat.primesLE P) hsub]
  have hterm : ∀ p ∈ Nat.primesLE P,
      (n.factorization p : ℝ) * Real.log p ≤ 6 * Real.log P := by
    intro p hp
    obtain ⟨hpp, hple⟩ := hmem p hp
    have hlt : (p : ℝ) ^ n.factorization p ≤ (P : ℝ) ^ 6 := by
      exact_mod_cast (pow_factorization_lt_pow_six hn hpp hple).le
    have hppos : (0 : ℝ) < (p : ℝ) ^ n.factorization p := by
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      positivity
    have hlog := Real.log_le_log hppos hlt
    rwa [Real.log_pow, Real.log_pow, show ((6 : ℕ) : ℝ) = 6 by norm_num] at hlog
  calc ∑ p ∈ Nat.primesLE P, (n.factorization p : ℝ) * Real.log p
      ≤ ∑ _p ∈ Nat.primesLE P, 6 * Real.log P := Finset.sum_le_sum hterm
    _ = (Nat.primesLE P).card * (6 * Real.log P) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 6 * (P.primeCounting : ℝ) * Real.log P := by
        rw [Nat.primesLE_card_eq_primeCounting]
        ring

/-- **Erdős's Lemma 1.**  For every sufficiently large highly composite `n`,
`log n / 18 < P ≤ 3 log n`, where `P = largestPrimeFactor n`. -/
theorem eventually_log_lt_and_lt_log :
    ∀ᶠ n : ℕ in atTop, Erdos381.HighlyComposite n →
      Real.log n / 18 < largestPrimeFactor n ∧
        (largestPrimeFactor n : ℝ) ≤ 3 * Real.log n := by
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp eventually_third_le_theta
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp eventually_primeCounting_mul_log_le
  filter_upwards [eventually_lt_largestPrimeFactor (⌈max X₁ X₂⌉₊ + 2),
    eventually_gt_atTop 1] with n hlow hn1 hHC
  have hP := hlow hHC
  set P : ℕ := largestPrimeFactor n with hPdef
  have hPR : (max X₁ X₂ : ℝ) ≤ (P : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast hP.le.trans' (by omega)
  have hPpos : (0 : ℝ) < (P : ℝ) := by
    have : (0 : ℕ) < P := by omega
    exact_mod_cast this
  constructor
  · -- `log n < 18 P`
    have hupper := log_le_six_mul_primeCounting_mul_log hHC hn1
    have hcheb := hX₂ (P : ℝ) (le_trans (le_max_right X₁ X₂) hPR)
    rw [Nat.floor_natCast] at hcheb
    have : Real.log n ≤ 6 * (2.9 * (P : ℝ)) := by
      have h6 : (0 : ℝ) ≤ 6 := by norm_num
      nlinarith [hupper, hcheb]
    linarith
  · -- `P ≤ 3 log n`
    have hlower := theta_largestPrimeFactor_le_log hHC
    have hcheb := hX₁ (P : ℝ) (le_trans (le_max_left X₁ X₂) hPR)
    linarith

end LemmaOne

/-- **Lemma 3(ii), eventual form** (the frozen statement of the decomposition plan). -/
theorem eventually_two_le_factorization_of_lt_four_sqrt :
    ∀ᶠ n : ℕ in atTop, Erdos381.HighlyComposite n → ∀ q : ℕ, q.Prime →
      (q : ℝ) < 4 * Real.sqrt (largestPrimeFactor n) → 2 ≤ n.factorization q := by
  filter_upwards [eventually_lt_largestPrimeFactor (2 ^ 82)] with n hn hHC q hq h
  exact two_le_factorization_of_lt_four_sqrt hHC (hn hHC) hq h

end Erdos381Lower
