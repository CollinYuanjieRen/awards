import Mathlib

/-!
# Erdős Problem #1100: `τ_⊥(n) ≥ ω(n)`, with equality for infinitely many `n`

If `1 = d_1 < ⋯ < d_{τ(n)} = n` are the divisors of `n`, let `τ_⊥(n)` count the indices `i` with
`gcd(d_i, d_{i+1}) = 1`.  Erdős asked whether `τ_⊥(n)/ω(n) → ∞` for almost all `n`, whether
`τ_⊥(n) < exp((log n)^{o(1)})`, and for the growth of `g(k) = max_{ω(n) = k} τ_⊥(n)` (OPEN; not
addressed here, nor the Erdős–Hall and Erdős–Simonovits bounds).  The problem page records:
"It is trivial that `τ_⊥(n) ≥ ω(n)` (with equality for infinitely many `n`)."  This file proves
both parts.

There is no formal-conjectures statement for #1100, so the definitions are ours: for a divisor
`d < n`, `nextDivisor n d` is the least divisor of `n` exceeding `d` (its successor in the sorted
list of divisors), and `tauPerp n` counts the divisors `d < n` with `gcd(d, nextDivisor n d) = 1`,
i.e. the consecutive coprime pairs `(d_i, d_{i+1})`; `ω(n)` is `n.primeFactors.card`.

Proof.  For each prime `p ∣ n`, the largest divisor `d < p` of `n` has successor `p`, and
`gcd(d, p) = 1`; distinct primes give distinct such `d` (as `d_p < p ≤ d_q` for `p < q`), so
`τ_⊥(n) ≥ ω(n)`.  For `n = 2^k` (`k ≥ 1`) the divisors are `1, 2, …, 2^k` and only the pair
`(1, 2)` is coprime, so `τ_⊥(2^k) = 1 = ω(2^k)`.
-/

open Finset

/-- The least divisor of `n` exceeding `d` (the successor of `d` among the divisors, for `d < n`). -/
noncomputable def nextDivisor (n d : ℕ) : ℕ := sInf {e : ℕ | e ∣ n ∧ d < e}

/-- `τ_⊥(n)`: the number of consecutive divisor pairs `(d_i, d_{i+1})` of `n` with
`gcd(d_i, d_{i+1}) = 1`, counted by their first element `d_i < n`. -/
noncomputable def tauPerp (n : ℕ) : ℕ :=
  open scoped Classical in
  ((n.divisors.filter (· < n)).filter fun d => Nat.gcd d (nextDivisor n d) = 1).card

/-- For a divisor `d < n`, `nextDivisor n d` divides `n` and exceeds `d`. -/
theorem nextDivisor_spec (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    nextDivisor n d ∣ n ∧ d < nextDivisor n d :=
  Nat.sInf_mem
    (⟨n, dvd_rfl, lt_of_lt_of_le hd (Nat.le_of_dvd hn dvd_rfl)⟩ :
      {e : ℕ | e ∣ n ∧ d < e}.Nonempty)

/-- `nextDivisor n d` is the least divisor of `n` exceeding `d`. -/
theorem nextDivisor_le (n d e : ℕ) (he : e ∣ n) (hde : d < e) : nextDivisor n d ≤ e :=
  Nat.sInf_le ⟨he, hde⟩

/-- `Nat.findGreatest (· ∣ n) (p - 1)`, the largest divisor of `n` below `p`, divides `n`. -/
theorem findGreatest_dvd_dvd (n p : ℕ) (hp : 2 ≤ p) :
    Nat.findGreatest (· ∣ n) (p - 1) ∣ n := by
  have h1 : (1 : ℕ) ≤ p - 1 := by omega
  exact Nat.findGreatest_spec (P := (· ∣ n)) h1 (one_dvd n)

/-- The largest divisor of `n` below `p` is positive (it is at least `1`). -/
theorem one_le_findGreatest_dvd (n p : ℕ) (hp : 2 ≤ p) :
    1 ≤ Nat.findGreatest (· ∣ n) (p - 1) :=
  Nat.le_findGreatest (by omega) (one_dvd n)

/-- The largest divisor of `n` below `p` is indeed below `p`. -/
theorem findGreatest_dvd_lt (n p : ℕ) (hp : 2 ≤ p) :
    Nat.findGreatest (· ∣ n) (p - 1) < p :=
  lt_of_le_of_lt (Nat.findGreatest_le _) (by omega)

/-- If `d` is the largest divisor of `n` below a divisor `p` of `n`, then `d`'s successor is `p`. -/
theorem nextDivisor_eq_of_maximal (n p d : ℕ) (hpn : p ∣ n) (hn : 0 < n)
    (hdp : d < p) (hmax : ∀ e, e ∣ n → e < p → e ≤ d) :
    nextDivisor n d = p := by
  have hpn' : p ≤ n := Nat.le_of_dvd hn hpn
  refine le_antisymm (nextDivisor_le n d p hpn hdp) ?_
  obtain ⟨he, hde⟩ := nextDivisor_spec n d hn (lt_of_lt_of_le hdp hpn')
  rcases Nat.lt_or_ge (nextDivisor n d) p with h | h
  · exact absurd (hmax _ he h) (not_le.mpr hde)
  · exact h

/-- The successor of the largest divisor of `n` below a divisor `p` of `n` is `p`. -/
theorem nextDivisor_findGreatest (n p : ℕ) (hp : 2 ≤ p) (hpn : p ∣ n) (hn : 0 < n) :
    nextDivisor n (Nat.findGreatest (· ∣ n) (p - 1)) = p :=
  nextDivisor_eq_of_maximal n p _ hpn hn (findGreatest_dvd_lt n p hp)
    (fun e hen hep => Nat.le_findGreatest (by omega) hen)

/-- Among the divisors of `2 ^ k`, the successor of `2 ^ i` is `2 ^ (i + 1)` (for `i < k`). -/
theorem nextDivisor_two_pow (k i : ℕ) (hik : i < k) :
    nextDivisor (2 ^ k) (2 ^ i) = 2 ^ (i + 1) := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hlt : (2 : ℕ) ^ i < 2 ^ k := Nat.pow_lt_pow_right one_lt_two hik
  refine le_antisymm (nextDivisor_le _ _ _ (pow_dvd_pow 2 hik)
    (Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self i))) ?_
  obtain ⟨he, hde⟩ := nextDivisor_spec (2 ^ k) (2 ^ i) hpos hlt
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp he
  rw [hj] at hde ⊢
  have hij : i < j := by
    rcases Nat.lt_or_ge i j with h | h
    · exact h
    · exact absurd hde (not_lt.mpr (Nat.pow_le_pow_right (by norm_num) h))
  exact Nat.pow_le_pow_right (by norm_num) hij

/-- For a prime `p ∣ n`, the largest divisor of `n` below `p` has successor `p`. -/
theorem nextDivisor_pred_prime (n p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hn : 0 < n) :
    ∃ d, d ∣ n ∧ d < p ∧ nextDivisor n d = p :=
  ⟨Nat.findGreatest (· ∣ n) (p - 1), findGreatest_dvd_dvd n p hp.two_le,
    findGreatest_dvd_lt n p hp.two_le, nextDivisor_findGreatest n p hp.two_le hpn hn⟩

/-- **Erdős #1100, the trivial bound**: `τ_⊥(n) ≥ ω(n)` for every `n`. -/
theorem erdos_1100_omega_le_tauPerp (n : ℕ) : n.primeFactors.card ≤ tauPerp n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tauPerp]
  classical
  rw [tauPerp]
  have key : ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, p < q →
      Nat.findGreatest (· ∣ n) (p - 1) < Nat.findGreatest (· ∣ n) (q - 1) := by
    intro p hp q _ hpq
    exact lt_of_lt_of_le
      (findGreatest_dvd_lt n p (Nat.prime_of_mem_primeFactors hp).two_le)
      (Nat.le_findGreatest (by omega) (Nat.dvd_of_mem_primeFactors hp))
  refine Finset.card_le_card_of_injOn (fun p => Nat.findGreatest (· ∣ n) (p - 1)) ?_ ?_
  · intro p hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
    have hdn := findGreatest_dvd_dvd n p hp.two_le
    have hdp := findGreatest_dvd_lt n p hp.two_le
    have hd1 := one_le_findGreatest_dvd n p hp.two_le
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨⟨hdn, hn.ne'⟩, lt_of_lt_of_le hdp (Nat.le_of_dvd hn hpn)⟩, ?_⟩
    rw [nextDivisor_findGreatest n p hp.two_le hpn hn]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (Nat.not_dvd_of_pos_of_lt hd1 hdp))
  · intro p hp q hq h
    rcases lt_trichotomy p q with hlt | heq | hgt
    · exact absurd h (ne_of_lt (key p (Finset.mem_coe.mp hp) q (Finset.mem_coe.mp hq) hlt))
    · exact heq
    · exact absurd h (ne_of_gt (key q (Finset.mem_coe.mp hq) p (Finset.mem_coe.mp hp) hgt))

/-- `τ_⊥(2^k) = 1` for `k ≥ 1`. -/
theorem tauPerp_two_pow (k : ℕ) (hk : 1 ≤ k) : tauPerp (2 ^ k) = 1 := by
  classical
  rw [tauPerp]
  have hset : (((2 ^ k).divisors.filter (· < 2 ^ k)).filter
      fun d => Nat.gcd d (nextDivisor (2 ^ k) d) = 1) = {1} := by
    ext d
    rw [Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨hd, -⟩, hdlt⟩, hgcd⟩
      obtain ⟨i, hik, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      have hik' : i < k := by
        rcases lt_or_eq_of_le hik with h | h
        · exact h
        · rw [h] at hdlt; exact absurd hdlt (lt_irrefl _)
      rw [nextDivisor_two_pow k i hik',
        Nat.gcd_eq_left (pow_dvd_pow 2 (Nat.le_succ i))] at hgcd
      exact hgcd
    · rintro rfl
      refine ⟨⟨⟨one_dvd _, (Nat.two_pow_pos k).ne'⟩, ?_⟩, ?_⟩
      · calc (1 : ℕ) < 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      · have h2 : nextDivisor (2 ^ k) 1 = 2 := by
          have := nextDivisor_two_pow k 0 (by omega)
          simpa using this
        rw [h2]
        exact Nat.gcd_one_left 2
  rw [hset, Finset.card_singleton]

/-- **Erdős #1100, equality for infinitely many `n`**: `τ_⊥(n) = ω(n)` for infinitely many `n`. -/
theorem erdos_1100_eq_infinite : ¬ {n : ℕ | tauPerp n = n.primeFactors.card}.Finite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 ^ (k + 1)) ?_ ?_
  · intro a b hab
    have h := Nat.pow_right_injective (le_refl 2) hab
    omega
  · intro k
    show tauPerp (2 ^ (k + 1)) = (2 ^ (k + 1)).primeFactors.card
    rw [tauPerp_two_pow (k + 1) (by omega),
      Nat.primeFactors_prime_pow (by omega) Nat.prime_two, Finset.card_singleton]

/-- Closed form of the page's remark. -/
theorem erdos_1100_remark_closed :
    (∀ n : ℕ, n.primeFactors.card ≤ tauPerp n) ∧
      ¬ {n : ℕ | tauPerp n = n.primeFactors.card}.Finite :=
  ⟨erdos_1100_omega_le_tauPerp, erdos_1100_eq_infinite⟩
