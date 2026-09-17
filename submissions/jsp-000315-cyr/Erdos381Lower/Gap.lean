import Erdos381Lower.GapCore
import Erdos381Lower.Structure

/-!
# Erdős #381, lower bound: the gap theorem (§3.8)

This module assembles Erdős's 1944 gap theorem from the four previous modules:

* `Structure.lean` supplies the highly-composite input — Lemma 1 (`p := P(n)` is of order
  `log n`), Lemma 2′ (primes in `(p/2, p]` have exponent one) and Lemma 3(ii) (primes below
  `4√p` have exponent at least two);
* `Dirichlet.lean` supplies the pair `s, t` approximating `δ = log q / log p`;
* `Blocks.lean` supplies the four blocks of primes around `p` and around `q`;
* `GapCore.lean` supplies the two trial numbers, the dichotomy of §3.6 and Lemma C1.

The parameters are those of digest §3.5: with `L ≥ 8` the fixed-power exponent of
`Erdos381.exists_fixedPower_prime_windows`, the Dirichlet exponent is `A = 1/(8L)`, the block
errors are `εp = 8L·p^(1/(8L) − 1/L)` and `εq = 8L·q^(1/(4L) − 1/L)`, and the final gap
exponent is `c = 1/(20L)`.
-/

namespace Erdos381Lower

open Erdos381 Filter

/-! ### The analytic side condition of §3.5 -/

/-- The total error of §3.5, `24L·x^(−1/(4L)) + x^(−1/(8L))·log x`, is eventually smaller than
half of `x^(−1/(10L))`.  This is the only place where the three scales `s, t ≍ x^(1/(8L))`,
`εp ≍ x^(−7/(8L))` and `εq ≍ x^(−3/(8L))` are reconciled. -/
theorem eventually_error_lt (L : ℕ) (hL : 0 < L) :
    ∀ᶠ x : ℝ in atTop,
      2 * (24 * (L : ℝ) * x ^ (-(1 / (4 * (L : ℝ)))) +
        x ^ (-(1 / (8 * (L : ℝ)))) * Real.log x) < x ^ (-(1 / (10 * (L : ℝ)))) := by
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hr1 : (0 : ℝ) < 3 / (20 * (L : ℝ)) := by positivity
  have hr2 : (0 : ℝ) < 1 / (40 * (L : ℝ)) := by positivity
  have hlog := (isLittleO_log_rpow_atTop hr2).def (c := 1 / 8) (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop hr1).eventually_gt_atTop (96 * (L : ℝ)), hlog] with x hx1 hx2 hx3
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx1
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1.le
  have hpos1 : (0 : ℝ) < x ^ (3 / (20 * (L : ℝ))) := Real.rpow_pos_of_pos hx0 _
  have hpos2 : (0 : ℝ) < x ^ (1 / (40 * (L : ℝ))) := Real.rpow_pos_of_pos hx0 _
  have hbase : (0 : ℝ) < x ^ (-(1 / (10 * (L : ℝ)))) := Real.rpow_pos_of_pos hx0 _
  have hlog2 : 4 * Real.log x < x ^ (1 / (40 * (L : ℝ))) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogx,
      abs_of_nonneg hpos2.le] at hx3
    linarith
  have e1 : x ^ (-(1 / (4 * (L : ℝ)))) =
      x ^ (-(1 / (10 * (L : ℝ)))) * (x ^ (3 / (20 * (L : ℝ))))⁻¹ := by
    rw [← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]
    congr 1
    field_simp
    ring
  have e2 : x ^ (-(1 / (8 * (L : ℝ)))) =
      x ^ (-(1 / (10 * (L : ℝ)))) * (x ^ (1 / (40 * (L : ℝ))))⁻¹ := by
    rw [← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]
    congr 1
    field_simp
    ring
  have h1 : 48 * (L : ℝ) * (x ^ (3 / (20 * (L : ℝ))))⁻¹ < 1 / 2 := by
    have hmul := mul_lt_mul_of_pos_right hx2 (inv_pos.2 hpos1)
    rw [mul_inv_cancel₀ hpos1.ne'] at hmul
    nlinarith [inv_pos.2 hpos1]
  have h2 : 2 * (x ^ (1 / (40 * (L : ℝ))))⁻¹ * Real.log x < 1 / 2 := by
    have hmul := mul_lt_mul_of_pos_right hlog2 (inv_pos.2 hpos2)
    rw [mul_inv_cancel₀ hpos2.ne'] at hmul
    nlinarith [inv_pos.2 hpos2, hlogx]
  rw [e1, e2]
  nlinarith [mul_lt_mul_of_pos_left (add_lt_add h1 h2) hbase]

/-! ### The `rpow` bookkeeping of §3.5 -/

/-- Monotonicity of the negated exponents occurring in §3.5. -/
theorem neg_div_le_neg_div {a b y : ℝ} (hy : 0 < y) (hab : a ≤ b) : -(b / y) ≤ -(a / y) := by
  have h : a / y ≤ b / y := by gcongr
  linarith

/-- **The `q`-side block error.**  Since `q > √p`, the relative window at `q` with exponent
`1/(4L)` is at most the window at `p` with exponent `3/(8L)`.  This is the step the digest
corrects in `scope.md`. -/
theorem rpow_sqrt_block_le {L : ℕ} (hL : 0 < L) {x y : ℝ} (hx : 0 < x)
    (hxy : Real.sqrt x ≤ y) :
    y ^ (1 / (4 * (L : ℝ)) - 1 / (L : ℝ)) ≤ x ^ (-(3 / (8 * (L : ℝ)))) := by
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hsq0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hexp : 1 / (4 * (L : ℝ)) - 1 / (L : ℝ) = -(3 / (4 * (L : ℝ))) := by
    field_simp
    ring
  have h1 : y ^ (-(3 / (4 * (L : ℝ)))) ≤ Real.sqrt x ^ (-(3 / (4 * (L : ℝ)))) :=
    Real.rpow_le_rpow_of_nonpos hsq0 hxy (neg_nonpos.2 (by positivity))
  have h2 : Real.sqrt x ^ (-(3 / (4 * (L : ℝ)))) = x ^ (-(3 / (8 * (L : ℝ)))) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
    congr 1
    field_simp
    ring
  rw [hexp, ← h2]
  exact h1

/-- **The total block error of §3.5.**  With `s ≤ x ^ (1/(8L))` and `t ≤ x ^ (1/(8L)) + 1`, the
two block contributions `t·εp` and `s·εq` are at most `24L·x ^ (−1/(4L))`. -/
theorem block_error_bound {L : ℕ} (hL : 0 < L) {x y : ℝ} (hx : 1 < x) (hxy : Real.sqrt x ≤ y)
    {s t : ℕ} (hs : (s : ℝ) ≤ x ^ (1 / (8 * (L : ℝ))))
    (ht : (t : ℝ) ≤ x ^ (1 / (8 * (L : ℝ))) + 1) :
    (t : ℝ) * (8 * (L : ℝ) * x ^ (1 / (8 * (L : ℝ)) - 1 / (L : ℝ))) +
        (s : ℝ) * (8 * (L : ℝ) * y ^ (1 / (4 * (L : ℝ)) - 1 / (L : ℝ))) ≤
      24 * (L : ℝ) * x ^ (-(1 / (4 * (L : ℝ)))) := by
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (Real.sqrt_pos.2 hx0) hxy
  set u : ℝ := x ^ (1 / (8 * (L : ℝ))) with hu
  have hu1 : (1 : ℝ) ≤ u := by
    have h := Real.rpow_le_rpow_of_exponent_le hx.le
      (by positivity : (0 : ℝ) ≤ 1 / (8 * (L : ℝ)))
    rwa [Real.rpow_zero] at h
  have hepx : x ^ (1 / (8 * (L : ℝ)) - 1 / (L : ℝ)) = x ^ (-(7 / (8 * (L : ℝ)))) := by
    congr 1
    field_simp
    ring
  have hprod1 : u * x ^ (-(7 / (8 * (L : ℝ)))) = x ^ (-(3 / (4 * (L : ℝ)))) := by
    rw [hu, ← Real.rpow_add hx0]
    congr 1
    field_simp
    ring
  have hprod2 : u * x ^ (-(3 / (8 * (L : ℝ)))) = x ^ (-(1 / (4 * (L : ℝ)))) := by
    rw [hu, ← Real.rpow_add hx0]
    congr 1
    field_simp
    ring
  have hmono1 : x ^ (-(3 / (4 * (L : ℝ)))) ≤ x ^ (-(1 / (4 * (L : ℝ)))) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (neg_div_le_neg_div (by positivity) (by norm_num))
  have hq_le : y ^ (1 / (4 * (L : ℝ)) - 1 / (L : ℝ)) ≤ x ^ (-(3 / (8 * (L : ℝ)))) :=
    rpow_sqrt_block_le hL hx0 hxy
  have hterm1 : (t : ℝ) * (8 * (L : ℝ) * x ^ (1 / (8 * (L : ℝ)) - 1 / (L : ℝ))) ≤
      16 * (L : ℝ) * x ^ (-(1 / (4 * (L : ℝ)))) := by
    rw [hepx]
    have h1 : (t : ℝ) * (8 * (L : ℝ) * x ^ (-(7 / (8 * (L : ℝ))))) ≤
        2 * u * (8 * (L : ℝ) * x ^ (-(7 / (8 * (L : ℝ))))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : 2 * u * (8 * (L : ℝ) * x ^ (-(7 / (8 * (L : ℝ))))) =
        16 * (L : ℝ) * (u * x ^ (-(7 / (8 * (L : ℝ))))) := by ring
    rw [h2, hprod1] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left hmono1 (by positivity))
  have hterm2 : (s : ℝ) * (8 * (L : ℝ) * y ^ (1 / (4 * (L : ℝ)) - 1 / (L : ℝ))) ≤
      8 * (L : ℝ) * x ^ (-(1 / (4 * (L : ℝ)))) := by
    have hcnn : (0 : ℝ) ≤ 8 * (L : ℝ) * y ^ (1 / (4 * (L : ℝ)) - 1 / (L : ℝ)) := by
      have := Real.rpow_nonneg hy0.le (1 / (4 * (L : ℝ)) - 1 / (L : ℝ))
      nlinarith
    have h1 : (s : ℝ) * (8 * (L : ℝ) * y ^ (1 / (4 * (L : ℝ)) - 1 / (L : ℝ))) ≤
        u * (8 * (L : ℝ) * x ^ (-(3 / (8 * (L : ℝ))))) :=
      mul_le_mul hs (mul_le_mul_of_nonneg_left hq_le (by positivity)) hcnn (by linarith)
    have h2 : u * (8 * (L : ℝ) * x ^ (-(3 / (8 * (L : ℝ))))) =
        8 * (L : ℝ) * (u * x ^ (-(3 / (8 * (L : ℝ))))) := by ring
    rw [h2, hprod2] at h1
    exact h1
  linarith

/-- **Smallness of the two block errors.**  Both are `≤ 8L·x ^ (−3/(8L))`, so their sum is
below `log 2` as soon as `16L < log 2 · x ^ (3/(8L))`. -/
theorem block_error_lt_log_two {L : ℕ} (hL : 0 < L) {x y : ℝ} (hx : 1 < x)
    (hxy : Real.sqrt x ≤ y)
    (hcond : 16 * (L : ℝ) < Real.log 2 * x ^ (3 / (8 * (L : ℝ)))) :
    8 * (L : ℝ) * x ^ (1 / (8 * (L : ℝ)) - 1 / (L : ℝ)) +
      8 * (L : ℝ) * y ^ (1 / (4 * (L : ℝ)) - 1 / (L : ℝ)) < Real.log 2 := by
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hpos : (0 : ℝ) < x ^ (3 / (8 * (L : ℝ))) := Real.rpow_pos_of_pos hx0 _
  have hepx : x ^ (1 / (8 * (L : ℝ)) - 1 / (L : ℝ)) = x ^ (-(7 / (8 * (L : ℝ)))) := by
    congr 1
    field_simp
    ring
  have hmono : x ^ (-(7 / (8 * (L : ℝ)))) ≤ x ^ (-(3 / (8 * (L : ℝ)))) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (neg_div_le_neg_div (by positivity) (by norm_num))
  have hq_le : y ^ (1 / (4 * (L : ℝ)) - 1 / (L : ℝ)) ≤ x ^ (-(3 / (8 * (L : ℝ)))) :=
    rpow_sqrt_block_le hL hx0 hxy
  have hinv : x ^ (-(3 / (8 * (L : ℝ)))) = (x ^ (3 / (8 * (L : ℝ))))⁻¹ :=
    Real.rpow_neg hx0.le _
  have hkey : 16 * (L : ℝ) * (x ^ (3 / (8 * (L : ℝ))))⁻¹ < Real.log 2 := by
    have hmul := mul_lt_mul_of_pos_right hcond (inv_pos.2 hpos)
    rwa [mul_assoc (Real.log 2), mul_inv_cancel₀ hpos.ne', mul_one] at hmul
  rw [hepx]
  rw [hinv] at hmono hq_le
  nlinarith

/-- **The last display of §3.5.**  If `log n ≤ p²` then `p ^ (−1/(10L))` is below
`(log n) ^ (−1/(20L))`, which converts the `p`-scale gap into the `log n`-scale gap. -/
theorem rpow_le_log_rpow {L : ℕ} (hL : 0 < L) {x ln : ℝ} (hx : 0 < x) (hln0 : 0 < ln)
    (hln : ln ≤ x ^ 2) :
    x ^ (-(1 / (10 * (L : ℝ)))) ≤ ln ^ (-(1 / (20 * (L : ℝ)))) := by
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have h1 : (x ^ 2) ^ (-(1 / (20 * (L : ℝ)))) ≤ ln ^ (-(1 / (20 * (L : ℝ)))) :=
    Real.rpow_le_rpow_of_nonpos hln0 hln (neg_nonpos.2 (by positivity))
  have h2 : (x ^ 2) ^ (-(1 / (20 * (L : ℝ)))) = x ^ (-(1 / (10 * (L : ℝ)))) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    field_simp
    ring
  rw [← h2]
  exact h1

/-! ### The prime `q` of §3.1 -/

/-- **The choice of `q` (§3.1).**  For a highly composite `n` whose largest prime factor `P` is
large, the largest prime with exponent at least two lies in `(√P, P/2]`, and every prime
strictly between it and `P` has exponent exactly one.  Bertrand's postulate produces a prime in
`(√P, 4√P)`, which has exponent `≥ 2` by Lemma 3(ii); Lemma 2′ forces `q ≤ P/2`. -/
theorem exists_maximal_two_le_factorization {n : ℕ} (hn : HighlyComposite n)
    (hP : 2 ^ 82 < largestPrimeFactor n)
    (hhalf : ∀ r : ℕ, r.Prime → (largestPrimeFactor n : ℝ) / 2 < r →
      r ≤ largestPrimeFactor n → n.factorization r = 1) :
    ∃ q : ℕ, q.Prime ∧ 2 ≤ n.factorization q ∧
      Real.sqrt (largestPrimeFactor n) < q ∧ 2 * q ≤ largestPrimeFactor n ∧
      ∀ r : ℕ, r.Prime → q < r → r < largestPrimeFactor n → n.factorization r = 1 := by
  classical
  set P : ℕ := largestPrimeFactor n with hPdef
  have hn1 : 1 < n := one_lt_of_largestPrimeFactor_pos (by omega)
  have hP2 : 2 ≤ P := le_trans (by norm_num) hP.le
  have hPR : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP2
  have hPR0 : (0 : ℝ) < (P : ℝ) := by linarith
  have hsq1 : (1 : ℝ) < Real.sqrt P := by
    have : Real.sqrt 1 < Real.sqrt P := Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    simpa using this
  obtain ⟨r, hrp, hmr, hr2m⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (⌊Real.sqrt P⌋₊ + 1) (by omega)
  have hfloor : Real.sqrt P < (⌊Real.sqrt P⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfloorle : ((⌊Real.sqrt P⌋₊ : ℕ) : ℝ) ≤ Real.sqrt P :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have hrgt : Real.sqrt P < (r : ℝ) := by
    refine lt_of_lt_of_le hfloor ?_
    have : ((⌊Real.sqrt P⌋₊ + 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hmr.le
    push_cast at this
    linarith
  have hrlt : (r : ℝ) < 4 * Real.sqrt P := by
    have h1 : ((r : ℕ) : ℝ) ≤ ((2 * (⌊Real.sqrt P⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast hr2m
    push_cast at h1
    linarith
  have hkr : 2 ≤ n.factorization r :=
    two_le_factorization_of_lt_four_sqrt hn hP hrp hrlt
  set S : Finset ℕ := n.primeFactors.filter (fun r ↦ 2 ≤ n.factorization r) with hSdef
  have hrS : r ∈ S := by
    refine Finset.mem_filter.2 ⟨?_, hkr⟩
    exact Nat.mem_primeFactors.2 ⟨hrp, Nat.dvd_of_factorization_pos (by omega), hn.1.ne'⟩
  have hSne : S.Nonempty := ⟨r, hrS⟩
  set q : ℕ := S.max' hSne with hqdef
  have hqS : q ∈ S := S.max'_mem hSne
  have hqmem := Finset.mem_filter.1 hqS
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqmem.1
  have hq2 : 2 ≤ n.factorization q := hqmem.2
  have hqP : q ≤ P := le_largestPrimeFactor hn.1.ne' hqprime
    (Nat.dvd_of_mem_primeFactors hqmem.1)
  have hmax : ∀ m : ℕ, m.Prime → 2 ≤ n.factorization m → m ≤ q := by
    intro m hm hkm
    refine Finset.le_max' _ m (Finset.mem_filter.2 ⟨?_, hkm⟩)
    exact Nat.mem_primeFactors.2 ⟨hm, Nat.dvd_of_factorization_pos (by omega), hn.1.ne'⟩
  have hqsqrt : Real.sqrt P < (q : ℝ) := by
    refine lt_of_lt_of_le hrgt ?_
    exact_mod_cast Finset.le_max' _ r hrS
  have hq2p : 2 * q ≤ P := by
    by_contra hcon
    have hlt : (P : ℝ) / 2 < (q : ℝ) := by
      have : (P : ℝ) < 2 * (q : ℝ) := by exact_mod_cast Nat.lt_of_not_le hcon
      linarith
    have := hhalf q hqprime hlt hqP
    omega
  refine ⟨q, hqprime, hq2, hqsqrt, hq2p, fun m hm hqm hmP ↦ ?_⟩
  have hle : n.factorization m ≤ 1 := by
    by_contra hcon
    exact absurd (hmax m hm (by omega)) (not_le.2 hqm)
  have hge : 1 ≤ n.factorization m :=
    one_le_factorization_of_le_largest hn hm hmP.le
  omega

/-! ### The gap theorem (§3.8) -/

/-- **Erdős's gap theorem (1944).**  There is `c > 0` such that every sufficiently large highly
composite number `n` is followed by another highly composite number below
`n + n (log n) ^ (−c)`.

With `L ≥ 8` the fixed-power exponent of `Erdos381.exists_fixedPower_prime_windows`, the proof
takes `c = 1/(20L)`: `p := P(n)` and the largest prime `q` with exponent `≥ 2` satisfy
`√p < q ≤ p/2`; Dirichlet approximation of `δ = log q / log p` with denominator `p ^ (1/(8L))`
produces `s, t`; the four prime blocks of §3.3 produce the trial numbers `n₁`, `n₂`, one of
which has strictly more divisors than `n` (§3.6) while lying within `n(1 ± p ^ (−1/(10L)))`
(§3.5); Lemma C1 then produces a genuine highly composite number in the gap. -/
theorem erdos381_gap :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, HighlyComposite n →
      ∃ n' : ℕ, HighlyComposite n' ∧ n < n' ∧ (n' : ℝ) < n + n * Real.log n ^ (-c) := by
  obtain ⟨L, N₀, hL8, hwindow⟩ := Erdos381.exists_fixedPower_prime_windows
  have hL0 : 0 < L := by omega
  have hLR : (8 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL8
  have hLR0 : (0 : ℝ) < (L : ℝ) := by linarith
  refine ⟨1 / (20 * (L : ℝ)), by positivity, ?_⟩
  have hA0 : (0 : ℝ) < 1 / (8 * (L : ℝ)) := by positivity
  have hAL : 1 / (8 * (L : ℝ)) < 1 / (L : ℝ) := one_div_lt_one_div_of_lt hLR0 (by linarith)
  have hB0 : (0 : ℝ) < 1 / (4 * (L : ℝ)) := by positivity
  have hBL : 1 / (4 * (L : ℝ)) < 1 / (L : ℝ) := one_div_lt_one_div_of_lt hLR0 (by linarith)
  obtain ⟨xp, hxp⟩ := exists_threshold_nonempty_primeBlocks hL0 hwindow hA0 hAL
  obtain ⟨xq, hxq⟩ := exists_threshold_nonempty_primeBlocks hL0 hwindow hB0 hBL
  have hcond : ∀ᶠ x : ℝ in atTop, xp ≤ x ∧ xq ≤ Real.sqrt x ∧
      2 < x ^ (1 / (8 * (L : ℝ))) ∧
      16 * (L : ℝ) < Real.log 2 * x ^ (3 / (8 * (L : ℝ))) ∧
      2 * (24 * (L : ℝ) * x ^ (-(1 / (4 * (L : ℝ)))) +
        x ^ (-(1 / (8 * (L : ℝ)))) * Real.log x) < x ^ (-(1 / (10 * (L : ℝ)))) := by
    have h1 : ∀ᶠ x : ℝ in atTop, xq ≤ Real.sqrt x :=
      Real.tendsto_sqrt_atTop.eventually_ge_atTop xq
    have h2 : ∀ᶠ x : ℝ in atTop, 2 < x ^ (1 / (8 * (L : ℝ))) :=
      (tendsto_rpow_atTop hA0).eventually_gt_atTop 2
    have h3 : ∀ᶠ x : ℝ in atTop, 16 * (L : ℝ) < Real.log 2 * x ^ (3 / (8 * (L : ℝ))) :=
      (Filter.Tendsto.const_mul_atTop (Real.log_pos (by norm_num))
        (tendsto_rpow_atTop (by positivity))).eventually_gt_atTop _
    filter_upwards [eventually_ge_atTop xp, h1, h2, h3, eventually_error_lt L hL0]
      with x k1 k2 k3 k4 k5
    exact ⟨k1, k2, k3, k4, k5⟩
  obtain ⟨X, hX⟩ := eventually_atTop.1 hcond
  filter_upwards [eventually_lt_largestPrimeFactor (max ⌈X⌉₊ (2 ^ 82)),
    eventually_log_lt_and_lt_log, eventually_factorization_eq_one_of_half_lt,
    eventually_ge_atTop 3] with n hB1 hB2 hB3 hn3
  intro hHC
  have hpB : max ⌈X⌉₊ (2 ^ 82) < largestPrimeFactor n := hB1 hHC
  have hp82 : 2 ^ 82 < largestPrimeFactor n := lt_of_le_of_lt (le_max_right _ _) hpB
  have hPpos : 0 < largestPrimeFactor n := lt_of_le_of_lt (Nat.zero_le _) hp82
  have hn1 : 1 < n := one_lt_of_largestPrimeFactor_pos hPpos
  have hpprime : (largestPrimeFactor n).Prime := largestPrimeFactor_prime hn1
  have hlogp18 : Real.log n / 18 < largestPrimeFactor n := (hB2 hHC).1
  have hzero : ∀ r : ℕ, r.Prime → largestPrimeFactor n < r → n.factorization r = 0 :=
    fun r hr h ↦ factorization_eq_zero_of_largestPrimeFactor_lt hHC.1.ne' hr h
  obtain ⟨q, hqprime, hq2, hqsqrt, hq2p, honeq⟩ :=
    exists_maximal_two_le_factorization hHC hp82 (hB3 hHC)
  set p : ℕ := largestPrimeFactor n with hpdef
  have hpR1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.one_lt
  have hpR0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hXp : X ≤ (p : ℝ) := by
    have h1 : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    have h2 : (⌈X⌉₊ : ℝ) ≤ (p : ℝ) := by
      have h3 : ⌈X⌉₊ ≤ p := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hpB)
      exact_mod_cast h3
    linarith
  obtain ⟨hxpP, hxqP, hpA, hεcond, herrcond⟩ := hX (p : ℝ) hXp
  have hq0 : 0 < q := hqprime.pos
  have hqp : q < p := by
    have := hqprime.two_le
    omega
  have hqR1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hqprime.one_lt
  have hqR0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hqpR : (q : ℝ) < (p : ℝ) := by exact_mod_cast hqp
  have hlogp : 0 < Real.log p := Real.log_pos hpR1
  have hlogsq : Real.log p / 2 < Real.log q := by
    have h := Real.log_lt_log (Real.sqrt_pos.2 hpR0) hqsqrt
    rwa [Real.log_sqrt hpR0.le] at h
  have hlow : 1 / 2 < Real.log q / Real.log p := by
    rw [lt_div_iff₀ hlogp]
    linarith
  have hhigh : Real.log q / Real.log p < 1 := by
    rw [div_lt_one hlogp]
    exact Real.log_lt_log hqR0 hqpR
  obtain ⟨s, t, hs1, ht1, -, hsu, htu, -, hDir⟩ := exists_dirichlet_pair hpR1 hpA hlow hhigh
  have hu1 : (1 : ℝ) ≤ (p : ℝ) ^ (1 / (8 * (L : ℝ))) := by
    have h := Real.rpow_le_rpow_of_exponent_le hpR1.le hA0.le
    rwa [Real.rpow_zero] at h
  set H : ℕ := ⌈(p : ℝ) ^ (1 / (8 * (L : ℝ)))⌉₊ + 1 with hHdef
  have hHlt : (H : ℝ) < (p : ℝ) ^ (1 / (8 * (L : ℝ))) + 2 := by
    have hc := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ (p : ℝ) ^ (1 / (8 * (L : ℝ))))
    rw [hHdef]
    push_cast
    linarith
  have hHge : (p : ℝ) ^ (1 / (8 * (L : ℝ))) + 1 ≤ (H : ℝ) := by
    have hc := Nat.le_ceil ((p : ℝ) ^ (1 / (8 * (L : ℝ))))
    rw [hHdef]
    push_cast
    linarith
  have hsH : s ≤ H := by
    have h : (s : ℝ) ≤ (H : ℝ) := by linarith
    exact_mod_cast h
  have htH : t ≤ H := by
    have h : (t : ℝ) ≤ (H : ℝ) := by linarith
    exact_mod_cast h
  obtain ⟨Bp⟩ := hxp (p : ℝ) hxpP H (by linarith)
  have hXq : xq ≤ (q : ℝ) := le_trans hxqP hqsqrt.le
  have huq : (p : ℝ) ^ (1 / (8 * (L : ℝ))) ≤ (q : ℝ) ^ (1 / (4 * (L : ℝ))) := by
    have h1 : Real.sqrt (p : ℝ) ^ (1 / (4 * (L : ℝ))) ≤ (q : ℝ) ^ (1 / (4 * (L : ℝ))) :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) hqsqrt.le hB0.le
    have h2 : Real.sqrt (p : ℝ) ^ (1 / (4 * (L : ℝ))) = (p : ℝ) ^ (1 / (8 * (L : ℝ))) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hpR0.le]
      congr 1
      field_simp
      ring
    rwa [h2] at h1
  obtain ⟨Bq⟩ := hxq (q : ℝ) hXq H (by linarith)
  have hεp0 : (0 : ℝ) ≤ 8 * (L : ℝ) * (p : ℝ) ^ (1 / (8 * (L : ℝ)) - 1 / (L : ℝ)) := by
    positivity
  have hεq0 : (0 : ℝ) ≤ 8 * (L : ℝ) * (q : ℝ) ^ (1 / (4 * (L : ℝ)) - 1 / (L : ℝ)) := by
    positivity
  have hε := block_error_lt_log_two hL0 hpR1 hqsqrt.le hεcond
  have htwo : ∀ r : ℕ, r.Prime → r < q → 2 ≤ n.factorization r := fun r hr h ↦
    le_trans hq2 (Erdos381.highlyComposite_factorization_antitone hHC hr hqprime h)
  obtain ⟨FB⟩ := exists_fourBlocks Bp Bq hsH htH hq0 hq2p hεp0 hεq0 hε hzero honeq htwo
  have hEle := block_error_bound hL0 hpR1 hqsqrt.le hsu htu
  have hlogn0 : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have h18 : (18 : ℝ) ≤ (p : ℝ) := by
    have h : (18 : ℕ) ≤ p := le_of_lt (lt_of_le_of_lt (by norm_num) hp82)
    exact_mod_cast h
  have hlognp : Real.log n ≤ (p : ℝ) ^ 2 := by nlinarith [hlogp18]
  have hfinal : (p : ℝ) ^ (-(1 / (10 * (L : ℝ)))) ≤ Real.log n ^ (-(1 / (20 * (L : ℝ)))) :=
    rpow_le_log_rpow hL0 hpR0 hlogn0 hlognp
  have hone_le : (p : ℝ) ^ (-(1 / (10 * (L : ℝ)))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hpR1.le (neg_nonpos.2 (by positivity))
  exact exists_highlyComposite_lt_of_fourBlocks hHC FB hqp hs1 hεp0 hεq0 hDir
    (by linarith) (by linarith)

end Erdos381Lower
