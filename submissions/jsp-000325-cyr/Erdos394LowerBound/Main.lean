import Mathlib

/-!
# Erdős Problem #394: the trivial lower bound `∑_{n ≤ x} t₂(n) ≫ x² / log x`

Let `t_k(n)` be the least `m ≥ 1` such that `n ∣ m(m+1)⋯(m+k−1)`.  Erdős and Graham asked
about the average behaviour of `t_k` (the questions on the problem page are OPEN).  The page
records: "since `t₂(p) = p − 1` for prime `p` it is trivial that `∑_{n ≤ x} t₂(n) ≫ x²/log x`."
This file proves that bound in the exact shape of the formal-conjectures statement
`Erdos394.erdos_394.variants.lower_bound` (tagged "research solved" with `sorry`; the
formal-conjectures notation `g ≪ f` means `IsBigO atTop g f` for functions `ℕ → ℝ`), with the
definition `t` copied verbatim.

Proof.  If `p` is prime then `t₂(p) = p − 1` (`p ∣ m(m+1)` forces `p ≤ m + 1`, and `m = p − 1`
works); more generally `t₂(n) ≥ p − 1` for every prime `p ∣ n`.  No `n ≤ x` has two prime
factors larger than `√x`, so summing `p − 1` over the `⌊x/p⌋` multiples `n ≤ x` of each prime
`p ∈ (√x, x/2]` gives `x·π(x/2) ≤ 4·∑_{n ≤ x} t₂(n) + x·√x`, and Chebyshev's bound
`π(y) ≥ (y log 2 − log (y+1)) / log y` in Mathlib gives `π(x/2) ≫ x / log x`.  The open
questions are not addressed.
-/

open Nat Filter Finset
open scoped Asymptotics

/-- `t k n` is the least `m ≥ 1` such that `n ∣ m(m+1)⋯(m+k−1)` (formal-conjectures
definition; `sInf ∅ = 0`). -/
noncomputable def t (k n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) }

namespace Erdos394

/-- Membership in the set defining `t 2 n`, with the two-term product expanded. -/
private lemma mem_tset_two {n m : ℕ} :
    (m ∈ { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range 2, (m + i) }) ↔ (0 < m ∧ n ∣ m * (m + 1)) := by
  simp [Finset.prod_range_succ]

/-- For `n > 0` the set defining `t 2 n` is nonempty: `m = n` belongs to it. -/
private lemma tset_two_nonempty {n : ℕ} (hn : 0 < n) :
    { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range 2, (m + i) }.Nonempty :=
  ⟨n, mem_tset_two.2 ⟨hn, Dvd.intro _ rfl⟩⟩

/-- The defining property of `t 2 n` for `n > 0`. -/
private lemma t_two_spec {n : ℕ} (hn : 0 < n) : 0 < t 2 n ∧ n ∣ t 2 n * (t 2 n + 1) :=
  mem_tset_two.1 (Nat.sInf_mem (tset_two_nonempty hn))

/-- Any witness bounds `t 2 n` from above. -/
private lemma t_two_le {n m : ℕ} (hm : 0 < m) (hdvd : n ∣ m * (m + 1)) : t 2 n ≤ m :=
  Nat.sInf_le (mem_tset_two.2 ⟨hm, hdvd⟩)

/-- If a prime `p` divides `n > 0`, then `p - 1 ≤ t₂(n)`: indeed `p ∣ m(m+1)` with
`m = t₂(n) > 0` forces `p ≤ m` or `p ≤ m + 1`. -/
private lemma sub_one_le_t_two {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : 0 < n) :
    p - 1 ≤ t 2 n := by
  obtain ⟨hpos, hdvd⟩ := t_two_spec hn
  have hpd : p ∣ t 2 n * (t 2 n + 1) := hpn.trans hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
  · have := Nat.le_of_dvd hpos h; omega
  · have := Nat.le_of_dvd (by omega) h; omega

/-- The elementary counting bound.  Summing `t₂(n) ≥ p − 1` over the multiples `n ≤ x` of each
prime `p` with `√x < p ≤ x/2` (no `n ≤ x` has two such prime factors, so the contributions do
not overlap) gives `x · π(x/2) ≤ 4 ∑_{n ≤ x} t₂(n) + x·√x`. -/
private lemma key_nat (x : ℕ) (hx : 16 ≤ x) :
    x * Nat.primeCounting (x / 2) ≤ 4 * (∑ n ∈ Finset.Icc 1 x, t 2 n) + x * Nat.sqrt x := by
  set s := Nat.sqrt x with hs
  have hs4 : 4 * s ≤ x := by
    nlinarith [Nat.sqrt_le' x, Nat.sqrt_le_self x, Nat.sqrt_lt_self (by omega : 1 < x),
      Nat.sqrt_le x]
  have hsx : x < (s + 1) * (s + 1) := Nat.lt_succ_sqrt x
  set P : Finset ℕ := {p ∈ Finset.Icc 1 (x / 2) | p.Prime ∧ s < p} with hP
  have hmem : ∀ p, p ∈ P ↔ (1 ≤ p ∧ p ≤ x / 2) ∧ (p.Prime ∧ s < p) := by
    intro p; simp [hP]
  -- (1) `#P` is at least `π(x/2) - √x`
  have hcard : Nat.primeCounting (x / 2) ≤ P.card + s := by
    have hsub : Nat.primesLE (x / 2) ⊆ P ∪ Finset.Icc 1 s := by
      intro p hp
      rw [Nat.mem_primesLE] at hp
      obtain ⟨hple, hpp⟩ := hp
      rcases lt_or_ge s p with h | h
      · exact Finset.mem_union_left _ ((hmem p).2 ⟨⟨hpp.one_lt.le, hple⟩, hpp, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_Icc.2 ⟨hpp.one_lt.le, h⟩)
    have h1 := Finset.card_le_card hsub
    rw [Nat.primesLE_card_eq_primeCounting] at h1
    calc Nat.primeCounting (x / 2) ≤ (P ∪ Finset.Icc 1 s).card := h1
      _ ≤ P.card + (Finset.Icc 1 s).card := Finset.card_union_le _ _
      _ = P.card + s := by simp
  -- (2) at most one `p ∈ P` divides a given `n ≤ x`, so the weights stay below `t 2 n`
  have hpt : ∀ n ∈ Finset.Icc 1 x, ∑ p ∈ {p ∈ P | p ∣ n}, (p - 1) ≤ t 2 n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hcard1 : ({p ∈ P | p ∣ n} : Finset ℕ).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      by_contra hne
      obtain ⟨-, hpa, hsa⟩ := (hmem a).1 ha.1
      obtain ⟨-, hpb, hsb⟩ := (hmem b).1 hb.1
      have hcop : Nat.Coprime a b := (Nat.coprime_primes hpa hpb).2 hne
      have hdvd : a * b ∣ n := hcop.mul_dvd_of_dvd_of_dvd ha.2 hb.2
      have hle := Nat.le_of_dvd (by omega) hdvd
      have : (s + 1) * (s + 1) ≤ a * b := Nat.mul_le_mul (by omega) (by omega)
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcard1 with h | h
    · rw [Finset.card_eq_zero.1 h]; simp
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.1 h
      have hpmem : p ∈ ({p ∈ P | p ∣ n} : Finset ℕ) := by
        rw [hp]; exact Finset.mem_singleton_self p
      simp only [Finset.mem_filter] at hpmem
      rw [hp, Finset.sum_singleton]
      exact sub_one_le_t_two ((hmem p).1 hpmem.1).2.1 hpmem.2 (by omega)
  -- (3) exchange the order of summation
  have hswap : ∑ p ∈ P, (x / p) * (p - 1)
      = ∑ n ∈ Finset.Icc 1 x, ∑ p ∈ {p ∈ P | p ∣ n}, (p - 1) := by
    symm
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    congr 1
    rw [show Finset.Icc 1 x = Finset.Ioc 0 x from rfl]
    exact Nat.Ioc_filter_dvd_card_eq_div x p
  -- (4) every term of the prime sum is at least `x / 4`
  have hper : ∀ p ∈ P, x ≤ 4 * ((x / p) * (p - 1)) := by
    intro p hpP
    obtain ⟨⟨hp1, hp2⟩, hpp, hps⟩ := (hmem p).1 hpP
    have hppos : 0 < p := by omega
    have hq : x / p ≤ s := by
      have h1 : x / p ≤ x / (s + 1) := Nat.div_le_div_left (by omega) (by omega)
      have h2 : x / (s + 1) < s + 1 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by nlinarith)
      omega
    have hB : x < (x / p) * p + p := by
      have h1 := Nat.div_add_mod x p
      have h2 := Nat.mod_lt x hppos
      nlinarith
    have hA : (x / p) * (p - 1) + (x / p) = (x / p) * p := by
      rw [Nat.mul_sub, Nat.mul_one]
      have : x / p ≤ (x / p) * p := Nat.le_mul_of_pos_right _ hppos
      omega
    have h2p : 2 * p ≤ x := by
      have := Nat.div_mul_le_self x 2
      omega
    revert hA hB hq
    generalize (x / p) * (p - 1) = A
    generalize x / p = Q
    generalize (x / p) * p = B
    intro h1 h2 h3
    omega
  have hfinal : x * P.card ≤ 4 * ∑ n ∈ Finset.Icc 1 x, t 2 n := by
    calc x * P.card = ∑ _p ∈ P, x := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ p ∈ P, 4 * ((x / p) * (p - 1)) := Finset.sum_le_sum hper
      _ = 4 * ∑ p ∈ P, (x / p) * (p - 1) := by rw [Finset.mul_sum]
      _ ≤ 4 * ∑ n ∈ Finset.Icc 1 x, t 2 n := by
          rw [hswap]; exact Nat.mul_le_mul_left _ (Finset.sum_le_sum hpt)
  calc x * Nat.primeCounting (x / 2) ≤ x * (P.card + s) := Nat.mul_le_mul_left _ hcard
    _ = x * P.card + x * s := by ring
    _ ≤ 4 * (∑ n ∈ Finset.Icc 1 x, t 2 n) + x * s := by omega

/-- The analytic core: for `x ≥ 10⁸` we have `x² / log x ≤ 20 · ∑_{n ≤ x} t₂(n)`.  Chebyshev's
lower bound `π(y) ≥ (y log 2 − log (y+1)) / log y` is applied at `y = x/2`. -/
private lemma key_real (x : ℕ) (hx : 10 ^ 8 ≤ x) :
    (x : ℝ) ^ 2 / Real.log x ≤ 20 * ∑ n ∈ Finset.Icc 1 x, (t 2 n : ℝ) := by
  have hX8 : (10:ℝ) ^ 8 ≤ (x : ℝ) := by exact_mod_cast hx
  set X : ℝ := (x : ℝ) with hXdef
  have hX0 : (0:ℝ) < X := lt_of_lt_of_le (by norm_num) hX8
  set u : ℝ := Real.sqrt (Real.sqrt X) with hudef
  have hsqX : Real.sqrt X = u ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg X)).symm
  have hXu : X = u ^ 4 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, ← hsqX, Real.sq_sqrt hX0.le]
  have hu : (100:ℝ) ≤ u := by
    rw [hudef, Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _),
      Real.le_sqrt (by norm_num) hX0.le]
    norm_num
    linarith
  have hu0 : (0:ℝ) < u := by linarith
  set L : ℝ := Real.log X with hLdef
  have hL0 : 0 < L := Real.log_pos (lt_of_lt_of_le (by norm_num) hX8)
  have hLu : L ≤ 4 * u := by
    rw [hLdef, hXu, Real.log_pow]
    have h1 : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu0
    push_cast
    linarith
  set m : ℕ := x / 2 with hmdef
  have hm2 : x ≤ 2 * m + 1 := by omega
  have hmx : m + 1 ≤ x := by omega
  have hmge : 2 ≤ m := by omega
  set M : ℝ := (m : ℝ) with hMdef
  have hM2 : X ≤ 2 * M + 1 := by rw [hXdef, hMdef]; exact_mod_cast hm2
  have hMX : M + 1 ≤ X := by rw [hXdef, hMdef]; exact_mod_cast hmx
  have hM2le : (2:ℝ) ≤ M := by rw [hMdef]; exact_mod_cast hmge
  have hlogM0 : 0 < Real.log M := Real.log_pos (by linarith)
  have hlogMX : Real.log M ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hpi0 : (0:ℝ) ≤ (Nat.primeCounting m : ℝ) := Nat.cast_nonneg _
  have hpi : (M * Real.log 2 - Real.log (M + 1)) / Real.log M ≤ (Nat.primeCounting m : ℝ) :=
    Chebyshev.pi_ge m
  rw [div_le_iff₀ hlogM0] at hpi
  have hnum : (X - 1) / 3 - L ≤ M * Real.log 2 - Real.log (M + 1) := by
    have h1 : Real.log (M + 1) ≤ L := Real.log_le_log (by linarith) hMX
    have h2 : (2:ℝ) / 3 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have h3 : M * (2 / 3) ≤ M * Real.log 2 := mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  have hpi3 : (X - 1) / 3 - L ≤ (Nat.primeCounting m : ℝ) * L :=
    hnum.trans (hpi.trans (mul_le_mul_of_nonneg_left hlogMX hpi0))
  have hkn := key_nat x (by omega)
  have hknR : X * (Nat.primeCounting m : ℝ)
      ≤ 4 * (∑ n ∈ Finset.Icc 1 x, (t 2 n : ℝ)) + X * (Nat.sqrt x : ℝ) := by
    rw [hXdef]
    exact_mod_cast hkn
  have hsq : (Nat.sqrt x : ℝ) ≤ u ^ 2 := by rw [← hsqX]; exact Real.nat_sqrt_le_real_sqrt
  set S : ℝ := ∑ n ∈ Finset.Icc 1 x, (t 2 n : ℝ) with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hknR' : X * (Nat.primeCounting m : ℝ) ≤ 4 * S + X * u ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq hX0.le
    linarith
  have hcore : X ≤ 5 * ((X - 1) / 3 - L) - 5 * u ^ 2 * L := by
    have hLu' : 5 * u ^ 2 * L ≤ 20 * u ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hLu (by positivity : (0:ℝ) ≤ 5 * u ^ 2)
      calc 5 * u ^ 2 * L ≤ 5 * u ^ 2 * (4 * u) := h
        _ = 20 * u ^ 3 := by ring
    have hc : (0:ℝ) ≤ u ^ 3 * (u - 100) := mul_nonneg (by positivity) (by linarith)
    have h4 : 100 * u ^ 3 ≤ u ^ 4 := by nlinarith
    have hd : (0:ℝ) ≤ u * (u ^ 2 - 1) := mul_nonneg (by linarith) (by nlinarith)
    have h5 : u ≤ u ^ 3 := by nlinarith
    have h6 : (1:ℝ) ≤ u ^ 3 := by nlinarith
    rw [hXu]
    linarith
  rw [div_le_iff₀ hL0]
  have s1 : X * X ≤ X * (5 * ((X - 1) / 3 - L) - 5 * u ^ 2 * L) :=
    mul_le_mul_of_nonneg_left hcore hX0.le
  have s2 : X * ((X - 1) / 3 - L) ≤ X * ((Nat.primeCounting m : ℝ) * L) :=
    mul_le_mul_of_nonneg_left hpi3 hX0.le
  have s3 : X * (Nat.primeCounting m : ℝ) * L ≤ (4 * S + X * u ^ 2) * L :=
    mul_le_mul_of_nonneg_right hknR' hL0.le
  nlinarith [s1, s2, s3]

end Erdos394

/-- `t₂(p) = p − 1` for every prime `p`. -/
theorem t_two_prime (p : ℕ) (hp : p.Prime) : t 2 p = p - 1 := by
  have h2 := hp.two_le
  refine le_antisymm ?_ (Erdos394.sub_one_le_t_two hp dvd_rfl (by omega))
  refine Erdos394.t_two_le (by omega) ?_
  have hpp : p - 1 + 1 = p := by omega
  rw [hpp]
  exact dvd_mul_left p (p - 1)

/-- **Erdős #394, the trivial lower bound.**  `x² / log x ≪ ∑_{n ≤ x} t₂(n)`, in the exact shape
of the formal-conjectures statement `erdos_394.variants.lower_bound` (with `≪` unfolded to
`IsBigO atTop` on `ℕ → ℝ`).  The open questions are not claimed. -/
theorem erdos_394_lower_bound :
    Asymptotics.IsBigO Filter.atTop ((fun x ↦ x ^ 2 / Real.log x) : ℕ → ℝ)
      ((fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, (t 2 n : ℝ)) : ℕ → ℝ) := by
  refine Asymptotics.IsBigO.of_bound 20 ?_
  filter_upwards [Filter.eventually_ge_atTop (10 ^ 8)] with x hx
  have hfl : (⌊x⌋₊ : ℕ) = x := by simp
  rw [hfl]
  have hX8 : (10:ℝ) ^ 8 ≤ (x : ℝ) := by exact_mod_cast hx
  have hL0 : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le (by norm_num) hX8)
  have hS0 : (0:ℝ) ≤ ∑ n ∈ Finset.Icc 1 x, (t 2 n : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hf0 : (0:ℝ) ≤ (x : ℝ) ^ 2 / Real.log x := div_nonneg (sq_nonneg _) hL0.le
  rw [Real.norm_of_nonneg hf0, Real.norm_of_nonneg hS0]
  exact Erdos394.key_real x hx
