import Erdos673Divisors.Definitions

/-!
# Erdős Problem 673 — basic properties of `G`

Elementary facts about `nextDiv` and `G`, culminating in Tao's sandwich
`τ(n/m)/m ≤ G(n) ≤ τ(n)` and the lower bound `τ(n)/(2p) ≤ G(n)` for a prime `p ∣ n`.
-/

namespace Erdos673

open Finset

/-! ### The next divisor -/

/-- For `d < n` with `0 < n`, the set of divisors of `n` exceeding `d` is nonempty. -/
theorem nextDiv_set_nonempty {n d : ℕ} (hd : d < n) :
    {e : ℕ | e ∣ n ∧ d < e}.Nonempty :=
  ⟨n, dvd_rfl, hd⟩

-- `hn` is kept so that the frozen lemmas below can pass it on verbatim.
set_option linter.unusedVariables false in
theorem nextDiv_spec {n d : ℕ} (hn : 0 < n) (hd : d < n) :
    nextDiv n d ∣ n ∧ d < nextDiv n d :=
  Nat.sInf_mem (nextDiv_set_nonempty hd)

theorem nextDiv_dvd {n d : ℕ} (hn : 0 < n) (hd : d < n) : nextDiv n d ∣ n :=
  (nextDiv_spec hn hd).1

theorem lt_nextDiv {n d : ℕ} (hn : 0 < n) (hd : d < n) : d < nextDiv n d :=
  (nextDiv_spec hn hd).2

theorem nextDiv_le {n d e : ℕ} (he : e ∣ n) (hde : d < e) : nextDiv n d ≤ e :=
  Nat.sInf_le ⟨he, hde⟩

theorem nextDiv_pos {n d : ℕ} (hn : 0 < n) (hd : d < n) : 0 < nextDiv n d :=
  Nat.lt_of_le_of_lt (Nat.zero_le d) (lt_nextDiv hn hd)

/-- A divisor of `n` other than `n` itself is smaller than `n`. -/
theorem lt_of_mem_erase {n d : ℕ} (hd : d ∈ (Nat.divisors n).erase n) : d < n := by
  rw [Finset.mem_erase, Nat.mem_divisors] at hd
  exact lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2.2) hd.2.1) hd.1

/-! ### Elementary bounds on `G` -/

theorem G_nonneg (n : ℕ) : 0 ≤ G n := by
  refine Finset.sum_nonneg fun d _ => ?_
  positivity

theorem G_le_card_divisors (n : ℕ) : G n ≤ (Nat.divisors n).card := by
  have hcard : ((Nat.divisors n).erase n).card ≤ (Nat.divisors n).card :=
    Finset.card_erase_le
  have hterm : ∀ d ∈ (Nat.divisors n).erase n, (d : ℝ) / nextDiv n d ≤ 1 := by
    intro d hd
    have hdn : d < n := lt_of_mem_erase hd
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le d) hdn
    have h1 : d < nextDiv n d := lt_nextDiv hn hdn
    have h2 : (0 : ℝ) < (nextDiv n d : ℝ) := by
      exact_mod_cast nextDiv_pos hn hdn
    rw [div_le_one h2]
    exact_mod_cast h1.le
  have := Finset.sum_le_card_nsmul ((Nat.divisors n).erase n)
    (fun d => (d : ℝ) / nextDiv n d) 1 hterm
  simp only [nsmul_eq_mul, mul_one] at this
  refine this.trans ?_
  exact_mod_cast hcard

/-! ### The lower bound `τ(n/m)/m ≤ G n` -/

theorem card_divisors_div_le_mul_G {n m : ℕ} (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n) :
    ((Nat.divisors (n / m)).card : ℝ) / m ≤ G n := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  have hdivpos : 0 < n / m := Nat.div_pos (Nat.le_of_dvd hn hmn) hm0
  have hdivlt : n / m < n := Nat.div_lt_self hn hm
  -- the divisors of `n / m` sit inside `(divisors n).erase n`
  have hsub : Nat.divisors (n / m) ⊆ (Nat.divisors n).erase n := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    have hdvd : d ∣ n := hd.1.trans (Nat.div_dvd_of_dvd hmn)
    have hdle : d ≤ n / m := Nat.le_of_dvd hdivpos hd.1
    have hdlt : d < n := lt_of_le_of_lt hdle hdivlt
    exact Finset.mem_erase.mpr ⟨ne_of_lt hdlt, Nat.mem_divisors.mpr ⟨hdvd, hn.ne'⟩⟩
  -- on that subset each term is at least `1 / m`
  have hterm : ∀ d ∈ Nat.divisors (n / m), (1 : ℝ) / m ≤ (d : ℝ) / nextDiv n d := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1 hdivpos
    have hdle : d ≤ n / m := Nat.le_of_dvd hdivpos hd.1
    have hdlt : d < n := lt_of_le_of_lt hdle hdivlt
    have hdm : d * m ∣ n := by
      have : d * m ∣ (n / m) * m := mul_dvd_mul_right hd.1 m
      rwa [Nat.div_mul_cancel hmn] at this
    have hlt : d < d * m := by nlinarith
    have hnext : nextDiv n d ≤ d * m := nextDiv_le hdm hlt
    have hnextpos : (0 : ℝ) < (nextDiv n d : ℝ) := by
      exact_mod_cast nextDiv_pos (lt_of_le_of_lt (Nat.zero_le d) hdlt) hdlt
    have hd0' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have key : (d : ℝ) / (d * m) ≤ (d : ℝ) / nextDiv n d := by
      refine div_le_div_of_nonneg_left hd0'.le hnextpos ?_
      exact_mod_cast hnext
    have heq : (d : ℝ) / ((d : ℝ) * (m : ℝ)) = 1 / m := by
      rw [← div_div, div_self hd0'.ne']
    rwa [heq] at key
  calc ((Nat.divisors (n / m)).card : ℝ) / m
      = ∑ _d ∈ Nat.divisors (n / m), (1 : ℝ) / m := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ d ∈ Nat.divisors (n / m), (d : ℝ) / nextDiv n d :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ d ∈ (Nat.divisors n).erase n, (d : ℝ) / nextDiv n d := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro d _ _
        positivity
    _ = G n := rfl

/-! ### Halving a prime factor -/

/-- **Note.** The statement frozen in `design.md` carried only `hp : p ∣ n`, which is false
(`n = 12`, `p = 6`: `τ(12) = 6 > 4 = 2 * τ(2)`).  As in §(3) of the design's mathematics
section, `p` must be prime. -/
theorem card_divisors_le_two_mul {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n) :
    (Nat.divisors n).card ≤ 2 * (Nat.divisors (n / p)).card := by
  classical
  have hsub : Nat.divisors n ⊆
      Nat.divisors (n / p) ∪ (Nat.divisors (n / p)).image (· * p) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    by_cases hpd : p ∣ d
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_image.mpr ⟨d / p, ?_, Nat.div_mul_cancel hpd⟩
      refine Nat.mem_divisors.mpr ⟨?_, ?_⟩
      · rw [Nat.dvd_div_iff_mul_dvd hpn, Nat.mul_div_cancel' hpd]
        exact hd.1
      · exact Nat.div_ne_zero_iff.mpr ⟨hp.pos.ne', Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn⟩
    · refine Finset.mem_union_left _ ?_
      refine Nat.mem_divisors.mpr ⟨?_, ?_⟩
      · rw [Nat.dvd_div_iff_mul_dvd hpn]
        exact (hp.coprime_iff_not_dvd.mpr hpd).mul_dvd_of_dvd_of_dvd hpn hd.1
      · exact Nat.div_ne_zero_iff.mpr ⟨hp.pos.ne', Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn⟩
  calc (Nat.divisors n).card
      ≤ (Nat.divisors (n / p) ∪ (Nat.divisors (n / p)).image (· * p)).card :=
        Finset.card_le_card hsub
    _ ≤ (Nat.divisors (n / p)).card + ((Nat.divisors (n / p)).image (· * p)).card :=
        Finset.card_union_le _ _
    _ ≤ (Nat.divisors (n / p)).card + (Nat.divisors (n / p)).card :=
        Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * (Nat.divisors (n / p)).card := by ring

theorem card_divisors_le_mul_G {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) :
    ((Nat.divisors n).card : ℝ) / (2 * p) ≤ G n := by
  have hp1 : 1 < p := hp.one_lt
  have hstep := card_divisors_div_le_mul_G hn hp1 hpn
  have hcard : ((Nat.divisors n).card : ℝ) ≤ 2 * ((Nat.divisors (n / p)).card : ℝ) := by
    exact_mod_cast card_divisors_le_two_mul hn.ne' hp hpn
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  calc ((Nat.divisors n).card : ℝ) / (2 * p)
      ≤ (2 * ((Nat.divisors (n / p)).card : ℝ)) / (2 * p) := by
        apply div_le_div_of_nonneg_right hcard
        positivity
    _ = ((Nat.divisors (n / p)).card : ℝ) / p := by
        rw [mul_div_mul_left _ _ (two_ne_zero)]
    _ ≤ G n := hstep

/-! ### Many divisors from many prime factors -/

/-- `2 ^ #(Q ∩ divisors n) ≤ τ(n)` for a finset of primes `Q`. -/
theorem two_pow_le_card_divisors {n : ℕ} (hn : n ≠ 0) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    2 ^ (Q.filter (· ∣ n)).card ≤ (Nat.divisors n).card := by
  classical
  set R := Q.filter (· ∣ n) with hR
  have hRprime : ∀ p ∈ R, p.Prime := fun p hp => hQ p (Finset.mem_filter.mp hp).1
  have hRdvd : ∀ p ∈ R, p ∣ n := fun p hp => (Finset.mem_filter.mp hp).2
  have hmaps : Set.MapsTo (fun s : Finset ℕ => ∏ p ∈ s, p) ↑R.powerset ↑(Nat.divisors n) := by
    intro s hs
    have hsR : s ⊆ R := Finset.mem_powerset.mp (by exact_mod_cast hs)
    refine Finset.mem_coe.mpr (Nat.mem_divisors.mpr ⟨?_, hn⟩)
    exact Finset.prod_primes_dvd n (fun a ha => (hRprime a (hsR ha)).prime)
      (fun a ha => hRdvd a (hsR ha))
  have hinj : Set.InjOn (fun s : Finset ℕ => ∏ p ∈ s, p) ↑R.powerset := by
    intro s hs t ht hst
    have hsR : s ⊆ R := Finset.mem_powerset.mp (by exact_mod_cast hs)
    have htR : t ⊆ R := Finset.mem_powerset.mp (by exact_mod_cast ht)
    have hs' : (∏ p ∈ s, p).primeFactors = s :=
      Nat.primeFactors_prod (fun a ha => hRprime a (hsR ha))
    have ht' : (∏ p ∈ t, p).primeFactors = t :=
      Nat.primeFactors_prod (fun a ha => hRprime a (htR ha))
    have hst' : (∏ p ∈ s, p) = ∏ p ∈ t, p := hst
    rw [← hs', ← ht', hst']
  have := Finset.card_le_card_of_injOn (fun s : Finset ℕ => ∏ p ∈ s, p) hmaps hinj
  rwa [Finset.card_powerset] at this

theorem card_divisors_le_card_divisors_two_mul (k : ℕ) :
    (Nat.divisors k).card ≤ (Nat.divisors (2 * k)).card := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · exact Finset.card_le_card
      (Nat.divisors_subset_of_dvd (by positivity) (dvd_mul_left k 2))

end Erdos673
