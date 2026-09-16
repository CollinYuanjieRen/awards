import Mathlib
import Proof.Defs

/-!
# Arithmetic of the Selfridge–Straus coefficients

`acoef n j m = ∑_{c=1}^{m} (-1)^(c-1) c^(j-1) C(n, m-c)` satisfies the Newton-type recursion
`m · acoef n j m = ∑_{i=1}^{m} (-1)^(i-1) (C(n, m-i) i^j + n · acoef n j (m-i))` (for `j ≥ 1`),
equals `n - 2^(j-1)` for `m = 2`, and is a unit modulo a prime `p` with `p ∣ n` and `m < p`,
because `C(n, r) ≡ 0 (mod p)` for `0 < r < p`.
-/

open Finset

namespace Erdos494

/-- Absorption identity for the alternating partial sums of binomial coefficients, in
`Finset.range` form: `n · ∑_{t<r} (-1)^t C(n, r-1-t) = r · C(n, r)`. -/
private lemma mul_alternating_sum_choose_range (n r : ℕ) :
    (n : ℤ) * ∑ t ∈ Finset.range r, (-1 : ℤ) ^ t * (n.choose (r - 1 - t) : ℤ) =
      (r : ℤ) * (n.choose r : ℤ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hstep : ∑ t ∈ Finset.range (r + 1), (-1 : ℤ) ^ t * (n.choose (r + 1 - 1 - t) : ℤ) =
        (n.choose r : ℤ) - ∑ t ∈ Finset.range r, (-1 : ℤ) ^ t * (n.choose (r - 1 - t) : ℤ) := by
      rw [Finset.sum_range_succ']
      have h : ∀ t ∈ Finset.range r,
          (-1 : ℤ) ^ (t + 1) * (n.choose (r + 1 - 1 - (t + 1)) : ℤ) =
            -((-1 : ℤ) ^ t * (n.choose (r - 1 - t) : ℤ)) := by
        intro t _
        have h1 : r + 1 - 1 - (t + 1) = r - 1 - t := by omega
        rw [h1, pow_succ]
        ring
      rw [Finset.sum_congr rfl h, Finset.sum_neg_distrib]
      simp only [pow_zero, one_mul, Nat.add_sub_cancel, Nat.sub_zero]
      ring
    rw [hstep, mul_sub, ih]
    rcases le_or_gt r n with h | h
    · have hc : (n.choose (r + 1) : ℤ) * ((r : ℤ) + 1) =
          (n.choose r : ℤ) * ((n : ℤ) - (r : ℤ)) := by
        have h0 : ((n.choose (r + 1) * (r + 1) : ℕ) : ℤ) = ((n.choose r * (n - r) : ℕ) : ℤ) := by
          exact_mod_cast congrArg (fun x : ℕ => (x : ℤ)) (Nat.choose_succ_right_eq n r)
        push_cast [Nat.cast_sub h] at h0
        linarith
      push_cast
      linarith
    · have h1 : n.choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have h2 : n.choose r = 0 := Nat.choose_eq_zero_of_lt h
      rw [h1, h2]
      push_cast
      ring

/-- Absorption identity for the alternating partial sums of binomial coefficients:
`n · ∑_{i=1}^{r} (-1)^(i-1) C(n, r-i) = r · C(n, r)`. -/
private lemma mul_alternating_sum_choose (n r : ℕ) :
    (n : ℤ) * ∑ i ∈ Finset.Icc 1 r, (-1 : ℤ) ^ (i - 1) * (n.choose (r - i) : ℤ) =
      (r : ℤ) * (n.choose r : ℤ) := by
  have hset : Finset.Icc 1 r = Finset.Ico 1 (r + 1) := by
    ext x
    simp
  have hsum : ∑ i ∈ Finset.Icc 1 r, (-1 : ℤ) ^ (i - 1) * (n.choose (r - i) : ℤ) =
      ∑ t ∈ Finset.range r, (-1 : ℤ) ^ t * (n.choose (r - 1 - t) : ℤ) := by
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h1 : 1 + t - 1 = t := by omega
    have h2 : r - (1 + t) = r - 1 - t := by omega
    rw [h1, h2]
  rw [hsum, mul_alternating_sum_choose_range]

/-- The Newton-type recursion satisfied by the closed form `acoef`. -/
theorem acoef_recursion (n j m : ℕ) (hj : 1 ≤ j) :
    (m : ℤ) * acoef n j m =
      ∑ i ∈ Finset.Icc 1 m,
        (-1 : ℤ) ^ (i - 1) * ((n.choose (m - i) : ℤ) * (i : ℤ) ^ j + (n : ℤ) * acoef n j (m - i)) := by
  simp only [acoef]
  have hsplit : ∀ i ∈ Finset.Icc 1 m,
      (-1 : ℤ) ^ (i - 1) * ((n.choose (m - i) : ℤ) * (i : ℤ) ^ j +
          (n : ℤ) * ∑ c ∈ Finset.Icc 1 (m - i),
            (-1 : ℤ) ^ (c - 1) * (c : ℤ) ^ (j - 1) * (n.choose (m - i - c) : ℤ)) =
        (-1 : ℤ) ^ (i - 1) * ((n.choose (m - i) : ℤ) * (i : ℤ) ^ j) +
          ∑ c ∈ Finset.Icc 1 (m - i), (-1 : ℤ) ^ (i - 1) *
            ((n : ℤ) * ((-1 : ℤ) ^ (c - 1) * (c : ℤ) ^ (j - 1) * (n.choose (m - i - c) : ℤ))) := by
    intro i _
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  have hcomm : ∀ x y : ℕ, x ∈ Finset.Icc 1 m ∧ y ∈ Finset.Icc 1 (m - x) ↔
      x ∈ Finset.Icc 1 (m - y) ∧ y ∈ Finset.Icc 1 m := by
    intro x y
    simp only [Finset.mem_Icc]
    omega
  have hinner : ∀ c ∈ Finset.Icc 1 m,
      ∑ i ∈ Finset.Icc 1 (m - c), (-1 : ℤ) ^ (i - 1) *
          ((n : ℤ) * ((-1 : ℤ) ^ (c - 1) * (c : ℤ) ^ (j - 1) * (n.choose (m - i - c) : ℤ))) =
        (-1 : ℤ) ^ (c - 1) * (c : ℤ) ^ (j - 1) * (((m - c : ℕ) : ℤ) * (n.choose (m - c) : ℤ)) := by
    intro c _
    have h1 : ∑ i ∈ Finset.Icc 1 (m - c), (-1 : ℤ) ^ (i - 1) *
          ((n : ℤ) * ((-1 : ℤ) ^ (c - 1) * (c : ℤ) ^ (j - 1) * (n.choose (m - i - c) : ℤ))) =
        (-1 : ℤ) ^ (c - 1) * (c : ℤ) ^ (j - 1) *
          ((n : ℤ) * ∑ i ∈ Finset.Icc 1 (m - c),
            (-1 : ℤ) ^ (i - 1) * (n.choose (m - c - i) : ℤ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h2 : m - i - c = m - c - i := by omega
      rw [h2]
      ring
    rw [h1, mul_alternating_sum_choose]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_comm' hcomm,
    Finset.sum_congr rfl hinner, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Finset.mem_Icc] at hc
  have hcm : ((m - c : ℕ) : ℤ) = (m : ℤ) - (c : ℤ) := by
    have := hc.2
    push_cast [Nat.cast_sub this]
    ring
  have hpow : (c : ℤ) ^ j = (c : ℤ) ^ (j - 1) * (c : ℤ) := by
    conv_lhs => rw [show j = j - 1 + 1 by omega]
    rw [pow_succ]
  rw [hcm, hpow]
  ring

theorem acoef_two (n j : ℕ) (_hj : 1 ≤ j) : acoef n j 2 = (n : ℤ) - 2 ^ (j - 1) := by
  have hset : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [acoef, hset, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  norm_num
  ring

theorem acoef_two_ne_zero (n j : ℕ) (hj : 1 ≤ j) (hn : ∀ l : ℕ, n ≠ 2 ^ l) : acoef n j 2 ≠ 0 := by
  rw [acoef_two n j hj]
  intro h
  have h1 : (n : ℤ) = ((2 ^ (j - 1) : ℕ) : ℤ) := by
    push_cast
    linarith
  exact hn (j - 1) (by exact_mod_cast h1)

/-- `p ∣ C(n, r)` whenever `p` is prime, `p ∣ n` and `0 < r < p`. -/
theorem prime_dvd_choose_of_dvd {p n r : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hr0 : 0 < r)
    (hrp : r < p) : p ∣ n.choose r := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Nat.choose_eq_zero_of_lt hr0]
    exact dvd_zero p
  · obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr0.ne'
    have hdvd : p ∣ (N + 1).choose (k + 1) * (k + 1) := by
      rw [← Nat.add_one_mul_choose_eq]
      exact hpn.mul_right _
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact h
    · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)

theorem acoef_ne_zero_of_prime {p n m j : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hm0 : 1 ≤ m)
    (hmp : m < p) (_hj : 1 ≤ j) : acoef n j m ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hval : ((acoef n j m : ℤ) : ZMod p) = (-1 : ZMod p) ^ (m - 1) * (m : ZMod p) ^ (j - 1) := by
    rw [acoef]
    push_cast
    rw [Finset.sum_eq_single m]
    · simp
    · intro b hb hbm
      rw [Finset.mem_Icc] at hb
      have hz : ((n.choose (m - b) : ℕ) : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact prime_dvd_choose_of_dvd hp hpn (by omega) (by omega)
      rw [hz, mul_zero]
    · intro hb
      exact absurd (Finset.mem_Icc.mpr ⟨hm0, le_rfl⟩) hb
  have hne : ((acoef n j m : ℤ) : ZMod p) ≠ 0 := by
    rw [hval]
    refine mul_ne_zero (pow_ne_zero _ (by simp)) (pow_ne_zero _ ?_)
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) hmp
  intro h
  rw [h] at hne
  simp at hne

end Erdos494
