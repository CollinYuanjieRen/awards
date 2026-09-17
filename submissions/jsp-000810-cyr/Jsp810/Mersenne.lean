import Mathlib

/-!
# Schinzel's prime-factor lower bound for Mersenne numbers with prime exponent

For an odd prime `p`, every prime `q` dividing `2 ^ p - 1` satisfies `q ≡ 1 (mod 2p)`, hence
`2 * p + 1 ≤ q`.  Consequently the greatest prime factor of `2 ^ p - 1` is `≥ 2 * p + 1`.

This is the clean order-argument special case of Schinzel's (1962) bound `P(2^n - 1) > 2n`
(here restricted to prime exponents, where the argument is elementary).
-/

namespace Erdos977

/-- For an odd prime exponent `p ≥ 3` we have `1 < 2 ^ p - 1` (indeed `2 ^ p - 1 ≥ 7`). -/
private theorem one_lt_two_pow_sub_one {p : ℕ} (hp : 3 ≤ p) : 1 < 2 ^ p - 1 := by
  have h8 : (8 : ℕ) ≤ 2 ^ p := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
  omega

/-- An odd prime `p` satisfies `3 ≤ p`. -/
private theorem three_le_of_odd_prime {p : ℕ} (hp : p.Prime) (hodd : Odd p) : 3 ≤ p := by
  have hp2 : p ≠ 2 := by rintro rfl; exact absurd hodd (by decide)
  have := hp.two_le
  omega

/-- For an odd prime `p`, every prime `q` dividing `2^p - 1` satisfies `2*p + 1 ≤ q`
(indeed `q ≡ 1 mod 2p`). -/
theorem two_mul_add_one_le_of_prime_dvd {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {q : ℕ} (hq : q.Prime) (hqd : q ∣ 2 ^ p - 1) : 2 * p + 1 ≤ q := by
  have : Fact q.Prime := ⟨hq⟩
  have hp0 : p ≠ 0 := hp.pos.ne'
  -- `q` cannot be `2`, because `2 ^ p - 1` is odd.
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨a, ha⟩ := (dvd_pow_self 2 hp0 : (2 : ℕ) ∣ 2 ^ p)
    obtain ⟨b, hb⟩ := hqd
    have hpos : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by norm_num)
    omega
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have : NeZero q := ⟨by omega⟩
  -- `(2 : ZMod q) ≠ 0`.
  have h2ne : (2 : ZMod q) ≠ 0 := by
    have hcast : ((2 : ℕ) : ZMod q) = (2 : ZMod q) := by push_cast; ring
    rw [← hcast, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  -- From `q ∣ 2 ^ p - 1` we get `(2 : ZMod q) ^ p = 1`.
  have hpow : (2 : ZMod q) ^ p = 1 := by
    have hz : ((2 ^ p - 1 : ℕ) : ZMod q) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact hqd
    rw [Nat.cast_sub (Nat.one_le_pow p 2 (by norm_num))] at hz
    push_cast at hz
    exact eq_of_sub_eq_zero hz
  -- The order of `2` divides `p`, and is not `1`, so it equals `p`.
  have hd_dvd_p : orderOf (2 : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one hpow
  have hd_ne_one : orderOf (2 : ZMod q) ≠ 1 := by
    intro h1
    have h2eq1 : (2 : ZMod q) = 1 := orderOf_eq_one_iff.mp h1
    exact one_ne_zero (show (1 : ZMod q) = 0 by linear_combination h2eq1)
  have hd_eq_p : orderOf (2 : ZMod q) = p :=
    (hp.eq_one_or_self_of_dvd _ hd_dvd_p).resolve_left hd_ne_one
  -- Fermat's little theorem: `p = orderOf 2 ∣ q - 1`.
  have hp_dvd : p ∣ q - 1 := by
    rw [← hd_eq_p]
    exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2ne)
  -- `q` is odd, so `2 ∣ q - 1`.
  have h2_dvd : 2 ∣ q - 1 := by
    obtain ⟨k, hk⟩ := hq.odd_of_ne_two hq2
    omega
  -- `2` and `p` are coprime, so `2 * p ∣ q - 1`.
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hodd
  have hmul : 2 * p ∣ q - 1 := hcop.mul_dvd_of_dvd_of_dvd h2_dvd hp_dvd
  have hle : 2 * p ≤ q - 1 := Nat.le_of_dvd (by omega) hmul
  omega

/-- Consequently, for an odd prime `p`, the greatest prime factor `P(2^p - 1) ≥ 2 * p + 1`. -/
theorem two_mul_add_one_le_greatestPrimeFactor {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    2 * p + 1 ≤ (2 ^ p - 1).primeFactors.max'
      (Nat.nonempty_primeFactors.mpr (one_lt_two_pow_sub_one (three_le_of_odd_prime hp hodd))) := by
  have hne : (2 ^ p - 1).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr (one_lt_two_pow_sub_one (three_le_of_odd_prime hp hodd))
  have hx_mem := (2 ^ p - 1).primeFactors.max'_mem hne
  have hx_prime := Nat.prime_of_mem_primeFactors hx_mem
  have hx_dvd := Nat.dvd_of_mem_primeFactors hx_mem
  exact two_mul_add_one_le_of_prime_dvd hp hodd hx_prime hx_dvd

#print axioms two_mul_add_one_le_of_prime_dvd
#print axioms two_mul_add_one_le_greatestPrimeFactor

end Erdos977
