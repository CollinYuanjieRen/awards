import Mathlib

/-!
# Erdős Problem #479: the known cases `k = 2^i`, `k = −1`, `k = 0` of Graham's conjecture

Graham conjectured that for every integer `k ≠ 1` there are infinitely many `n` with
`2^n ≡ k (mod n)`.  The conjecture is OPEN (for `k = 3` the least such `n` is `4700063497`).
Erdős and Graham report that Graham, Lehmer and Lehmer proved it for `k = 2^i` (`i ≥ 1`) and for
`k = −1`; Tang's note "A note on Erdős Problem #479" (2025) gives proofs.  This file proves
exactly these known cases, in the shape of the formal-conjectures statement `Erdos479.erdos_479`
(`{ n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] }.Infinite`):

* `k = 2^i`, `i ≥ 1`: for a prime `p > i` with `p ≡ 1 (mod φ(i))` (Dirichlet), `n = i p` works;
* `k = −1`: `n = 3^m` works for every `m` (`3^{m+1} ∣ 2^{3^m} + 1`);
* `k = 0`: `n = 2^m` works (trivially).

Nothing is claimed for any other `k`.
-/

/-- The set of `n` with `2^n ≡ k (mod n)`, as in the formal-conjectures statement. -/
def grahamSet (k : ℤ) : Set ℕ := { n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] }

namespace Erdos479Aux

/-- A set of naturals containing, for every bound, a larger element is infinite. -/
theorem infinite_of_forall_exists_gt {S : Set ℕ} (h : ∀ N : ℕ, ∃ n ∈ S, N < n) :
    S.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rw [not_bddAbove_iff]
  exact h

/-- Transfer of a natural divisibility `n ∣ 2^a - 2^b` (with `b ≤ a`) into the integer
congruence `2^a ≡ 2^b (mod n)`. -/
theorem int_pow_modEq_of_nat_dvd {n a b : ℕ} (hab : b ≤ a) (h : n ∣ 2 ^ a - 2 ^ b) :
    (2 : ℤ) ^ a ≡ 2 ^ b [ZMOD (n : ℤ)] := by
  have h2 : (2 : ℕ) ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hab
  have hz : (n : ℤ) ∣ (2 : ℤ) ^ a - (2 : ℤ) ^ b := by
    have hc := Int.natCast_dvd_natCast.mpr h
    rw [Nat.cast_sub h2] at hc
    push_cast at hc
    exact hc
  exact Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp hz)

/-- The classical divisibility `3^{m+1} ∣ 2^{3^m} + 1`, by induction on `m`. -/
theorem three_pow_dvd (m : ℕ) : (3 : ℤ) ^ (m + 1) ∣ 2 ^ (3 ^ m) + 1 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hcube : (2 : ℤ) ^ (3 ^ (m + 1)) = ((2 : ℤ) ^ (3 ^ m)) ^ 3 := by
      rw [← pow_mul, pow_succ]
    set a : ℤ := (2 : ℤ) ^ (3 ^ m) with ha
    obtain ⟨t, ht⟩ := ih
    have h3 : (3 : ℤ) ∣ a ^ 2 - a + 1 := by
      refine ⟨3 * (3 ^ m * t) ^ 2 - 3 * (3 ^ m * t) + 1, ?_⟩
      have haval : a = 3 * (3 ^ m * t) - 1 := by
        have : a + 1 = 3 * (3 ^ m * t) := by rw [ht, pow_succ]; ring
        linarith
      rw [haval]; ring
    have hmul : (3 : ℤ) ^ (m + 1) * 3 ∣ (a + 1) * (a ^ 2 - a + 1) := mul_dvd_mul ⟨t, ht⟩ h3
    rw [hcube, show a ^ 3 + 1 = (a + 1) * (a ^ 2 - a + 1) by ring, pow_succ]
    exact hmul

/-- Fermat's little theorem in the form `2^p ≡ 2 (mod p)`, valid for every prime `p`. -/
theorem two_pow_prime_modEq {p : ℕ} (hp : Nat.Prime p) : 2 ^ p ≡ 2 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  refine (ZMod.natCast_eq_natCast_iff (2 ^ p) 2 p).mp ?_
  push_cast
  exact ZMod.pow_card (2 : ZMod p)

end Erdos479Aux

open Erdos479Aux

/-- `k = 2^i` with `i ≥ 1`: infinitely many `n` with `2^n ≡ 2^i (mod n)` (Graham–Lehmer–Lehmer;
Tang, Theorem 3.1). -/
theorem erdos_479_two_pow (i : ℕ) (hi : 1 ≤ i) :
    { n : ℕ | (2 : ℤ) ^ n ≡ 2 ^ i [ZMOD (n : ℤ)] }.Infinite := by
  refine infinite_of_forall_exists_gt ?_
  intro N
  have hipos : 0 < i := hi
  have htot : Nat.totient i ≠ 0 := (Nat.totient_pos.mpr hipos).ne'
  obtain ⟨p, hpgt, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N i) htot (Nat.coprime_one_left (Nat.totient i))
  have hpN : N < p := lt_of_le_of_lt (le_max_left N i) hpgt
  have hpi : i < p := lt_of_le_of_lt (le_max_right N i) hpgt
  have hppos : 0 < p := hp.pos
  -- `n := i * p`
  refine ⟨i * p, ?_, ?_⟩
  · -- membership: `2^(i*p) ≡ 2^i (mod i*p)`
    show (2 : ℤ) ^ (i * p) ≡ 2 ^ i [ZMOD ((i * p : ℕ) : ℤ)]
    have hile : i ≤ i * p := Nat.le_mul_of_pos_right i hppos
    -- the `p`-part
    have hpart_p : p ∣ 2 ^ (i * p) - 2 ^ i := by
      have h1 : (2 : ℕ) ^ (i * p) = (2 ^ p) ^ i := by
        rw [← pow_mul, Nat.mul_comm]
      have h2 : (2 : ℕ) ^ (i * p) ≡ 2 ^ i [MOD p] := by
        rw [h1]
        exact (two_pow_prime_modEq hp).pow i
      exact (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) hile)).mp h2.symm
    -- the `i`-part
    have hpart_i : i ∣ 2 ^ (i * p) - 2 ^ i := by
      obtain ⟨s, m, hm, hism⟩ := Nat.exists_eq_two_pow_mul_odd (n := i) hipos.ne'
      have hmpos : 0 < m := hm.pos
      have hsi : s ≤ i := by
        have h1 : s < 2 ^ s := Nat.lt_two_pow_self
        have h2 : 2 ^ s ≤ 2 ^ s * m := Nat.le_mul_of_pos_right _ hmpos
        omega
      have hcop2m : Nat.Coprime (2 ^ s) m := Nat.Coprime.pow_left s (Nat.coprime_two_left.mpr hm)
      -- the `2^s`-part
      have hdvd2 : 2 ^ s ∣ 2 ^ (i * p) - 2 ^ i :=
        Nat.dvd_sub (pow_dvd_pow 2 (hsi.trans hile)) (pow_dvd_pow 2 hsi)
      -- the odd part
      have hdvdm : m ∣ 2 ^ (i * p) - 2 ^ i := by
        have hsplit : (2 : ℕ) ^ (i * p) - 2 ^ i = 2 ^ i * (2 ^ (i * (p - 1)) - 1) := by
          have hip : i * p = i + i * (p - 1) := by
            have hp1 : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hppos
            calc i * p = i * (p - 1 + 1) := by rw [hp1]
              _ = i + i * (p - 1) := by ring
          rw [Nat.mul_sub, ← pow_add, Nat.mul_one, ← hip]
        have htotdvd : Nat.totient m ∣ Nat.totient i := by
          rw [hism, Nat.totient_mul hcop2m]
          exact Dvd.intro_left _ rfl
        have hqdvd : Nat.totient i ∣ p - 1 :=
          (Nat.modEq_iff_dvd' hp.one_lt.le).mp hpmod.symm
        have hdvdexp : Nat.totient m ∣ i * (p - 1) :=
          Dvd.dvd.mul_left (htotdvd.trans hqdvd) i
        obtain ⟨u, hu⟩ := hdvdexp
        have heuler : (2 : ℕ) ^ Nat.totient m ≡ 1 [MOD m] :=
          Nat.ModEq.pow_totient (Nat.coprime_two_left.mpr hm)
        have hone : (2 : ℕ) ^ (i * (p - 1)) ≡ 1 [MOD m] := by
          calc (2 : ℕ) ^ (i * (p - 1)) = (2 ^ Nat.totient m) ^ u := by rw [hu, pow_mul]
            _ ≡ 1 ^ u [MOD m] := heuler.pow u
            _ = 1 := one_pow u
        have : m ∣ 2 ^ (i * (p - 1)) - 1 :=
          (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hone.symm
        rw [hsplit]
        exact this.mul_left _
      have hcomb : 2 ^ s * m ∣ 2 ^ (i * p) - 2 ^ i :=
        hcop2m.mul_dvd_of_dvd_of_dvd hdvd2 hdvdm
      rwa [← hism] at hcomb
    have hcop : Nat.Coprime i p :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (Nat.not_dvd_of_pos_of_lt hipos hpi)))
    exact int_pow_modEq_of_nat_dvd hile (hcop.mul_dvd_of_dvd_of_dvd hpart_i hpart_p)
  · have hle : 1 * p ≤ i * p := Nat.mul_le_mul_right p hi
    omega

/-- `k = −1`: `2^{3^m} ≡ −1 (mod 3^m)` for every `m`, so infinitely many `n`. -/
theorem erdos_479_neg_one : { n : ℕ | (2 : ℤ) ^ n ≡ -1 [ZMOD (n : ℤ)] }.Infinite := by
  refine infinite_of_forall_exists_gt ?_
  intro N
  refine ⟨3 ^ (N + 1), ?_, ?_⟩
  · show (2 : ℤ) ^ (3 ^ (N + 1)) ≡ -1 [ZMOD ((3 ^ (N + 1) : ℕ) : ℤ)]
    have hd : ((3 ^ (N + 1) : ℕ) : ℤ) ∣ (2 : ℤ) ^ (3 ^ (N + 1)) + 1 := by
      push_cast
      exact dvd_trans (pow_dvd_pow 3 (Nat.le_succ (N + 1))) (three_pow_dvd (N + 1))
    refine Int.modEq_iff_dvd.mpr ?_
    rw [show (-1 : ℤ) - 2 ^ (3 ^ (N + 1)) = -(2 ^ (3 ^ (N + 1)) + 1) by ring]
    exact dvd_neg.mpr hd
  · calc N < 2 ^ N := Nat.lt_two_pow_self
      _ ≤ 3 ^ N := Nat.pow_le_pow_left (by norm_num) N
      _ ≤ 3 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ N)

/-- `k = 0`: `2^{2^m} ≡ 0 (mod 2^m)` for every `m`, so infinitely many `n`. -/
theorem erdos_479_zero : { n : ℕ | (2 : ℤ) ^ n ≡ 0 [ZMOD (n : ℤ)] }.Infinite := by
  refine infinite_of_forall_exists_gt ?_
  intro N
  refine ⟨2 ^ (N + 1), ?_, ?_⟩
  · show (2 : ℤ) ^ (2 ^ (N + 1)) ≡ 0 [ZMOD ((2 ^ (N + 1) : ℕ) : ℤ)]
    refine Int.modEq_zero_iff_dvd.mpr ?_
    push_cast
    exact pow_dvd_pow 2 (Nat.lt_two_pow_self (n := N + 1)).le
  · exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ N))

/-- **Erdős #479, the known cases.**  For `k = 0`, `k = −1` and every `k = 2^i` with `i ≥ 1`, the
set `{ n | 2^n ≡ k (mod n) }` of the formal-conjectures statement is infinite (stated as: no such
`k` has a finite set).  All other `k ≠ 1` remain open and are not claimed. -/
theorem erdos_479_known_cases :
    ¬ ∃ k : ℤ, (k = 0 ∨ k = -1 ∨ ∃ i : ℕ, 1 ≤ i ∧ k = 2 ^ i) ∧
      { n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] }.Finite := by
  rintro ⟨k, hk, hfin⟩
  rcases hk with rfl | rfl | ⟨i, hi, rfl⟩
  · exact erdos_479_zero hfin
  · exact erdos_479_neg_one hfin
  · exact erdos_479_two_pow i hi hfin
