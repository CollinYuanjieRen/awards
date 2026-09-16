import Proof.Defs

/-!
# Erdős Problem 436: infinitely many primes with `r(2,2,p) = 9`

For a prime `p ≡ 43 (mod 840)`: `p ≡ 3 (mod 8)` so `2` is a non-residue; `p ≡ 1 (mod 3)` and
`p ≡ 3 (mod 4)` so `3` is a non-residue (quadratic reciprocity); `p ≡ 3 (mod 5)` so `5` is a
non-residue; `p ≡ 1 (mod 7)` and `p ≡ 3 (mod 4)` so `7` is a non-residue.  Hence among
`1, …, 10` the residues are exactly `1, 4, 6, 9, 10`, and the first run of two consecutive residues
is `(9, 10)`.  Dirichlet's theorem gives infinitely many such primes.
-/

namespace Erdos436

/-- `3` is not a square modulo `5`. -/
private theorem not_isSquare_three_zmod_five : ¬ IsSquare (3 : ZMod 5) := by decide

/-- Modulo a prime `p ≡ 43 (mod 840)`, none of `2, 3, 5, 7` is a square. -/
theorem not_isSquare_small_primes (p : ℕ) [Fact p.Prime] (hp : p % 840 = 43) :
    ¬ IsSquare (2 : ZMod p) ∧ ¬ IsSquare (3 : ZMod p) ∧ ¬ IsSquare (5 : ZMod p) ∧
      ¬ IsSquare (7 : ZMod p) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp8 : p % 8 = 3 := by omega
  have hp4 : p % 4 = 3 := by omega
  have hc3 : ((p : ℕ) : ZMod 3) = 1 := by
    rw [← ZMod.natCast_mod p 3, show p % 3 = 1 by omega]
    norm_num
  have hc5 : ((p : ℕ) : ZMod 5) = 3 := by
    rw [← ZMod.natCast_mod p 5, show p % 5 = 3 by omega]
    norm_num
  have hc7 : ((p : ℕ) : ZMod 7) = 1 := by
    rw [← ZMod.natCast_mod p 7, show p % 7 = 1 by omega]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ZMod.exists_sq_eq_two_iff (by omega)]
    omega
  · have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := p) (q := 3) hp4
      (by norm_num) (by omega)
    rw [Nat.cast_ofNat] at h
    rw [h, not_not, hc3]
    exact ⟨1, by norm_num⟩
  · have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p)
      (by norm_num) (by omega)
    rw [Nat.cast_ofNat] at h
    rw [← h, hc5]
    exact not_isSquare_three_zmod_five
  · have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := p) (q := 7) hp4
      (by norm_num) (by omega)
    rw [Nat.cast_ofNat] at h
    rw [h, not_not, hc7]
    exact ⟨1, by norm_num⟩

/-- For a prime `p ≡ 43 (mod 840)`, no `r ≤ 8` starts a run of two consecutive residues. -/
theorem not_isRunStart_of_le_eight (p : ℕ) [Fact p.Prime] (hp : p % 840 = 43) (r : ℕ)
    (hr : r ≤ 8) : ¬ IsRunStart p r := by
  obtain ⟨h2, h3, h5, h7⟩ := not_isSquare_small_primes p hp
  have h2' : ¬ IsSquare ((2 : ℕ) : ZMod p) := by simpa using h2
  have h4 : IsQR p (2 ^ 2) :=
    isQR_sq fun h ↦ by have := Nat.le_of_dvd (by norm_num) h; omega
  have h8 : ¬ IsSquare ((8 : ℕ) : ZMod p) := by
    have h := not_isSquare_mul_of_isQR h4 (cast_ne_zero_of_lt (by norm_num) (by omega)) h2'
    simpa using h
  rintro ⟨hr0, hqr, hqr1⟩
  interval_cases r
  · exact h2 (by simpa using hqr1.2)
  · exact h2 (by simpa using hqr.2)
  · exact h3 (by simpa using hqr.2)
  · exact h5 (by simpa using hqr1.2)
  · exact h5 (by simpa using hqr.2)
  · exact h7 (by simpa using hqr1.2)
  · exact h7 (by simpa using hqr.2)
  · exact h8 (by simpa using hqr.2)

/-- For a prime `p ≡ 43 (mod 840)`, `9` starts a run (`9` and `10 = 2 · 5` are residues). -/
theorem isRunStart_nine (p : ℕ) [Fact p.Prime] (hp : p % 840 = 43) : IsRunStart p 9 := by
  obtain ⟨h2, h3, h5, h7⟩ := not_isSquare_small_primes p hp
  refine ⟨by norm_num, ?_, ?_⟩
  · have h : IsQR p (3 ^ 2) :=
      isQR_sq fun hd ↦ by have := Nat.le_of_dvd (by norm_num) hd; omega
    simpa using h
  · have h : IsQR p (2 * 5) :=
      isQR_mul_of_not (cast_ne_zero_of_lt (by norm_num) (by omega))
        (cast_ne_zero_of_lt (by norm_num) (by omega)) (by simpa using h2) (by simpa using h5)
    simpa using h

/-- For a prime `p ≡ 43 (mod 840)`, `r(2,2,p) = 9`. -/
theorem runStart_eq_nine (p : ℕ) [Fact p.Prime] (hp : p % 840 = 43) : runStart p = 9 := by
  have h9 : IsRunStart p 9 := isRunStart_nine p hp
  have hmem : IsRunStart p (runStart p) := Nat.sInf_mem (s := {r : ℕ | IsRunStart p r}) ⟨9, h9⟩
  refine le_antisymm (Nat.sInf_le h9) ?_
  by_contra hlt
  exact not_isRunStart_of_le_eight p hp _ (by omega) hmem

/-- **Lehmer–Lehmer, lower half.** There are arbitrarily large primes `p` with `r(2,2,p) = 9`. -/
theorem exists_prime_gt_runStart_eq_nine (N : ℕ) : ∃ p > N, p.Prime ∧ runStart p = 9 := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 840) (a := 43) (by norm_num) (by norm_num)
  have := Fact.mk hp
  refine ⟨p, hpN, hp, runStart_eq_nine p ?_⟩
  simpa [Nat.ModEq] using hmod

end Erdos436
