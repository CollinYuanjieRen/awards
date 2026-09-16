import Mathlib

/-!
# Erdős Problem 436 (runs of power residues): definitions for `Λ(2,2)`

For a prime `p`, a natural number `r` is a *quadratic residue* modulo `p` when it is a nonzero
square in `ZMod p`.  `runStart p` is the least `r ≥ 1` such that `r` and `r + 1` are both quadratic
residues modulo `p` (Lehmer–Lehmer's `r(2,2,p)`), and `Lambda22` is `limsup_{p → ∞} runStart p`
over the primes.  Lehmer and Lehmer showed `Λ(2,2) = 9`.
-/

open Filter

namespace Erdos436

/-- `r` is a quadratic residue modulo `p`: a nonzero square in `ZMod p`. -/
def IsQR (p r : ℕ) : Prop := (r : ZMod p) ≠ 0 ∧ IsSquare (r : ZMod p)

/-- `r ≥ 1` starts a run of two consecutive quadratic residues modulo `p`. -/
def IsRunStart (p r : ℕ) : Prop := 0 < r ∧ IsQR p r ∧ IsQR p (r + 1)

/-- Lehmer–Lehmer's `r(2,2,p)`: the least `r ≥ 1` with `r`, `r + 1` both quadratic residues
modulo `p` (as an infimum in `ℕ`; `0` if there is none). -/
noncomputable def runStart (p : ℕ) : ℕ := sInf {r : ℕ | IsRunStart p r}

/-- `Λ(2,2) = limsup_{p → ∞} r(2,2,p)` over the primes. -/
noncomputable def Lambda22 : ℕ := limsup runStart (atTop ⊓ 𝓟 {p : ℕ | p.Prime})

/-- A natural square `k ^ 2` with `p ∤ k` is a quadratic residue. -/
theorem isQR_sq {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : ¬ p ∣ k) : IsQR p (k ^ 2) := by
  have hk0 : (k : ZMod p) ≠ 0 := fun h ↦ hk ((ZMod.natCast_eq_zero_iff k p).mp h)
  refine ⟨?_, ?_⟩
  · rw [Nat.cast_pow]
    exact pow_ne_zero 2 hk0
  · rw [Nat.cast_pow]
    exact ⟨(k : ZMod p), by ring⟩

/-- The product of two nonzero non-residues is a residue (the quadratic character is
multiplicative). -/
theorem isQR_mul_of_not {p : ℕ} [Fact p.Prime] {a b : ℕ} (ha : (a : ZMod p) ≠ 0)
    (hb : (b : ZMod p) ≠ 0) (ha' : ¬ IsSquare (a : ZMod p)) (hb' : ¬ IsSquare (b : ZMod p)) :
    IsQR p (a * b) := by
  have hab : (a : ZMod p) * (b : ZMod p) ≠ 0 := mul_ne_zero ha hb
  have h : quadraticChar (ZMod p) ((a : ZMod p) * (b : ZMod p)) = 1 := by
    rw [map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr ha',
      quadraticChar_neg_one_iff_not_isSquare.mpr hb']
    norm_num
  refine ⟨?_, ?_⟩
  · rw [Nat.cast_mul]
    exact hab
  · rw [Nat.cast_mul]
    exact (quadraticChar_one_iff_isSquare hab).mp h

/-- A residue times a non-residue is a non-residue. -/
theorem not_isSquare_mul_of_isQR {p : ℕ} [Fact p.Prime] {a b : ℕ} (ha : IsQR p a)
    (hb : (b : ZMod p) ≠ 0) (hb' : ¬ IsSquare (b : ZMod p)) : ¬ IsSquare ((a * b : ℕ) : ZMod p) := by
  have hb1 : quadraticChar (ZMod p) (b : ZMod p) = -1 :=
    (quadraticChar_eq_neg_one_iff_not_one hb).mpr fun hc ↦
      hb' ((quadraticChar_one_iff_isSquare hb).mp hc)
  have h : quadraticChar (ZMod p) ((a : ZMod p) * (b : ZMod p)) = -1 := by
    rw [map_mul, (quadraticChar_one_iff_isSquare ha.1).mpr ha.2, hb1]
    norm_num
  rw [Nat.cast_mul]
  exact quadraticChar_neg_one_iff_not_isSquare.mp h

/-- For a prime `p > r`, the cast of `r ≥ 1` is nonzero. -/
theorem cast_ne_zero_of_lt {p r : ℕ} [Fact p.Prime] (hr : 0 < r) (hrp : r < p) :
    (r : ZMod p) ≠ 0 := by
  intro h
  exact absurd (Nat.le_of_dvd hr ((ZMod.natCast_eq_zero_iff r p).mp h)) (not_le.mpr hrp)

end Erdos436
