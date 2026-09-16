import Erdos439Power.Vendor.ErdosProblems.Erdos439.PowerSums

namespace Erdos439Power

lemma intCast_ne_zero_of_prime_factor {p q : ℕ} (hpq : p ∣ q) (z : ℤ)
    (hz : (z : ZMod p) ≠ 0) : (z : ZMod q) ≠ 0 := by
  intro h
  apply hz
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
  exact dvd_trans (by exact_mod_cast hpq) h

/-- A good shift preserves the nonvanishing leading coefficient modulo a
prime larger than the original degree. -/
lemma shiftDifference_prime_data (P : Polynomial ℤ) (s p : ℕ)
    (hp : Nat.Prime p) (hd : 0 < P.natDegree) (hdp : P.natDegree < p)
    (hlc : (P.leadingCoeff : ZMod p) ≠ 0) (hs : ¬ p ∣ s) :
    (Erdos439.PowerDecay.polynomialShiftDifference (s : ℤ) P).natDegree =
        P.natDegree - 1 ∧
      ((Erdos439.PowerDecay.polynomialShiftDifference (s : ℤ) P).leadingCoeff : ZMod p) ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hs0 : (s : ℤ) ≠ 0 := by
    intro h
    have : s = 0 := by exact_mod_cast h
    exact hs (this ▸ dvd_zero p)
  constructor
  · exact Erdos439.PowerDecay.natDegree_polynomialShiftDifference _ _ hd hs0
  · rw [Erdos439.PowerDecay.leadingCoeff_polynomialShiftDifference _ _ hd hs0]
    push_cast
    apply mul_ne_zero (mul_ne_zero hlc _)
    · exact_mod_cast (ZMod.natCast_eq_zero_iff s p).not.mpr hs
    · exact (ZMod.natCast_eq_zero_iff P.natDegree p).not.mpr
        (Nat.not_dvd_of_pos_of_lt hd hdp)

end Erdos439Power
