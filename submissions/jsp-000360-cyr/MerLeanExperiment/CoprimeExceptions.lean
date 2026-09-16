import MerLeanExperiment.ResidueCount
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic

namespace Erdos441

/-- Integers in a signed interval that are not coprime to `D` are covered by
the residue-zero classes of the prime factors of `D`. -/
theorem coprime_exception_bound (D : ℕ) (hD : D ≠ 0) (a b : ℤ) (hab : a ≤ b) :
    (({x ∈ Finset.Ioc a b | ¬ Nat.Coprime (x : ℤ).natAbs D}).card : ℚ) ≤
      ∑ p ∈ D.primeFactors, (((b - a : ℤ) : ℚ) / p + 1) := by
  let bad : Finset ℤ := {x ∈ Finset.Ioc a b | ¬ Nat.Coprime x.natAbs D}
  let multiples (p : ℕ) : Finset ℤ :=
    {x ∈ Finset.Ioc a b | Int.ModEq (p : ℤ) x 0}
  have hcover : bad ⊆ D.primeFactors.biUnion multiples := by
    intro x hx
    have hx' : x ∈ Finset.Ioc a b ∧ ¬ Nat.Coprime x.natAbs D := by
      simpa [bad] using hx
    obtain ⟨p, hp, hpx, hpD⟩ := Nat.Prime.not_coprime_iff_dvd.mp hx'.2
    have hpMem : p ∈ D.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpD, hD⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hpMem, ?_⟩
    have hpInt : (p : ℤ) ∣ x := Int.natCast_dvd.mpr hpx
    simpa [multiples, hx'.1, Int.modEq_zero_iff_dvd] using hpInt
  have hcardNat : bad.card ≤ ∑ p ∈ D.primeFactors, (multiples p).card := by
    exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hcardQ : (bad.card : ℚ) ≤
      ∑ p ∈ D.primeFactors, ((multiples p).card : ℚ) := by
    exact_mod_cast hcardNat
  have hclass (p : ℕ) (hpMem : p ∈ D.primeFactors) :
      ((multiples p).card : ℚ) ≤ ((b - a : ℤ) : ℚ) / p + 1 := by
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hres := residue_count_discrepancy a b 0 p hp.pos hab
    change |((multiples p).card : ℚ) - ((b - a : ℤ) : ℚ) / p| ≤ 1 at hres
    rw [abs_le] at hres
    linarith
  change (bad.card : ℚ) ≤ ∑ p ∈ D.primeFactors, (((b - a : ℤ) : ℚ) / p + 1)
  exact hcardQ.trans (Finset.sum_le_sum fun p hpMem ↦ hclass p hpMem)

end Erdos441
