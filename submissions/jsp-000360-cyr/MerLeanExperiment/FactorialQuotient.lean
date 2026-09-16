import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

namespace Erdos441

/-- Every prime at most `M` divides the quotient `M! / d` when both `d` and
`2d` occur as distinct factors of the factorial. -/
theorem factorial_quotient_small_prime (M d p : ℕ) (hd : 0 < d)
    (hsize : 2 * d ≤ M) (hp : p.Prime) (hpM : p ≤ M) :
    p ∣ M.factorial / d := by
  have hdM : d ≤ M := by omega
  have hdFact : d ∣ M.factorial := Nat.dvd_factorial hd hdM
  by_cases hpd : p ∣ d
  · have hidx : d - 1 ≠ 2 * d - 1 := by omega
    have hsubset : ({d - 1, 2 * d - 1} : Finset ℕ) ⊆ Finset.range M := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp <;> omega
    have hpair := Finset.prod_dvd_prod_of_subset
      ({d - 1, 2 * d - 1} : Finset ℕ) (Finset.range M) (fun i => i + 1) hsubset
    have hpairValue :
        (∏ i ∈ ({d - 1, 2 * d - 1} : Finset ℕ), (i + 1)) = d * (2 * d) := by
      simp [hidx, Nat.sub_add_cancel (by omega : 1 ≤ d),
        Nat.sub_add_cancel (by omega : 1 ≤ 2 * d)]
    rw [hpairValue, ← Nat.factorial_eq_prod_range_add_one] at hpair
    have hpdPair : p * d ∣ d * (2 * d) := by
      obtain ⟨k, hk⟩ := hpd
      refine ⟨2 * k, ?_⟩
      rw [hk]
      ring
    have hpdFact : p * d ∣ M.factorial := hpdPair.trans hpair
    apply (Nat.dvd_div_iff_mul_dvd hdFact).2
    simpa [Nat.mul_comm] using hpdFact
  · have hpFact : p ∣ M.factorial := hp.dvd_factorial.mpr hpM
    have hcop : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hpd).symm
    apply (Nat.dvd_div_iff_mul_dvd hdFact).2
    exact hcop.mul_dvd_of_dvd_of_dvd hdFact hpFact

/-- Integer form of `factorial_quotient_small_prime`, including negative
denominators with their actual Euclidean-division semantics. -/
theorem factorial_int_quotient_small_prime (M p : ℕ) (d : ℤ) (hd : d ≠ 0)
    (hsize : 2 * d.natAbs ≤ M) (hp : p.Prime) (hpM : p ≤ M) :
    (p : ℤ) ∣ (M.factorial : ℤ) / d := by
  have hdAbs : 0 < d.natAbs := Int.natAbs_pos.mpr hd
  have hnat := factorial_quotient_small_prime M d.natAbs p hdAbs hsize hp hpM
  have hdM : d.natAbs ≤ M := by omega
  have hdFact : d.natAbs ∣ M.factorial := Nat.dvd_factorial hdAbs hdM
  have hmulNat : d.natAbs * p ∣ M.factorial :=
    (Nat.dvd_div_iff_mul_dvd hdFact).1 hnat
  have hmulInt : (d.natAbs : ℤ) * (p : ℤ) ∣ (M.factorial : ℤ) := by
    exact_mod_cast hmulNat
  have hdMul : d * (p : ℤ) ∣ (M.factorial : ℤ) := by
    rcases le_total 0 d with hdNonneg | hdNonpos
    · simpa [Int.natAbs_of_nonneg hdNonneg] using hmulInt
    · simpa [Int.natCast_natAbs, abs_of_nonpos hdNonpos] using hmulInt
  exact Int.dvd_div_of_mul_dvd hdMul

end Erdos441
