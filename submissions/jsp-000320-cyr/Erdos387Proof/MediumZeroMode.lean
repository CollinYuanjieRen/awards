import Erdos387Proof.BrunLocalDensity
import Erdos387Proof.CoprimeHarmonic
import Erdos387Proof.MediumSieveEuler

/-! Exact local main term and explicit endpoint error after gcd splitting.
The signed outer sieve coefficient is intentionally not estimated here. -/

namespace Erdos387Proof.MediumZeroMode

open scoped BigOperators

noncomputable def harmonicBlock (A B u Q : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ioc (A / u) (B / u) with Nat.Coprime Q t, (1 : ℝ) / t

noncomputable def zeroMode (g Q k A B : ℕ) (mass : ℝ) : ℝ :=
  ∑ u ∈ g.divisors,
    (k : ℝ) ^ (g / u).primeFactors.card * mass / (Q * g : ℕ) *
      harmonicBlock A B u (Q * (g / u))

noncomputable def mainTerm (g Q k A B : ℕ) (mass : ℝ) : ℝ :=
  (mass / Q) * ((Nat.totient Q : ℝ) / Q) * Real.log ((B : ℝ) / A) *
    ∏ p ∈ g.primeFactors, MediumSieveEuler.alpha k p

noncomputable def endpointError (g Q k A : ℕ) (mass : ℝ) : ℝ :=
  ∑ u ∈ g.divisors,
    (k : ℝ) ^ (g / u).primeFactors.card * mass / (Q * g : ℕ) *
      (4 * (Q * (g / u)).divisors.card * u / A)

theorem mainTerm_eq_sum {g Q k A B : ℕ} (hg : Squarefree g)
    (hcop : Nat.Coprime Q g) (mass : ℝ) :
    mainTerm g Q k A B mass =
      ∑ u ∈ g.divisors,
        (k : ℝ) ^ (g / u).primeFactors.card * mass / (Q * g : ℕ) *
          ((Nat.totient (Q * (g / u)) : ℝ) / (Q * (g / u) : ℕ) *
            Real.log ((B : ℝ) / A)) := by
  have hid := squarefree_divisor_local_density k g hg
  unfold mainTerm
  simp only [MediumSieveEuler.alpha] 
  rw [← hid, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hQv : Nat.Coprime Q (g / u) :=
    hcop.of_dvd_right (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hu))
  rw [Nat.totient_mul hQv]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem abs_zeroMode_sub_mainTerm_le {g Q k A B : ℕ}
    (hg : Squarefree g) (hQ : 0 < Q) (hcop : Nat.Coprime Q g)
    (hA : 0 < A) (hAB : A ≤ B) (mass : ℝ) (hmass : 0 ≤ mass) :
    |zeroMode g Q k A B mass - mainTerm g Q k A B mass| ≤
      endpointError g Q k A mass := by
  classical
  rw [mainTerm_eq_sum hg hcop mass]
  unfold zeroMode endpointError
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro u hu
  have hu0 := Nat.pos_of_mem_divisors hu
  have hv0 : 0 < g / u :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hg.ne_zero)
        (Nat.dvd_of_mem_divisors hu)) hu0
  have hweight : 0 ≤ (k : ℝ) ^ (g / u).primeFactors.card * mass / (Q * g : ℕ) := by
    positivity
  rw [← mul_sub, abs_mul, abs_of_nonneg hweight]
  exact mul_le_mul_of_nonneg_left
    (CoprimeHarmonic.abs_sum_coprime_Ioc_div_inv_sub_log_le
      hA hAB hu0 (Nat.mul_pos hQ hv0)) hweight

end Erdos387Proof.MediumZeroMode
