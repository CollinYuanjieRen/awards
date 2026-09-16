import Mathlib

namespace Erdos439Power

/-- Move a positive natural scale from the left side of a rational
approximation into its denominator, then reduce the resulting fraction. -/
theorem exists_reduced_scaled_rational
    (C b Q a : ℕ) (α : ℝ) (hC : 0 < C) (hb : 0 < b) (hQ : 0 < Q)
    (happrox :
      |(C : ℝ) * α - (a : ℝ) / b| ≤ 1 / ((b : ℝ) * Q)) :
    ∃ A q : ℕ,
      0 < q ∧ q ≤ C * b ∧ A.Coprime q ∧
      (A : ℝ) / q = (a : ℝ) / ((C : ℝ) * b) ∧
      (q : ℝ) * |α - (A : ℝ) / q| ≤ 1 / (Q : ℝ) := by
  let n := C * b
  let g := a.gcd n
  let A := a / g
  let q := n / g
  have hn : 0 < n := by dsimp [n]; positivity
  have hg : 0 < g := by
    exact Nat.gcd_pos_of_pos_right a hn
  have hgdn : g ∣ n := Nat.gcd_dvd_right a n
  have hgda : g ∣ a := Nat.gcd_dvd_left a n
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hn hgdn) hg
  have hqn : q ≤ n := Nat.div_le_self n g
  have hcop : A.Coprime q := Nat.coprime_div_gcd_div_gcd hg
  have ha : A * g = a := Nat.div_mul_cancel hgda
  have hnq : q * g = n := Nat.div_mul_cancel hgdn
  have hratio : (A : ℝ) / q = (a : ℝ) / n := by
    apply (div_eq_div_iff (by positivity : (q : ℝ) ≠ 0)
      (by positivity : (n : ℝ) ≠ 0)).2
    exact_mod_cast (by rw [← ha, ← hnq]; ring : A * n = a * q)
  have hscaleIdentity :
      (C : ℝ) * |α - (a : ℝ) / n| =
        |(C : ℝ) * α - (a : ℝ) / b| := by
    calc
      (C : ℝ) * |α - (a : ℝ) / n| =
          |(C : ℝ)| * |α - (a : ℝ) / n| := by
            rw [abs_of_nonneg (by exact_mod_cast hC.le : (0 : ℝ) ≤ C)]
      _ = |(C : ℝ) * (α - (a : ℝ) / n)| := (abs_mul _ _).symm
      _ = |(C : ℝ) * α - (a : ℝ) / b| := by
        congr 1
        dsimp [n]
        push_cast
        field_simp
  have hscaledN : (n : ℝ) * |α - (a : ℝ) / n| ≤ 1 / (Q : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left happrox (show (0 : ℝ) ≤ b by positivity)
    rw [← hscaleIdentity] at hmul
    calc
      (n : ℝ) * |α - (a : ℝ) / n| =
          (b : ℝ) * ((C : ℝ) * |α - (a : ℝ) / n|) := by
            dsimp [n]
            push_cast
            ring
      _ ≤ (b : ℝ) * (1 / ((b : ℝ) * Q)) := hmul
      _ = 1 / (Q : ℝ) := by field_simp
  refine ⟨A, q, hq, ?_, hcop, ?_, ?_⟩
  · simpa [n] using hqn
  · simpa [n] using hratio
  · rw [hratio]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hqn)
      (abs_nonneg _)).trans hscaledN

end Erdos439Power
