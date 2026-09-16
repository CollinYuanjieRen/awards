import Erdos387Proof.HarmonicInterval
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient

/-! Exact Möbius coefficients and finite coprime harmonic interval errors. -/

namespace Erdos387Proof.CoprimeHarmonic

open scoped BigOperators

theorem sum_moebius_common_divisors {Q n : ℕ} (hQ : 0 < Q) :
    (∑ e ∈ Q.divisors with e ∣ n, (ArithmeticFunction.moebius e : ℝ)) =
      if Nat.Coprime Q n then 1 else 0 := by
  have hg : Nat.gcd Q n ≠ 0 := (Nat.gcd_pos_of_pos_left n hQ).ne'
  have hset : Q.divisors.filter (fun e => e ∣ n) = (Nat.gcd Q n).divisors := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨heQ, _⟩, hen⟩
      exact ⟨⟨heQ, hen⟩, hg⟩
    · rintro ⟨⟨heQ, hen⟩, _⟩
      exact ⟨⟨heQ, hQ.ne'⟩, hen⟩
  rw [hset]
  have h := congrArg (fun f : ArithmeticFunction ℝ => f (Nat.gcd Q n))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply, Nat.Coprime] using h

theorem sum_moebius_div_eq_totient_div {Q : ℕ} (hQ : 0 < Q) :
    (∑ e ∈ Q.divisors, (ArithmeticFunction.moebius e : ℝ) / e) =
      (Nat.totient Q : ℝ) / Q := by
  have hsum : ∀ n : ℕ, n > 0 → (∑ e ∈ n.divisors, (Nat.totient e : ℝ)) = (n : ℝ) := by
    intro n _
    exact_mod_cast Nat.sum_totient n
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hsum) Q hQ
  rw [Nat.sum_divisorsAntidiagonal
    (f := fun e t : ℕ => (ArithmeticFunction.moebius e : ℝ) * (t : ℝ))] at h
  apply (eq_div_iff (by positivity : (Q : ℝ) ≠ 0)).mpr
  rw [Finset.sum_mul]
  calc
    _ = ∑ e ∈ Q.divisors, (ArithmeticFunction.moebius e : ℝ) * (Q / e : ℕ) := by
      apply Finset.sum_congr rfl
      intro e he
      have heR : (e : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors he).ne'
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors he) heR]
      ring
    _ = (Nat.totient Q : ℝ) := h

theorem abs_weighted_harmonic_error_le
    {A B u : ℕ} (hA : 0 < A) (hAB : A ≤ B) (hu : 0 < u)
    (D : Finset ℕ) (hD : ∀ e ∈ D, 0 < e) (weight : ℕ → ℝ)
    (hweight : ∀ e ∈ D, |weight e| ≤ 1) :
    |(∑ e ∈ D, (weight e / e) *
      ∑ n ∈ Finset.Ioc (A / (u * e)) (B / (u * e)), (1 : ℝ) / n) -
      (∑ e ∈ D, weight e / e) * Real.log ((B : ℝ) / A)| ≤
      4 * D.card * u / A := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hid : (∑ e ∈ D, (weight e / e) *
      ∑ n ∈ Finset.Ioc (A / (u * e)) (B / (u * e)), (1 : ℝ) / n) -
      (∑ e ∈ D, weight e / e) * Real.log ((B : ℝ) / A) =
      ∑ e ∈ D, (weight e / e) *
        ((∑ n ∈ Finset.Ioc (A / (u * e)) (B / (u * e)), (1 : ℝ) / n) -
          Real.log ((B : ℝ) / A)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hid]
  calc
    _ ≤ ∑ e ∈ D, |(weight e / e) *
        ((∑ n ∈ Finset.Ioc (A / (u * e)) (B / (u * e)), (1 : ℝ) / n) -
          Real.log ((B : ℝ) / A))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ D, 4 * (u : ℝ) / A := by
      apply Finset.sum_le_sum
      intro e he
      have her : (0 : ℝ) < e := by exact_mod_cast hD e he
      have hcoeff : |weight e / e| ≤ (1 : ℝ) / e := by
        rw [abs_div, abs_of_pos her]
        exact div_le_div_of_nonneg_right (hweight e he) her.le
      have herr := HarmonicInterval.abs_sum_Ioc_div_inv_sub_log_le
        hA hAB (Nat.mul_pos hu (hD e he))
      rw [abs_mul]
      calc
        _ ≤ ((1 : ℝ) / e) * (4 * (u * e : ℕ) / A) :=
          mul_le_mul hcoeff herr (abs_nonneg _) (by positivity)
        _ = 4 * u / A := by push_cast; field_simp
    _ = 4 * D.card * u / A := by simp; ring

theorem sum_Ioc_dvd_inv (a b e : ℕ) (he : 0 < e) :
    (∑ n ∈ Finset.Ioc a b with e ∣ n, (1 : ℝ) / n) =
      (1 / (e : ℝ)) * ∑ m ∈ Finset.Ioc (a / e) (b / e), (1 : ℝ) / m := by
  classical
  have hmem (m : ℕ) : m ∈ Finset.Ioc (a / e) (b / e) ↔ e * m ∈ Finset.Ioc a b := by
    simp only [Finset.mem_Ioc, Nat.div_lt_iff_lt_mul he, Nat.le_div_iff_mul_le he]
    simp only [Nat.mul_comm]
  have hset : (Finset.Ioc (a / e) (b / e)).image (fun m => e * m) =
      (Finset.Ioc a b).filter (fun n => e ∣ n) := by
    ext n
    constructor
    · intro hn
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_filter.mpr ⟨(hmem m).mp hm, dvd_mul_right e m⟩
    · intro hn
      obtain ⟨hnI, m, rfl⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_image.mpr ⟨m, (hmem m).mpr hnI, rfl⟩
  rw [← hset, Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    push_cast
    simp only [one_div, mul_inv]
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left he hab

theorem sum_coprime_Ioc_inv_eq_moebius (a b : ℕ) {Q : ℕ} (hQ : 0 < Q) :
    (∑ n ∈ Finset.Ioc a b with Nat.Coprime Q n, (1 : ℝ) / n) =
      ∑ e ∈ Q.divisors, (ArithmeticFunction.moebius e : ℝ) / e *
        ∑ m ∈ Finset.Ioc (a / e) (b / e), (1 : ℝ) / m := by
  classical
  calc
    _ = ∑ n ∈ Finset.Ioc a b,
        (∑ e ∈ Q.divisors with e ∣ n, (ArithmeticFunction.moebius e : ℝ)) *
          ((1 : ℝ) / n) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      rw [sum_moebius_common_divisors hQ]
      split_ifs <;> simp
    _ = ∑ e ∈ Q.divisors, (ArithmeticFunction.moebius e : ℝ) *
        ∑ n ∈ Finset.Ioc a b with e ∣ n, (1 : ℝ) / n := by
      simp_rw [Finset.sum_filter, Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      rw [sum_Ioc_dvd_inv a b e (Nat.pos_of_mem_divisors he)]
      ring

/-- Exact coprime harmonic main term and an explicit uniform endpoint error.
`Q.divisors.card` is the ordinary divisor count; no prime estimate is assumed. -/
theorem abs_sum_coprime_Ioc_div_inv_sub_log_le
    {A B u Q : ℕ} (hA : 0 < A) (hAB : A ≤ B) (hu : 0 < u) (hQ : 0 < Q) :
    |(∑ n ∈ Finset.Ioc (A / u) (B / u) with Nat.Coprime Q n, (1 : ℝ) / n) -
      ((Nat.totient Q : ℝ) / Q) * Real.log ((B : ℝ) / A)| ≤
      4 * Q.divisors.card * u / A := by
  have hweight (e : ℕ) (_he : e ∈ Q.divisors) :
      |(ArithmeticFunction.moebius e : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := e))
  have h := abs_weighted_harmonic_error_le hA hAB hu Q.divisors
    (fun _ he => Nat.pos_of_mem_divisors he)
    (fun e => (ArithmeticFunction.moebius e : ℝ)) hweight
  rw [sum_moebius_div_eq_totient_div hQ] at h
  rw [sum_coprime_Ioc_inv_eq_moebius (A / u) (B / u) hQ]
  simpa only [Nat.div_div_eq_div_mul] using h

end Erdos387Proof.CoprimeHarmonic
