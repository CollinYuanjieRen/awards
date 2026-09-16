import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic

/-! Uniform harmonic interval errors, including endpoints below one. -/

namespace Erdos387Proof.HarmonicInterval

open Real

theorem abs_harmonic_floor_sub_log_sub_gamma_le {x : ℝ} (hx : 0 < x) :
    |(harmonic ⌊x⌋₊ : ℝ) - log x - eulerMascheroniConstant| ≤ 2 / x := by
  let m : ℕ := ⌊x⌋₊
  have hmle : (m : ℝ) ≤ x := Nat.floor_le hx.le
  have hxlt : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
  have hγlo := (eulerMascheroniSeq_lt_eulerMascheroniConstant m).le
  change (harmonic m : ℝ) - log ((m : ℝ) + 1) ≤ eulerMascheroniConstant at hγlo
  have hupp : (harmonic m : ℝ) - log x - eulerMascheroniConstant ≤ 1 / x := by
    have hlog := log_le_sub_one_of_pos (div_pos (by positivity : 0 < (m : ℝ) + 1) hx)
    rw [log_div (by positivity) hx.ne'] at hlog
    have hrat : ((m : ℝ) + 1) / x - 1 ≤ 1 / x := by
      apply (le_div_iff₀ hx).mpr
      field_simp
      nlinarith
    linarith
  have hlo : -(2 / x) ≤ (harmonic m : ℝ) - log x - eulerMascheroniConstant := by
    by_cases hm : m = 0
    · have hx1 : x < 1 := by simpa [hm] using hxlt
      have hlog : log x ≤ 0 := log_nonpos hx.le hx1.le
      have hγ : eulerMascheroniConstant ≤ 1 := by
        simpa only [eulerMascheroniSeq'_one] using
          (eulerMascheroniConstant_lt_eulerMascheroniSeq' 1).le
      have hxinv : 1 ≤ 2 / x := (le_div_iff₀ hx).mpr (by linarith)
      simp only [hm, harmonic_zero, Rat.cast_zero]
      linarith
    · have hmp : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hm)
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm)
      have hγhi := (eulerMascheroniConstant_lt_eulerMascheroniSeq' m).le
      simp only [eulerMascheroniSeq', hm, if_false] at hγhi
      have hlog := log_le_sub_one_of_pos (div_pos hx hmp)
      rw [log_div hx.ne' hmp.ne'] at hlog
      have hrat : x / (m : ℝ) - 1 ≤ 1 / (m : ℝ) := by
        apply (le_div_iff₀ hmp).mpr
        field_simp
        linarith
      have hinv : 1 / (m : ℝ) ≤ 2 / x := by
        apply (div_le_div_iff₀ hmp hx).mpr
        nlinarith
      linarith
  exact abs_le.mpr ⟨hlo, hupp.trans (by gcongr; norm_num)⟩

theorem abs_harmonic_floor_difference_sub_log_le
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    |((harmonic ⌊y⌋₊ : ℝ) - harmonic ⌊x⌋₊) - log (y / x)| ≤ 4 / x := by
  have hy : 0 < y := hx.trans_le hxy
  have h := abs_sub
    ((harmonic ⌊y⌋₊ : ℝ) - log y - eulerMascheroniConstant)
    ((harmonic ⌊x⌋₊ : ℝ) - log x - eulerMascheroniConstant)
  rw [log_div hy.ne' hx.ne']
  calc
    _ = |((harmonic ⌊y⌋₊ : ℝ) - log y - eulerMascheroniConstant) -
        ((harmonic ⌊x⌋₊ : ℝ) - log x - eulerMascheroniConstant)| := by congr 1; ring
    _ ≤ |(harmonic ⌊y⌋₊ : ℝ) - log y - eulerMascheroniConstant| +
        |(harmonic ⌊x⌋₊ : ℝ) - log x - eulerMascheroniConstant| := h
    _ ≤ 2 / y + 2 / x := add_le_add
      (abs_harmonic_floor_sub_log_sub_gamma_le hy)
      (abs_harmonic_floor_sub_log_sub_gamma_le hx)
    _ ≤ 4 / x := by
      have hinv : 2 / y ≤ 2 / x := div_le_div_of_nonneg_left (by norm_num) hx hxy
      calc
        2 / y + 2 / x ≤ 2 / x + 2 / x := add_le_add hinv le_rfl
        _ = 4 / x := by ring

theorem sum_Ioc_inv_eq_harmonic_sub {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc a b, (1 : ℝ) / n) = (harmonic b : ℝ) - harmonic a := by
  have heq (n : ℕ) : (∑ i ∈ Finset.Ioc 0 n, (1 : ℝ) / i) = harmonic n := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    have hset : Finset.Ioc 0 n = Finset.Icc 1 n := by
      ext i
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    simp [hset, one_div]
  have h := Finset.sum_Ioc_consecutive (fun n : ℕ => (1 : ℝ) / n) (Nat.zero_le a) hab
  rw [heq a, heq b] at h
  linarith

/-- The divisions in the endpoints are natural divisions. There is no lower
bound on A/u: an empty or subunit initial interval is covered by the same error. -/
theorem abs_sum_Ioc_div_inv_sub_log_le
    {A B u : ℕ} (hA : 0 < A) (hAB : A ≤ B) (hu : 0 < u) :
    |(∑ n ∈ Finset.Ioc (A / u) (B / u), (1 : ℝ) / n) -
      log ((B : ℝ) / A)| ≤ 4 * u / A := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hur : (0 : ℝ) < u := by exact_mod_cast hu
  have hABr : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have h := abs_harmonic_floor_difference_sub_log_le
    (div_pos hAr hur) (div_le_div_of_nonneg_right hABr hur.le)
  rw [Nat.floor_div_eq_div, Nat.floor_div_eq_div] at h
  rw [sum_Ioc_inv_eq_harmonic_sub (Nat.div_le_div_right hAB)]
  have hratio : ((B : ℝ) / u) / ((A : ℝ) / u) = (B : ℝ) / A := by field_simp
  have herr : 4 / ((A : ℝ) / u) = 4 * u / A := by field_simp
  simpa only [hratio, herr] using h

end Erdos387Proof.HarmonicInterval
