import MerLeanExperiment.QuadraticChord
import Mathlib.Tactic

namespace Erdos441

/-- The first floor branch is a concave quadratic on the closed half-unit
interval; both endpoint values dominate the common source bound. -/
theorem floor_branch_one (q u n : ℝ) (hq : 1 ≤ q) (hu : 2 ≤ u)
    (hnlo : u - 1 / 2 ≤ n) (hnhi : n ≤ u) :
    (2 - q) * u - q / (4 * u) ≤ 2 * n - q * n ^ 2 / u := by
  have hupos : 0 < u := by linarith
  let A : ℝ := -q / u
  let B : ℝ := 2
  let C : ℝ := -((2 - q) * u - q / (4 * u))
  have hA : A ≤ 0 := by
    dsimp [A]
    have hq0 : 0 ≤ q := le_trans (by norm_num) hq
    have hd : 0 ≤ q / u := div_nonneg hq0 hupos.le
    have heq : -q / u = -(q / u) := by ring
    rw [heq]
    exact neg_nonpos.mpr hd
  have hleft : 0 ≤ A * (u - 1 / 2) ^ 2 + B * (u - 1 / 2) + C := by
    dsimp [A, B, C]
    field_simp [hupos.ne']
    ring_nf
    nlinarith
  have hright : 0 ≤ A * u ^ 2 + B * u + C := by
    dsimp [A, B, C]
    field_simp [hupos.ne']
    ring_nf
    nlinarith
  have hquad := quadratic_nonneg_between (u - 1 / 2) u n A B C
    hnlo hnhi hA hleft hright
  calc
    (2 - q) * u - q / (4 * u) ≤
        (2 - q) * u - q / (4 * u) + (A * n ^ 2 + B * n + C) := by linarith
    _ = 2 * n - q * n ^ 2 / u := by
      dsimp [A, B, C]
      field_simp [hupos.ne']
      ring_nf

/-- The second floor branch lies above its rational endpoint chord on the
closed half-unit interval, by the explicit nonnegative chord-gap identity. -/
theorem floor_branch_two (q u n : ℝ) (hq : 1 ≤ q) (hu : 2 ≤ u)
    (hnlo : u - 1 ≤ n) (hnhi : n ≤ u - 1 / 2) :
    (2 - q) * u - q / (4 * u) ≤
      2 * n - q * n * (n + 1) / u + u / (n + 1) := by
  let a : ℝ := u - 1
  let b : ℝ := u - 1 / 2
  let F : ℝ → ℝ := fun x ↦ 2 * x - q * x * (x + 1) / u + u / (x + 1)
  let target : ℝ := (2 - q) * u - q / (4 * u)
  have hupos : 0 < u := by linarith
  have ha1 : a + 1 = u := by dsimp [a]; ring
  have hb1 : b + 1 = u + 1 / 2 := by dsimp [b]; ring
  have ha1pos : 0 < a + 1 := by rw [ha1]; exact hupos
  have hb1pos : 0 < b + 1 := by rw [hb1]; linarith
  have hn1pos : 0 < n + 1 := by
    linarith
  have hgapPos : 0 < b - a := by
    dsimp [a, b]
    norm_num
  have hFa : target ≤ F a := by
    have heq : F a = (2 - q) * u + (q - 1) := by
      dsimp [F, a]
      field_simp [hupos.ne']
      ring
    rw [heq]
    dsimp [target]
    have : 0 ≤ q / (4 * u) := by positivity
    linarith
  have hFb : target ≤ F b := by
    have hrecip : 1 / (2 * u + 1) ≤ q / (2 * u) := by
      have h2u : 0 < 2 * u := by positivity
      have h2u1 : 0 < 2 * u + 1 := by positivity
      apply (div_le_div_iff₀ h2u1 h2u).2
      nlinarith
    have heq : F b = (2 - q) * u + q / (4 * u) - 1 / (2 * u + 1) := by
      dsimp [F]
      rw [hb1]
      dsimp [b]
      field_simp [hupos.ne', show u + 1 / 2 ≠ 0 by positivity,
        show 2 * u + 1 ≠ 0 by positivity]
      ring
    rw [heq]
    dsimp [target]
    have htwice : q / (4 * u) + q / (4 * u) = q / (2 * u) := by
      field_simp [hupos.ne']
      ring
    linarith
  have habNonneg : 0 ≤ b - n := sub_nonneg.mpr hnhi
  have hnaNonneg : 0 ≤ n - a := sub_nonneg.mpr hnlo
  have hprodPos : 0 < (a + 1) * (b + 1) * (n + 1) := by positivity
  have hsecond : u / ((a + 1) * (b + 1) * (n + 1)) ≤ 1 / u := by
    apply (div_le_div_iff₀ hprodPos hupos).2
    rw [ha1]
    have hbn : u ≤ (b + 1) * (n + 1) := by
      have hbge : u ≤ b + 1 := by rw [hb1]; linarith
      have hnge : 1 ≤ n + 1 := by linarith
      calc
        u = u * 1 := by ring
        _ ≤ (b + 1) * (n + 1) :=
          mul_le_mul hbge hnge (by linarith) (by linarith)
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hbn hupos.le
  have hfirst : 1 / u ≤ q / u := by
    exact (div_le_div_iff_of_pos_right hupos).2 hq
  have hbracket : 0 ≤ q / u - u / ((a + 1) * (b + 1) * (n + 1)) := by
    linarith
  have hgapNonneg : 0 ≤
      (n - a) * (b - n) *
        (q / u - u / ((a + 1) * (b + 1) * (n + 1))) := by
    positivity
  let chord : ℝ := ((b - n) * F a + (n - a) * F b) / (b - a)
  have hchord : target ≤ chord := by
    have hweighted : (b - a) * target ≤ (b - n) * F a + (n - a) * F b := by
      have h1 := mul_le_mul_of_nonneg_left hFa habNonneg
      have h2 := mul_le_mul_of_nonneg_left hFb hnaNonneg
      have hweights : (b - n) * target + (n - a) * target = (b - a) * target := by ring
      rw [← hweights]
      exact add_le_add h1 h2
    dsimp [chord]
    exact (le_div_iff₀ hgapPos).2 (by simpa [mul_comm] using hweighted)
  have hgapEq : F n - chord =
      (n - a) * (b - n) *
        (q / u - u / ((a + 1) * (b + 1) * (n + 1))) := by
    dsimp [F, chord]
    field_simp [hupos.ne', ha1pos.ne', hb1pos.ne', hn1pos.ne', hgapPos.ne']
    ring
  have hFn : chord ≤ F n := by
    rw [← sub_nonneg]
    rw [hgapEq]
    exact hgapNonneg
  exact hchord.trans hFn

end Erdos441
