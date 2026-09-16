import Erdos387Proof.MediumFactorWindow

/-! Elementary geometry of the exact medium-factor interval. Floors remain
explicit; all ratio bounds are derived from the original product window. -/

namespace Erdos387Proof.MediumFactorGeometry

open MediumFactorWindow
open scoped BigOperators

theorem lower_pos {B X D medium : ℕ} (hm : 0 < medium) :
    0 < lower B X D medium := hm.trans_le (le_max_left _ _)

theorem X_le_six_mul_lower {B X D medium : ℕ}
    (hB : 0 < B) (hD : 0 < D) (hm : 0 < medium) :
    X ≤ 6 * B * D * lower B X D medium := by
  let A := lower B X D medium
  have hA : 0 < A := lower_pos hm
  have hBD : 0 < B * D := Nat.mul_pos hB hD
  have hdiv : (X / 2) / (B * D) < A + 1 :=
    Nat.lt_succ_iff.mpr (le_max_right _ _)
  have hxhalf : X / 2 < (A + 1) * (B * D) :=
    (Nat.div_lt_iff_lt_mul hBD).mp hdiv
  have hx : X ≤ 2 * (X / 2) + 1 := by omega
  have hprod : 1 ≤ (B * D) * A := Nat.mul_pos hBD hA
  nlinarith

theorem upper_le_six_mul_lower {B X D medium large : ℕ}
    (hB : 0 < B) (hD : 0 < D) (hm : 0 < medium) :
    upper X D large ≤ 6 * B * lower B X D medium := by
  have hu : upper X D large * D ≤ X :=
    (Nat.le_div_iff_mul_le hD).mp (min_le_right _ _)
  have hx := X_le_six_mul_lower (X := X) hB hD hm
  have hp : upper X D large * D ≤ (6 * B * lower B X D medium) * D := by
    calc
      _ ≤ X := hu
      _ ≤ _ := by simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hx
  exact Nat.le_of_mul_le_mul_right hp hD

theorem upper_div_lower_le {B X D medium large : ℕ}
    (hB : 0 < B) (hD : 0 < D) (hm : 0 < medium) :
    (upper X D large : ℝ) / lower B X D medium ≤ 6 * B := by
  apply (div_le_iff₀ (by exact_mod_cast lower_pos (B := B) (X := X) (D := D) hm)).mpr
  exact_mod_cast upper_le_six_mul_lower (X := X) (large := large) hB hD hm

/-- The very first divided factor already has a large enough full modulus
for uniform control of all reciprocal Fourier weights in that gcd stratum. -/
theorem X_div_first_modulus_le {B X D M v u medium : ℕ}
    (hB : 0 < B) (hD : 0 < D) (hM : 0 < M) (hv : 0 < v)
    (hu : 0 < u) (hm : 0 < medium) :
    (X : ℝ) / (M * D * v * u * (lower B X D medium / u + 1) : ℕ) ≤
      (6 * (B : ℝ)) / (M * v : ℕ) := by
  let A := lower B X D medium
  have hA : A ≤ u * (A / u + 1) := by
    have h := (Nat.div_lt_iff_lt_mul hu).mp (Nat.lt_succ_self (A / u))
    simpa only [Nat.mul_comm] using h.le
  have hX := X_le_six_mul_lower (X := X) hB hD hm
  have hden : 0 < M * D * v * u * (A / u + 1) := by positivity
  have hMv : 0 < M * v := Nat.mul_pos hM hv
  apply (div_le_div_iff₀ (by exact_mod_cast hden) (by exact_mod_cast hMv)).mpr
  have hXR : (X : ℝ) ≤ 6 * B * D * A := by exact_mod_cast hX
  have hAR : (A : ℝ) ≤ u * (A / u + 1 : ℕ) := by exact_mod_cast hA
  push_cast
  have hh := mul_le_mul_of_nonneg_right hXR (show (0 : ℝ) ≤ M * v by positivity)
  have hh' := mul_le_mul_of_nonneg_left hAR (show (0 : ℝ) ≤ 6 * B * D * M * v by positivity)
  dsimp only [A] at hh hh'
  push_cast at hh'
  nlinarith

end Erdos387Proof.MediumFactorGeometry
