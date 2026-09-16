import Erdos387Proof.MediumOscillatoryMass

/-! Scalar bounds converting the weighted periodic estimate to the two
complementary sums without replacing interval length by its worst case. -/

set_option autoImplicit false

namespace Erdos387Proof.MediumCompletionShape

noncomputable def shape (X D : ℕ) : ℝ :=
  (X : ℝ) / (D * Real.sqrt D) + Real.sqrt D

theorem blockCount_mul_sqrt_le {X D q L : ℕ}
    (hD : 0 < D) (hDq : D ≤ q) (hL : L * D ≤ X) :
    ((L / q + 1 : ℕ) : ℝ) * Real.sqrt D ≤ shape X D := by
  have hquot : L / q * D ≤ L :=
    (Nat.mul_le_mul_left (L / q) hDq).trans (Nat.div_mul_le_self L q)
  have hbudget : (L / q) * D * D ≤ X :=
    (Nat.mul_le_mul_right D hquot).trans hL
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hroot : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr hDR
  have hsq := Real.sq_sqrt hDR.le
  have hquotR : ((L / q : ℕ) : ℝ) ≤ (X : ℝ) / (D : ℝ)^2 := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (D : ℝ)^2)).mpr
    exact_mod_cast (show (L / q) * D^2 ≤ X by simpa [pow_two, Nat.mul_assoc] using hbudget)
  calc
    _ ≤ ((X : ℝ) / (D : ℝ)^2 + 1) * Real.sqrt D := by
      push_cast
      exact mul_le_mul_of_nonneg_right (add_le_add hquotR le_rfl) hroot.le
    _ = shape X D := by
      unfold shape
      field_simp
      nlinarith [hsq, congrArg (fun t : ℝ => (X : ℝ) * t) hsq]

theorem variation_le {B M v : ℕ} {H : ℝ}
    (hM : 0 < M) (hv : 0 < v) (hH : 0 ≤ H) :
    8 * ((6 * (B : ℝ)) / (M * v : ℕ)) +
      128 * H * ((6 * (B : ℝ)) / (M * v : ℕ))^2 ≤
        48 * B + 4608 * H * (B : ℝ)^2 := by
  have hden : (1 : ℝ) ≤ (M * v : ℕ) := by exact_mod_cast Nat.mul_pos hM hv
  have hR : (6 * (B : ℝ)) / (M * v : ℕ) ≤ 6 * B :=
    div_le_self (by positivity) hden
  calc
    _ ≤ 8 * (6 * (B : ℝ)) + 128 * H * (6 * (B : ℝ))^2 := by
      gcongr
    _ = _ := by ring

theorem sqrt_product_le {D v G h H : ℕ}
    (hv : v ≤ G) (hh : h ≤ H) (hH : 1 ≤ H) :
    Real.sqrt (D * v : ℝ) * Real.sqrt (v * h : ℝ) ≤
      Real.sqrt D * G * H := by
  have hhR : (h : ℝ) ≤ (H : ℝ)^2 := by
    have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hhR : (h : ℝ) ≤ H := by exact_mod_cast hh
    nlinarith
  have hsqrth : Real.sqrt (h : ℝ) ≤ H :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, hhR⟩
  calc
    _ = Real.sqrt D * v * Real.sqrt h := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
      calc
        _ = Real.sqrt D * (Real.sqrt (v : ℝ))^2 * Real.sqrt h := by ring
        _ = _ := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ v by positivity)]
    _ ≤ _ := by gcongr

theorem log_modulus_le {M D v X G : ℕ}
    (hM : 0 < M) (hD : 0 < D) (hv : 0 < v) (hDX : D ≤ X) (hvG : v ≤ G) :
    Real.log (M * (D * v) : ℕ) + 1 ≤ Real.log (M * X * G : ℕ) + 1 := by
  apply add_le_add _ le_rfl
  apply Real.log_le_log
  · exact_mod_cast Nat.mul_pos hM (Nat.mul_pos hD hv)
  · exact_mod_cast (show M * (D * v) ≤ M * X * G from by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left M (Nat.mul_le_mul hDX hvG))

/-- A finite budget independent of the varying complementary product.
All the size premises are elementary certificate bounds. -/
theorem weighted_completion_le {B X M D v G W depth length H h : ℕ}
    (hM : 0 < M) (hD : 0 < D) (hv : 0 < v)
    (hDX : D ≤ X) (hvG : v ≤ G) (hH : 1 ≤ H) (hh : h ≤ H)
    (hW : (D * v).primeFactors.card ≤ W + depth) (hlen : length * D ≤ X) :
    (8 * ((6 * (B : ℝ)) / (M * v : ℕ)) +
      128 * H * ((6 * (B : ℝ)) / (M * v : ℕ))^2) *
      (((length / (M * (D * v)) + 1 : ℕ) : ℝ) *
        ((Real.log (M * (D * v) : ℕ) + 1) *
          ((4 : ℝ)^(D * v).primeFactors.card *
            Real.sqrt (D * v : ℝ) * Real.sqrt (v * h : ℝ) * M))) ≤
    ((48 * B + 4608 * (H : ℝ) * (B : ℝ)^2) *
      (Real.log (M * X * G : ℕ) + 1) * (4 : ℝ)^(W + depth) * G * H * M) *
        shape X D := by
  have hmod : (1 : ℝ) ≤ (M * (D * v) : ℕ) := by
    exact_mod_cast Nat.mul_pos hM (Nat.mul_pos hD hv)
  have hlog : 0 ≤ Real.log (M * (D * v) : ℕ) + 1 :=
    add_nonneg (Real.log_nonneg hmod) zero_le_one
  have hDq : D ≤ M * (D * v) := by
    exact (Nat.le_mul_of_pos_right D hv).trans (Nat.le_mul_of_pos_left (D * v) hM)
  have hs := blockCount_mul_sqrt_le hD hDq hlen
  have hvar := variation_le (B := B) hM hv (show (0 : ℝ) ≤ H by positivity)
  have hlogs := log_modulus_le hM hD hv hDX hvG
  have hroots := sqrt_product_le (D := D) hvG hh hH
  let C : ℝ := (48 * B + 4608 * (H : ℝ) * (B : ℝ)^2) *
    (Real.log (M * X * G : ℕ) + 1) * (4 : ℝ)^(W + depth) * G * H * M
  have hC : 0 ≤ C := by
    dsimp [C]
    have hbiglog := hlog.trans hlogs
    positivity
  calc
    _ ≤ (48 * B + 4608 * (H : ℝ) * (B : ℝ)^2) *
        (((length / (M * (D * v)) + 1 : ℕ) : ℝ) *
          ((Real.log (M * X * G : ℕ) + 1) *
            ((4 : ℝ)^(W + depth) * (Real.sqrt D * G * H) * M))) := by
      apply mul_le_mul hvar _ (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul hlogs _ (by positivity) (hlog.trans hlogs)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [mul_assoc]
      exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hW) hroots (by positivity) (by positivity)
    _ = C * (((length / (M * (D * v)) + 1 : ℕ) : ℝ) * Real.sqrt D) := by dsimp [C]; ring
    _ ≤ C * shape X D := mul_le_mul_of_nonneg_left hs hC

end Erdos387Proof.MediumCompletionShape
