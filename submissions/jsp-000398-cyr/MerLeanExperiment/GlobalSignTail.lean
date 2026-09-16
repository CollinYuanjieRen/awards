import MerLeanExperiment.BlockExceptional
import MerLeanExperiment.SubdivisionEnumeration

open Classical Set

namespace Erdos492Real

noncomputable section

theorem exists_nat_scale_bounds {α : ℝ} (hα : 0 < α) :
    ∃ b : ℕ, 2 ≤ b ∧ 1 / (b : ℝ) ≤ α ∧ α ≤ b := by
  obtain ⟨b, hb⟩ := exists_nat_gt (max 2 (max α (1 / α)))
  have hb2 : (2 : ℝ) < b := (le_max_left _ _).trans_lt hb
  have hαb : α < b := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hb
  have hinvb : 1 / α < (b : ℝ) :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hb
  have hbpos : (0 : ℝ) < b := by linarith
  refine ⟨b, by exact_mod_cast hb2.le, ?_, hαb.le⟩
  apply (div_le_iff₀ hbpos).mpr
  have := (div_lt_iff₀ hα).mp hinvb
  nlinarith

/-- The actual sign on a global sample agrees with its finite block's common
base sign whenever finite dilation invariance applies. The block-location and
exceptional-set hypotheses are all explicit and will be discharged by the
natural cutoff estimates and Borel--Cantelli. -/
theorem global_sample_sign_eq (P : ℕ → FiniteDivision)
    (hFine : ∀ k, (P k).Fine (blockEpsilon k)) (E : ℕ → Set ℝ) (k : ℕ)
    (hInvariant : ∀ x : ℝ, 0 ≤ x → x < 1 → x ∉ E k →
      ∀ m : ℕ, 1 ≤ m → m ≤ blockCutoff (k + 1) → (m : ℝ) * x < 1 →
        divisionSign ((P k).points : Set ℝ) ((m : ℝ) * x) =
          divisionSign ((P k).points : Set ℝ) x)
    {α : ℝ} (hα : 0 < α) (havoid : α ∉ scaledExceptional E k)
    {m : ℕ} (hm : 1 ≤ m) (hmB : m ≤ blockCutoff (k + 1))
    (hleft : (blockCutoff k : ℝ) + 1 ≤ (m : ℝ) * α)
    (hright : (m : ℝ) * α < blockCutoff (k + 1)) :
    divisionSign (globalEndpoints P) ((m : ℝ) * α) =
      divisionSign ((P k).points : Set ℝ) (α / (blockCutoff (k + 1) : ℝ)) := by
  have hB : (0 : ℝ) < blockCutoff (k + 1) := by
    exact_mod_cast blockCutoff_pos (k + 1)
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hαB : α < blockCutoff (k + 1) := by
    have : α ≤ (m : ℝ) * α := by nlinarith
    exact this.trans_lt hright
  rw [divisionSign_global_eq P hFine k _ hleft hright]
  have hinv := hInvariant (α / (blockCutoff (k + 1) : ℝ))
    (div_nonneg hα.le hB.le) ((div_lt_one hB).mpr hαB) havoid m hm hmB
    (by rw [← mul_div_assoc]; exact (div_lt_one hB).mpr hright)
  simpa only [mul_div_assoc] using hinv

theorem sequence_sample_sign_eq (P : ℕ → FiniteDivision) {a : ℕ → ℝ}
    (hrange : range a = globalEndpoints P) (hmono : StrictMono a) (x : ℝ) :
    (if x ∈ sequenceRegion a (1 / 2) then (1 : ℝ) else -1) =
      divisionSign (globalEndpoints P) x := by
  rw [← lowerRegion_eq_sequenceRegion hrange hmono (1 / 2)]
  rfl

end

end Erdos492Real
