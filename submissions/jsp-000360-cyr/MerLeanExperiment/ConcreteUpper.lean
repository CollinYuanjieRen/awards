import MerLeanExperiment.WeightedGridPacking
import MerLeanExperiment.GridNormalization
import MerLeanExperiment.TailBound

namespace Erdos441

theorem eventually_concrete_upper : ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L ≥ L0, ∀ S : ℕ,
    1 ≤ S → ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ N ≥ N0, ∀ A : Finset ℕ, LcmBounded N A →
        (A.card : ℝ) ≤ (Real.sqrt (9 / 8 : ℝ) + (1 - gridQ L ^ (-1 : ℤ)) +
          (1 / 2 : ℝ) ^ S + epsilon * (Real.sqrt (9 / 8 : ℝ) + 1)) *
            Real.sqrt (N : ℝ) := by
  classical
  obtain ⟨L0, hL0, hweighted⟩ := eventually_weighted_grid_packing
  refine ⟨L0, hL0, ?_⟩
  intro L hL S hS epsilon hepsilon
  have hLone : 1 ≤ L := hL0.trans hL
  obtain ⟨hq, hqL, hq2L, _⟩ := grid_ratio_spec L hLone
  let q := gridQ L
  have hqp : 0 < q := by dsimp [q]; linarith
  let T : ℤ := 2 * (L : ℤ) * (S : ℤ) - 1
  have hLI : (1 : ℤ) ≤ L := by exact_mod_cast hLone
  have hSI : (1 : ℤ) ≤ S := by exact_mod_cast hS
  have hT : (L : ℤ) - 1 ≤ T := by
    dsimp [T]
    nlinarith
  have hT0 : 0 ≤ T := by omega
  have hscale : q ^ (T + 1) = (2 : ℝ) ^ S := by
    dsimp only [T]
    rw [sub_add_cancel]
    exact grid_scale_power q L S hq2L
  obtain ⟨NW, hW⟩ := hweighted L hL T hT epsilon hepsilon
  refine ⟨max 1 NW, le_max_left _ _, ?_⟩
  intro N hN A hA
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNW : NW ≤ N := (le_max_right _ _).trans hN
  let R := Real.sqrt (N : ℝ)
  have hR : 0 < R := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))
  have hR2 : R ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  let c : ℝ := Real.sqrt (9 / 8 : ℝ)
  let D : ℝ := ∑ j ∈ Finset.Icc (-T) (L : ℤ), gridDelta q L j
  have hD : D = c - q ^ (-T) + 1 - q ^ (-1 : ℤ) := by
    dsimp [D, c]
    rw [grid_delta_sum q hq L hLone hqL T hT0, sqrt_nine_eighth]
  have hDle : D ≤ c + 1 := by
    rw [hD]
    have h1 := zpow_pos hqp (-T)
    have h2 := zpow_pos hqp (-1)
    linarith
  have hsmall := positive_prefix_card_le A
    (fun n hn => by have := (Finset.mem_Icc.mp (hA.1 hn)).1; omega)
    (q ^ (-T) * R) (mul_pos (zpow_pos hqp _) hR).le
  have hmiddle : ((intervalRegion A (q ^ (-T)) (q ^ (T + 1)) R).card : ℝ) ≤
      ((1 + epsilon) * D) * R := by
    apply (div_le_iff₀ hR).mp
    exact (grid_middle_le_weighted_density A q hq L T hT0 R hR).trans (hW N hNW A hA)
  have htail := lcm_tail_bound N A hA (q ^ (T + 1) * R)
    (mul_pos (zpow_pos hqp _) hR)
  have htailval : (N : ℝ) / (q ^ (T + 1) * R) = (1 / 2 : ℝ) ^ S * R := by
    rw [hscale, ← hR2]
    calc
      _ = (1 / (2 : ℝ) ^ S) * R := by field_simp
      _ = _ := by rw [div_pow, one_pow]
  rw [htailval] at htail
  have hHJ : q ^ (-T) * R ≤ q ^ (T + 1) * R :=
    mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ hq.le (by omega)) hR.le
  have hpart : (A.card : ℝ) =
      ((A.filter fun n : ℕ => (n : ℝ) ≤ q ^ (-T) * R).card : ℝ) +
      ((intervalRegion A (q ^ (-T)) (q ^ (T + 1)) R).card : ℝ) +
      ((A.filter fun n : ℕ => q ^ (T + 1) * R < (n : ℝ)).card : ℝ) := by
    exact_mod_cast three_region_card_partition A (q ^ (-T) * R) (q ^ (T + 1) * R) hHJ
  have heD := mul_le_mul_of_nonneg_left hDle hepsilon.le
  calc
    (A.card : ℝ) ≤ q ^ (-T) * R + ((1 + epsilon) * D) * R + (1 / 2 : ℝ) ^ S * R := by
      rw [hpart]
      exact add_le_add (add_le_add hsmall hmiddle) htail
    _ = (q ^ (-T) + D + (1 / 2 : ℝ) ^ S + epsilon * D) * R := by ring
    _ ≤ (q ^ (-T) + D + (1 / 2 : ℝ) ^ S + epsilon * (c + 1)) * R := by
      apply mul_le_mul_of_nonneg_right _ hR.le
      linarith
    _ = _ := by rw [hD]; dsimp only [q, c, R]; ring

end Erdos441

#print axioms Erdos441.eventually_concrete_upper
