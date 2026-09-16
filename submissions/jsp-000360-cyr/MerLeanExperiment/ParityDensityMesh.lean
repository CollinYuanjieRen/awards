import MerLeanExperiment.ParityRegions
import Mathlib.Tactic

namespace Erdos441

theorem parity_density_mesh_bound (A : Finset ℕ) (a b delta R : ℝ)
    (r : ℤ) (m : ℕ) (hm : 0 < m) (hd : 0 < delta) (hR : 0 < R)
    (hlo : (m : ℝ) * delta ≤ b - a)
    (hhi : b - a < ((m : ℝ) + 1) * delta) :
    delta * R * parityDensity A a b R r ≤
      (∑ s : Fin m, ((consecutiveCell A a delta R r s.val).card : ℝ)) / m +
        delta * (delta * R + 1) / (b - a) := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hw : 0 < b - a := (mul_pos hmR hd).trans_le hlo
  let C : ℝ := ∑ s : Fin m, ((consecutiveCell A a delta R r s.val).card : ℝ)
  let F : ℝ := (parityRegion A a b R r).card
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hfull : F ≤ C + delta * R + 1 := by
    have h := parity_region_le_cells_add A a b delta R r m hd hR hlo hhi
    have heq := Fin.sum_univ_eq_sum_range
      (fun s : ℕ => ((consecutiveCell A a delta R r s).card : ℝ)) m
    change F ≤ C + delta * R + 1
    dsimp only [C]
    rw [heq]
    exact h
  have hratio : delta / (b - a) ≤ 1 / (m : ℝ) := by
    apply (div_le_div_iff₀ hw hmR).mpr
    nlinarith
  have heq : delta * R * parityDensity A a b R r = delta / (b - a) * F := by
    unfold parityDensity
    change delta * R * (F / ((b - a) * R)) = _
    field_simp
  calc
    delta * R * parityDensity A a b R r = delta / (b - a) * F := heq
    _ ≤ delta / (b - a) * (C + delta * R + 1) :=
      mul_le_mul_of_nonneg_left hfull (div_nonneg hd.le hw.le)
    _ ≤ C / m + delta * (delta * R + 1) / (b - a) := by
      have hh := mul_le_mul_of_nonneg_right hratio hC
      calc
        _ = delta / (b - a) * C + delta * (delta * R + 1) / (b - a) := by ring
        _ ≤ 1 / (m : ℝ) * C + delta * (delta * R + 1) / (b - a) := add_le_add hh le_rfl
        _ = _ := by ring

end Erdos441

#print axioms Erdos441.parity_density_mesh_bound
