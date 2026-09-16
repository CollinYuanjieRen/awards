import MerLeanExperiment.CellDefinitions
import Mathlib.Tactic

namespace Erdos441

theorem mem_realIntIoc (a b : ℝ) (n : ℤ) :
    n ∈ realIntIoc a b ↔ a < (n : ℝ) ∧ (n : ℝ) ≤ b := by
  simp only [realIntIoc, Finset.mem_Ioc, Int.floor_lt, Int.le_floor]

theorem card_realIntIoc_le (a b : ℝ) (hab : a ≤ b) :
    ((realIntIoc a b).card : ℝ) ≤ b - a + 1 := by
  have hc : ((realIntIoc a b).card : ℤ) = ⌊b⌋ - ⌊a⌋ :=
    Int.card_Ioc_of_le _ _ (Int.floor_mono hab)
  have hcR : ((realIntIoc a b).card : ℝ) = (⌊b⌋ : ℝ) - (⌊a⌋ : ℝ) := by
    exact_mod_cast hc
  rw [hcR]
  have hb := Int.floor_le b
  have ha := Int.lt_floor_add_one a
  linarith

theorem cell_point_cover (c delta R E : ℝ) (y n : ℤ)
    (hylo : c * R < (y : ℝ)) (hyhi : (y : ℝ) ≤ c * R + E)
    (hnlo : c * R < (n : ℝ)) (hnhi : (n : ℝ) ≤ (c + delta) * R)
    (hparity : Even (n - y)) :
    n ∈ realIntIoc (c * R) (c * R + E) ∨
      ∃ h ∈ Finset.Icc (1 : ℤ) ⌊delta * R / 2⌋, n = y + 2 * h := by
  by_cases hny : n ≤ y
  · left
    exact (mem_realIntIoc _ _ _).mpr ⟨hnlo, (Int.cast_le.mpr hny).trans hyhi⟩
  · right
    obtain ⟨h, he⟩ := hparity
    have hn : n = y + 2 * h := by omega
    have hh : 1 ≤ h := by omega
    refine ⟨h, Finset.mem_Icc.mpr ⟨hh, ?_⟩, hn⟩
    apply Int.le_floor.mpr
    have hnR : (n : ℝ) = (y : ℝ) + 2 * (h : ℝ) := by exact_mod_cast hn
    nlinarith

end Erdos441

#print axioms Erdos441.mem_realIntIoc
#print axioms Erdos441.card_realIntIoc_le
#print axioms Erdos441.cell_point_cover
