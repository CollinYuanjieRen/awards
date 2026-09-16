import MerLeanExperiment.PackingCellDefinitions
import MerLeanExperiment.CellCover
import MerLeanExperiment.External.Erdos441

namespace Erdos441

theorem packing_bad_points_le_exceptions (N : ℕ) (A : Finset ℕ) (hA : LcmBounded N A) (D : ℕ) (B R : ℝ) : (packingBadPoints A D B R).card ≤ ((realIntIoc 0 (B * R)).filter fun n => ¬ Nat.Coprime n.natAbs D).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun n : ℕ => (n : ℤ))
  · intro n hn
    obtain ⟨hnA, hupper, hbad⟩ := Finset.mem_filter.mp hn
    have hnpos : 0 < n := by
      have := (Finset.mem_Icc.mp (hA.1 hnA)).1
      omega
    apply Finset.mem_filter.mpr
    refine ⟨(mem_realIntIoc _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
    · change (0 : ℝ) < (n : ℝ)
      exact_mod_cast hnpos
    · change (n : ℝ) ≤ B * R
      exact hupper
    · simpa using hbad
  · intro n _ m _ he
    change (n : ℤ) = (m : ℤ) at he
    exact_mod_cast he

end Erdos441

#print axioms Erdos441.packing_bad_points_le_exceptions
