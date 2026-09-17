import Mathlib

namespace UnitFractions

theorem four_fifths_eq : (1:ℚ)/2 + 1/4 + 1/20 = 4/5 := by norm_num

theorem exists_three_distinct_unit_fractions :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ (1:ℚ)/a + 1/b + 1/c = 4/5 := by
  refine ⟨2, 4, 20, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · push_cast; norm_num

end UnitFractions

#print axioms UnitFractions.four_fifths_eq
#print axioms UnitFractions.exists_three_distinct_unit_fractions
