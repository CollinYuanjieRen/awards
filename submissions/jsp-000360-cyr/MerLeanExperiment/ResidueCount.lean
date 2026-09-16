import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic

namespace Erdos441

/-- A residue class has discrepancy at most one in an integer interval. -/
theorem residue_count_discrepancy (a b v : ℤ) (r : ℕ)
    (hr : 0 < r) (hab : a ≤ b) :
    |(({x ∈ Finset.Ioc a b | Int.ModEq (r : ℤ) x v}).card : ℚ) -
      ((b - a : ℤ) : ℚ) / r| ≤ 1 := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hrZ : (0 : ℤ) < r := by exact_mod_cast hr
  have habQ : (a : ℚ) ≤ b := by exact_mod_cast hab
  have hmono : ⌊(a - v : ℚ) / r⌋ ≤ ⌊(b - v : ℚ) / r⌋ :=
    Int.floor_mono (div_le_div_of_nonneg_right (sub_le_sub_right habQ _) hrQ.le)
  have hc := Int.Ioc_filter_modEq_card a b hrZ v
  simp only [Int.cast_natCast] at hc
  rw [max_eq_left (sub_nonneg.mpr hmono)] at hc
  have hcQ : (({x ∈ Finset.Ioc a b | Int.ModEq (r : ℤ) x v}).card : ℚ) =
      (⌊(b - v : ℚ) / r⌋ : ℚ) - (⌊(a - v : ℚ) / r⌋ : ℚ) := by
    exact_mod_cast hc
  rw [hcQ]
  have haL := Int.floor_le ((a - v : ℚ) / r)
  have haU := Int.lt_floor_add_one ((a - v : ℚ) / r)
  have hbL := Int.floor_le ((b - v : ℚ) / r)
  have hbU := Int.lt_floor_add_one ((b - v : ℚ) / r)
  have hdiff : ((b - a : ℤ) : ℚ) / r =
      (b - v : ℚ) / r - (a - v : ℚ) / r := by
    push_cast
    ring
  rw [hdiff, abs_le]
  constructor <;> linarith

end Erdos441

#print axioms Erdos441.residue_count_discrepancy
