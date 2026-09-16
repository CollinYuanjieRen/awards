import MerLeanExperiment.ResidueCount

namespace Erdos441

/-- A finite set of residue classes has discrepancy at most its cardinality
in an integer interval. -/
theorem residue_set_discrepancy (a b : ℤ) (r : ℕ) (hr : 0 < r) (hab : a ≤ b)
    (R : Finset (ZMod r)) :
    |(({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) ∈ R}).card : ℚ) -
      ((b - a : ℤ) : ℚ) / r * R.card| ≤ R.card := by
  have hresidue (x : ℤ) (v : ZMod r) :
      (((x : ℤ) : ZMod r) = v) ↔ Int.ModEq (r : ℤ) x (v.val : ℤ) := by
    have hv : (v.val : ZMod r) = v :=
      @ZMod.natCast_zmod_val r ⟨Nat.ne_of_gt hr⟩ v
    calc
      (((x : ℤ) : ZMod r) = v) ↔
          (((x : ℤ) : ZMod r) = (v.val : ZMod r)) := by rw [hv]
      _ ↔ Int.ModEq (r : ℤ) x (v.val : ℤ) := by
        simpa only [Int.cast_natCast] using
          (ZMod.intCast_eq_intCast_iff x (v.val : ℤ) r)
  have hsingle (v : ZMod r) :
      |((({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) = v}).card : ℚ) -
          ((b - a : ℤ) : ℚ) / r)| ≤ 1 := by
    simpa only [hresidue] using
      residue_count_discrepancy a b (v.val : ℤ) r hr hab
  have hcard :
      (∑ v ∈ R, ({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) = v}).card) =
        ({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) ∈ R}).card :=
    Finset.sum_card_fiberwise_eq_card_filter
      ((Finset.Ioc a b : Finset ℤ)) R (fun x : ℤ => ((x : ℤ) : ZMod r))
  have hdecomp :
      (({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) ∈ R}).card : ℚ) -
          ((b - a : ℤ) : ℚ) / r * R.card =
        ∑ v ∈ R,
          ((({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) = v}).card : ℚ) -
            ((b - a : ℤ) : ℚ) / r) := by
    rw [← hcard]
    push_cast
    rw [Finset.sum_sub_distrib]
    simp
    ring
  rw [hdecomp]
  calc
    |∑ v ∈ R,
        ((({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) = v}).card : ℚ) -
          ((b - a : ℤ) : ℚ) / r)|
        ≤ ∑ v ∈ R,
            |((({x ∈ (Finset.Ioc a b : Finset ℤ) | ((x : ℤ) : ZMod r) = v}).card : ℚ) -
              ((b - a : ℤ) : ℚ) / r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ R, (1 : ℚ) := by
      exact Finset.sum_le_sum fun v hv => hsingle v
    _ = R.card := by simp

end Erdos441
