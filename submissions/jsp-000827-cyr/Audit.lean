import Jsp827

/-!
Kernel audit for the JSP-000827 / Erdős #994 development: prints the axioms of every root.
Expected for all: `[propext, Classical.choice, Quot.sound]` (or a subset of these).
-/

#print axioms Erdos994.not_khintchineFixedSet
#print axioms Erdos994.exists_counterexample_ae
#print axioms RokhlinTower.NatAction.exists_tower
#print axioms RokhlinTower.exists_separated_subset
#print axioms Erdos994.smoothAction_free
#print axioms Erdos994.half_visits
#print axioms Erdos994.measure_badSet_le
#print axioms Erdos994.measure_goodSet_ge

/-- The exact fixed-set predicate of the source, re-stated here to fix the theorem face. -/
example : ¬ (∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Ioo (0 : ℝ) 1 →
    ∀ᵐ α : ℝ, Filter.Tendsto (Erdos994.visitAverage E α) Filter.atTop
      (nhds (MeasureTheory.volume E).toReal)) :=
  Erdos994.not_khintchineFixedSet
