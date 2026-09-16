import MerLeanExperiment.Target

example :
    Filter.Tendsto (fun N : ℕ => (Erdos441.g N : ℝ) / Real.sqrt ((9 / 8 : ℝ) * N))
      Filter.atTop (nhds 1) ∧
    ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ (Erdos441.erdosConstruction N).card < Erdos441.g N :=
  Erdos441.erdos_441_complete

#print axioms Erdos441.sum_int_interval_subtype
#print axioms Erdos441.sum_int_interval_prefix
#print axioms Erdos441.eventually_weighted_grid_packing
#print axioms Erdos441.grid_middle_le_weighted_density
#print axioms Erdos441.grid_scale_power
#print axioms Erdos441.sqrt_nine_eighth
#print axioms Erdos441.eventually_concrete_upper
#print axioms Erdos441.chen_uniform_upper
#print axioms Erdos441.chen_asymptotic
#print axioms Erdos441.erdos_441_complete
#print axioms Erdos441.erdosConstruction_not_eventually_extremal
