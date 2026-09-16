import Erdos439Power

#print axioms Erdos439Power.full_resolution
#print axioms Erdos439Power.integer_resolution
#print axioms Erdos439Power.full_resolution_explicit
#print axioms Erdos439Power.integer_resolution_explicit
#print axioms Erdos439Power.hasNormalizedPowerFourierDecay
#print axioms Erdos439Power.exists_dilation_complete_sums
#print axioms Erdos439Power.exists_minorArc_threshold
#print axioms Erdos439Power.norm_transform_le_major_parameter
#print axioms Erdos439.powerResolution_of_normalizedPowerFourierDecay

/-- Every finite colouring of the positive integers has two distinct equally coloured
integers whose sum is a `k`-th power, for every `k ≥ 2`. -/
example : Erdos439Power.FullStatement := Erdos439Power.full_resolution

/-- The same statement with every auxiliary definition unfolded. -/
example : ∀ k : ℕ, 2 ≤ k → ∀ r : ℕ, ∀ colour : ℕ → Fin r,
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ colour x = colour y ∧ x + y = z ^ k :=
  Erdos439Power.full_resolution

/-- The integer-domain wording of the problem page. -/
example : ∀ k : ℕ, 2 ≤ k → ∀ r : ℕ, ∀ colour : ℤ → Fin r,
    ∃ x y z : ℤ, x ≠ y ∧ colour x = colour y ∧ x + y = z ^ k :=
  Erdos439Power.integer_resolution
