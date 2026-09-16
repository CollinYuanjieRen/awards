import Mathlib

/-!
# The rational lattice `ℚ + ℚ i`

Erdős's construction takes the prescribed values of the entire functions in a fixed countable
dense subset of `ℂ`.  We use the Gaussian rationals.  The only density property needed is that
every open disc contains a lattice point different from any prescribed value.
-/

/-- The Gaussian rationals `{a + b i : a, b ∈ ℚ}`. -/
def rationalLattice : Set ℂ :=
  {z : ℂ | ∃ a b : ℚ, z = (a : ℂ) + (b : ℂ) * Complex.I}

/-- The Gaussian rationals form a countable set. -/
theorem rationalLattice_countable : rationalLattice.Countable := by
  have h : rationalLattice
      = Set.range (fun p : ℚ × ℚ ↦ (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
    ext z
    constructor
    · rintro ⟨a, b, rfl⟩
      exact ⟨(a, b), rfl⟩
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨a, b, rfl⟩
  rw [h]
  exact Set.countable_range _

/-- Every open disc contains a Gaussian rational different from any prescribed value `v`. -/
theorem rationalLattice_dense_punctured (c : ℂ) {δ : ℝ} (hδ : 0 < δ) (v : ℂ) :
    ∃ s ∈ rationalLattice, s ≠ v ∧ ‖s - c‖ < δ := by
  have hhalf : (0 : ℝ) < δ / 2 := by positivity
  obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show c.re - δ / 2 < c.re + δ / 2 by linarith)
  obtain ⟨b₁, hb₁, hb₁'⟩ := exists_rat_btwn (show c.im - δ / 2 < c.im + δ / 2 by linarith)
  obtain ⟨b₂, hb₂, hb₂'⟩ := exists_rat_btwn hb₁'
  have key : ∀ b : ℚ, c.im - δ / 2 < (b : ℝ) → (b : ℝ) < c.im + δ / 2 →
      ‖((a : ℂ) + (b : ℂ) * Complex.I) - c‖ < δ := by
    intro b hlo hhi
    have hre : ((a : ℂ) + (b : ℂ) * Complex.I - c).re = (a : ℝ) - c.re := by simp
    have him : ((a : ℂ) + (b : ℂ) * Complex.I - c).im = (b : ℝ) - c.im := by simp
    have h₁ : |(a : ℝ) - c.re| < δ / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have h₂ : |(b : ℝ) - c.im| < δ / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    rw [hre, him]
    linarith
  by_cases hv : (a : ℂ) + (b₁ : ℂ) * Complex.I = v
  · refine ⟨(a : ℂ) + (b₂ : ℂ) * Complex.I, ⟨a, b₂, rfl⟩, ?_, key b₂ (by linarith) hb₂'⟩
    rw [← hv]
    intro h
    have him : (b₂ : ℝ) = (b₁ : ℝ) := by simpa using congrArg Complex.im h
    linarith
  · exact ⟨(a : ℂ) + (b₁ : ℂ) * Complex.I, ⟨a, b₁, rfl⟩, hv, key b₁ hb₁ hb₁'⟩
