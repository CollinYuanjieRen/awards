import MerLeanExperiment.BlockConstruction

open Classical MeasureTheory Set

namespace Erdos492Real

noncomputable section

/-- Choose the finite divisions and their actual exceptional sets once, before
choosing any real dilation parameter. The finite lemma is an explicit
intermediate dependency and must be instantiated by its proof at the root. -/
theorem exists_finite_division_family (hfinite : FiniteSubdivisionLemma) :
    ∃ (P : ℕ → FiniteDivision) (E : ℕ → Set ℝ),
      (∀ k, (P k).Fine (blockEpsilon k)) ∧
      (∀ k, MeasurableSet (E k)) ∧
      (∀ k, volume (E k) < ENNReal.ofReal (blockEpsilon k)) ∧
      ∀ k, ∀ x : ℝ, 0 ≤ x → x < 1 → x ∉ E k →
        ∀ m : ℕ, 1 ≤ m → m ≤ blockCutoff (k + 1) → (m : ℝ) * x < 1 →
          divisionSign ((P k).points : Set ℝ) ((m : ℝ) * x) =
            divisionSign ((P k).points : Set ℝ) x := by
  choose P hP using fun k =>
    hfinite (blockCutoff (k + 1)) (blockEpsilon k) (blockEpsilon_pos k)
  have hInv : ∀ k, (P k).DilationInvariant (blockCutoff (k + 1)) (blockEpsilon k) :=
    fun k => (hP k).2
  unfold FiniteDivision.DilationInvariant at hInv
  choose E hEm hEv hEi using hInv
  exact ⟨P, E, fun k => (hP k).1, hEm, hEv, hEi⟩

end

end Erdos492Real
