import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Topology.Continuous

/-! Extend orbit-sum bounds from a dense orbit at continuity points. -/

namespace Kesten

/-- A bound on a dense set extends to every continuity point of a real-valued function. -/
theorem abs_le_of_denseRange_of_continuousAt {X ι : Type*} [TopologicalSpace X]
    (e : ι → X) (g : X → ℝ) (x : X) (C : ℝ) (he : DenseRange e)
    (hg : ContinuousAt g x) (hbound : ∀ i : ι, |g (e i)| ≤ C) : |g x| ≤ C := by
  have hx : x ∈ closure (Set.range e) := by
    rw [he.closure_range]
    exact Set.mem_univ x
  have himage : g '' Set.range e ⊆ Set.Icc (-C) C := by
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact abs_le.mp (hbound i)
  have hgx : g x ∈ closure (Set.Icc (-C) C) :=
    closure_mono himage (mem_closure_image hg hx)
  rw [isClosed_Icc.closure_eq] at hgx
  exact abs_le.mpr hgx

/-- A dense-orbit bound for Birkhoff sums extends almost everywhere when the summand is
almost everywhere continuous and the dynamics preserve the measure. -/
theorem ae_birkhoffSum_bound_of_denseRange {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (T : X → X) (f : X → ℝ) (μ : MeasureTheory.Measure X)
    (x₀ : X) (C : ℝ) (hT : Continuous T)
    (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (hdense : DenseRange fun j : ℕ ↦ (T^[j]) x₀)
    (hf : ∀ᵐ x ∂μ, ContinuousAt f x)
    (hbound : ∀ n : ℕ, |birkhoffSum T f n x₀| ≤ C) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, |birkhoffSum T f n x| ≤ 2 * C := by
  have hf_iterate : ∀ k : ℕ, ∀ᵐ x ∂μ, ContinuousAt f ((T^[k]) x) := by
    intro k
    exact (hmp.quasiMeasurePreserving.iterate k).ae hf
  filter_upwards [MeasureTheory.ae_all_iff.2 hf_iterate] with x hx
  intro n
  apply abs_le_of_denseRange_of_continuousAt (fun j : ℕ ↦ (T^[j]) x₀)
    (birkhoffSum T f n) x (2 * C) hdense
  · change ContinuousAt (fun y ↦ ∑ k ∈ Finset.range n, f ((T^[k]) y)) x
    exact tendsto_finsetSum (Finset.range n) fun k _ ↦
      (hx k).comp (hT.iterate k).continuousAt
  · intro j
    have horbit : birkhoffSum T f n ((T^[j]) x₀) =
        birkhoffSum T f (j + n) x₀ - birkhoffSum T f j x₀ := by
      rw [birkhoffSum_add_right_apply]
      ring
    rw [horbit]
    calc
      |birkhoffSum T f (j + n) x₀ - birkhoffSum T f j x₀| ≤
          |birkhoffSum T f (j + n) x₀| + |birkhoffSum T f j x₀| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (birkhoffSum T f (j + n) x₀) (-birkhoffSum T f j x₀)
      _ ≤ C + C := add_le_add (hbound (j + n)) (hbound j)
      _ = 2 * C := by ring

end Kesten
