import MerLeanExperiment.SimultaneousApproximation
import MerLeanExperiment.Subdivision

open Filter
open scoped Topology

namespace Erdos492Real

noncomputable section

/-- The two mesh errors can be made small uniformly above a natural cutoff. -/
theorem eventually_small_exponential_mesh {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ q : ℕ, B ≤ q →
      Real.exp (-(q : ℝ)) < ε / 4 ∧ Real.exp (1 / (q : ℝ)) - 1 < ε := by
  have hnat : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hbottom : Tendsto (fun q : ℕ => Real.exp (-(q : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hnat)
  have hinv : Tendsto (fun q : ℕ => 1 / (q : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnat
  have hmesh : Tendsto (fun q : ℕ => Real.exp (1 / (q : ℝ)) - 1) atTop (𝓝 0) := by
    simpa using (Real.continuous_exp.continuousAt.tendsto.comp hinv).sub_const 1
  have hb := (tendsto_order.mp hbottom).2 (ε / 4) (by positivity)
  have hm := (tendsto_order.mp hmesh).2 ε hε
  obtain ⟨B, hB⟩ := eventually_atTop.mp (hb.and hm)
  exact ⟨max B 1, le_max_right _ _, fun q hq => hB q ((le_max_left _ _).trans hq)⟩

/-- The same large denominator realizes all finite logarithmic approximations
and the actual exponential-grid mesh bounds. -/
theorem exists_finite_parameters (N : ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ q : ℕ, 0 < q ∧ Real.exp (-(q : ℝ)) < ε / 4 ∧
      Real.exp (1 / (q : ℝ)) - 1 < ε ∧
      ∀ m : ℕ, m ≤ N → ∃ z : ℤ, |(q : ℝ) * Real.log (m : ℝ) - z| < δ := by
  obtain ⟨B, hB, hmesh⟩ := eventually_small_exponential_mesh hε
  obtain ⟨q, hq, happ⟩ := exists_large_simultaneous_approximation
    (fun m : Fin (N + 1) => Real.log (m.val : ℝ)) B hB δ hδ
  refine ⟨q, by omega, (hmesh q hq).1, (hmesh q hq).2, ?_⟩
  intro m hm
  exact happ ⟨m, by omega⟩

end

end Erdos492Real
