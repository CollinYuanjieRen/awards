import MerLeanExperiment.CounterexampleSequence
import MerLeanExperiment.FirstSumScale
import MerLeanExperiment.ExteriorParameterDisk
import MerLeanExperiment.ExteriorOverconvergence
import MerLeanExperiment.ExteriorDiskIdentities
import MerLeanExperiment.VariableEmpiricalMeasure

/-!
# The uniform exterior lower bound

This module connects the sequential algebraic and analytic estimates to the
Cauchy-transform rigidity theorem.  The Proposition 3.3 implementation is
imported from `ExteriorOverconvergence`.
-/

open Filter Finset Metric Set
open scoped Topology

namespace Erdos973

private theorem normalizedRootLogDeriv_eq_reciprocal_average
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ j, 1 ≤ ‖z j‖)
    {w : ℂ} (hw : 1 < ‖w‖) :
    normalizedRootLogDeriv (fun _ => n) (fun _ => z) 0 w =
      ((n : ℂ)⁻¹) * ∑ j, (w - (z j)⁻¹)⁻¹ := by
  have hne : ∀ j, w ≠ (z j)⁻¹ := by
    intro j heq
    have hinv : ‖(z j)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact (inv_le_one₀ (zero_lt_one.trans_le (hz j))).2 (hz j)
    rw [heq] at hw
    exact (not_lt_of_ge hinv) hw
  have hderiv : deriv (fun u => (rootProduct z).eval u) w =
      (rootProduct z).derivative.eval w :=
    (rootProduct z).hasDerivAt w |>.deriv
  have hlog := logDeriv_eval_rootProduct z hz w hne
  rw [logDeriv_apply, hderiv] at hlog
  rw [← hlog]
  unfold normalizedRootLogDeriv
  simp only
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  ring

/-- No positive exponential rate admits a strictly increasing sequence of
finite counterexamples. -/
theorem not_counterexampleSequenceAt (lambda : ℝ) (hlambda : 0 < lambda) :
    ¬ CounterexampleSequenceAt lambda := by
  rintro ⟨size₀, z₀, hsize₀, hz₀, hsmall₀⟩
  obtain ⟨phi₀, c, hphi₀, hlimit₀, hc0, hc1, hscale⟩ :=
    normalized_first_sum_scale hlambda size₀ hsize₀ z₀ hz₀ hsmall₀
  let phi : ℕ → ℕ := fun m => phi₀ (m + 1)
  let size : ℕ → ℕ := fun m => size₀ (phi m)
  let z : ∀ m, Fin (size m) → ℂ := fun m => z₀ (phi m)
  have hphi : StrictMono phi := by
    intro m n hmn
    exact hphi₀ (Nat.add_lt_add_right hmn 1)
  have hsize : StrictMono size := hsize₀.comp hphi
  have hsizepos : ∀ m, 0 < size m := by
    intro m
    have hindex : 1 ≤ phi m := by
      calc
        1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
        _ ≤ phi₀ (m + 1) := hphi₀.le_apply
    exact lt_of_lt_of_le Nat.zero_lt_one (hindex.trans hsize₀.le_apply)
  have hz : ∀ m j, 1 ≤ ‖z m j‖ := fun m => hz₀ (phi m)
  have hsmall : ∀ m k, k ∈ Finset.Icc 2 (size m + 1) →
      ‖powerSum (z m) k‖ ≤ Real.exp (-lambda * size m) :=
    fun m => hsmall₀ (phi m)
  have hlimit : Tendsto
      (fun m => (-powerSum (z m) 1) / (size m : ℂ)) atTop (𝓝 c) := by
    have ht := (tendsto_add_atTop_iff_nat 1).2 hlimit₀
    simpa [phi, size, z] using ht
  obtain ⟨center, radius, a, Q, R, eta, hradius, ha, hQ0, hR0, heta,
      hRdef, hRexp, hQ1, hexterior, hrealnorm, hmarginTail,
      hmarginPerturb⟩ :=
    exists_exterior_parameter_disk hlambda hc0 hc1 hscale
  have hreal : ∀ w ∈ closedBall center radius, a < (c * w).re :=
    fun w hw => (hrealnorm w hw).1
  have hnorm : ∀ w ∈ closedBall center radius, ‖c * w‖ < Q :=
    fun w hw => (hrealnorm w hw).2
  obtain ⟨sigma, hsigma, _hestimates, huniform⟩ :=
    exterior_overconvergence_sequence lambda size hsize z c center
      radius a Q R eta hlambda hradius ha hQ0 hR0 heta hRdef hRexp hQ1
      hexterior hreal hnorm hmarginTail hmarginPerturb hsmall hlimit
  let alpha : ∀ m, Fin (size m) → UnitDisk := fun m j =>
    reciprocalDiskPoint (z m j) (hz m j)
  have hfinite : ∀ m w, w ∈ closedBall center radius →
      ((size m : ℂ)⁻¹) * ∑ j, (w - (alpha m j : ℂ))⁻¹ =
        normalizedRootLogDeriv size z m w := by
    intro m w hw
    have hbase := normalizedRootLogDeriv_eq_reciprocal_average
      (z m) (hz m) (hexterior w hw)
    change normalizedRootLogDeriv (fun _ => size m) (fun _ => z m) 0 w =
      ((size m : ℂ)⁻¹) * ∑ j, (w - (z m j)⁻¹)⁻¹ at hbase
    simpa [alpha, normalizedRootLogDeriv] using hbase.symm
  have hconv : ∀ w ∈ ball center radius, Tendsto
      (fun m => ((size m : ℂ)⁻¹) * ∑ j, (w - (alpha m j : ℂ))⁻¹)
      atTop (𝓝 c) := by
    intro w hw
    have hwclosed : w ∈ closedBall center radius := ball_subset_closedBall hw
    have ht := huniform.tendsto_at hwclosed
    apply ht.congr'
    filter_upwards with m
    exact (hfinite m w hwclosed).symm
  have hczero := constant_limit_variableEmpiricalCauchyTransform_eq_zero
    size hsizepos alpha (ball center radius) c isOpen_ball
    (Metric.nonempty_ball.mpr hradius)
    (fun w hw => hexterior w (ball_subset_closedBall hw)) hconv
  exact hc0.ne' (by simpa [hczero])

/-- Luo--Yang--Zhu's eventual finite-model lower bound. -/
theorem finiteUniformExteriorLowerBound : FiniteUniformExteriorLowerBound :=
  finiteUniformExteriorLowerBound_of_no_counterexampleSequence
    not_counterexampleSequenceAt

end Erdos973
