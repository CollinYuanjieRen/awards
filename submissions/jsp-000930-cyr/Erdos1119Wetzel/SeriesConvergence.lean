import Mathlib

/-!
# Entire functions from node series

For a sequence of nodes `w : ℕ → ℂ` let `nodePoly w n z = ∏_{i < n} (z - w i)`.  If the
coefficients satisfy `‖ε n‖ ≤ nodeBound w n = 1 / (n! ∏_{i<n} (1 + ‖w i‖))`, then on the disc
`‖z‖ ≤ R` each term is bounded by `(R + 1)^n / n!`, so the series `∑ ε n * nodePoly w n z`
converges locally uniformly and its sum is an entire function (Erdős's series (2)).
-/

open Finset

/-- The node polynomial `∏_{i < n} (z - w i)`. -/
def nodePoly (w : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∏ i ∈ range n, (z - w i)

/-- The coefficient bound `1 / (n! ∏_{i < n} (1 + ‖w i‖))`. -/
noncomputable def nodeBound (w : ℕ → ℂ) (n : ℕ) : ℝ :=
  ((n.factorial : ℝ) * ∏ i ∈ range n, (1 + ‖w i‖))⁻¹

/-- The sum of the node series. -/
noncomputable def nodeSeries (w : ℕ → ℂ) (ε : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n, ε n * nodePoly w n z

/-- The coefficient bound is strictly positive. -/
theorem nodeBound_pos (w : ℕ → ℂ) (n : ℕ) : 0 < nodeBound w n := by
  refine inv_pos.2 (mul_pos ?_ (Finset.prod_pos fun i _ ↦ by positivity))
  exact_mod_cast n.factorial_pos

/-- `nodePoly w n` vanishes at every node `w i` with `i < n`. -/
theorem nodePoly_eq_zero_of_lt (w : ℕ → ℂ) {i n : ℕ} (h : i < n) : nodePoly w n (w i) = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.2 h) (sub_self _)

/-- For injective nodes, `nodePoly w n (w n) ≠ 0`. -/
theorem nodePoly_self_ne_zero {w : ℕ → ℂ} (hw : Function.Injective w) (n : ℕ) :
    nodePoly w n (w n) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _i hi ↦
    sub_ne_zero.2 fun h ↦ (Finset.mem_range.1 hi).ne' (hw h)

/-- The term bound on the disc of radius `R ≥ 0`. -/
theorem norm_term_le {w : ℕ → ℂ} {ε : ℕ → ℂ} (hε : ∀ n, ‖ε n‖ ≤ nodeBound w n) {R : ℝ}
    (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖ε n * nodePoly w n z‖ ≤ (R + 1) ^ n / n.factorial := by
  have hP : (0 : ℝ) < ∏ i ∈ range n, (1 + ‖w i‖) := Finset.prod_pos fun i _ ↦ by positivity
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hpoly : ‖nodePoly w n z‖ ≤ (R + 1) ^ n * ∏ i ∈ range n, (1 + ‖w i‖) := by
    have hnorm : ‖nodePoly w n z‖ = ∏ i ∈ range n, ‖z - w i‖ := norm_prod _ _
    rw [hnorm]
    calc ∏ i ∈ range n, ‖z - w i‖
        ≤ ∏ i ∈ range n, ((R + 1) * (1 + ‖w i‖)) := by
          refine Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) fun i _ ↦ ?_
          have h1 : ‖z - w i‖ ≤ R + ‖w i‖ := (norm_sub_le _ _).trans (by linarith)
          nlinarith [norm_nonneg (w i), mul_nonneg hR (norm_nonneg (w i))]
      _ = (R + 1) ^ n * ∏ i ∈ range n, (1 + ‖w i‖) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [norm_mul]
  refine (mul_le_mul (hε n) hpoly (norm_nonneg _) (nodeBound_pos w n).le).trans (le_of_eq ?_)
  rw [nodeBound]
  field_simp

/-- The node series converges absolutely at every point. -/
theorem nodeSeries_summable {w : ℕ → ℂ} {ε : ℕ → ℂ} (hε : ∀ n, ‖ε n‖ ≤ nodeBound w n)
    (z : ℂ) : Summable (fun n ↦ ε n * nodePoly w n z) :=
  Summable.of_norm_bounded (Real.summable_pow_div_factorial (‖z‖ + 1))
    fun n ↦ norm_term_le hε (norm_nonneg z) le_rfl n

/-- The sum of the node series is an entire function. -/
theorem nodeSeries_differentiable {w : ℕ → ℂ} {ε : ℕ → ℂ} (hε : ∀ n, ‖ε n‖ ≤ nodeBound w n) :
    Differentiable ℂ (nodeSeries w ε) := by
  intro z
  have hR : (0 : ℝ) ≤ ‖z‖ + 1 := by positivity
  have hopen : IsOpen (Metric.ball (0 : ℂ) (‖z‖ + 1)) := Metric.isOpen_ball
  have hterm : ∀ n : ℕ, Differentiable ℂ fun x : ℂ ↦ ε n * nodePoly w n x := by
    intro n
    unfold nodePoly
    fun_prop
  have hd : DifferentiableOn ℂ (fun x : ℂ ↦ ∑' n : ℕ, ε n * nodePoly w n x)
      (Metric.ball (0 : ℂ) (‖z‖ + 1)) :=
    Complex.differentiableOn_tsum_of_summable_norm
      (Real.summable_pow_div_factorial (‖z‖ + 1 + 1)) (fun n ↦ (hterm n).differentiableOn) hopen
      fun n x hx ↦ norm_term_le hε hR (mem_ball_zero_iff.1 hx).le n
  exact hd.differentiableAt (hopen.mem_nhds (by simp))

/-- At the node `w n` only the first `n + 1` terms contribute. -/
theorem nodeSeries_apply_node {w : ℕ → ℂ} {ε : ℕ → ℂ} (_hε : ∀ n, ‖ε n‖ ≤ nodeBound w n)
    (n : ℕ) : nodeSeries w ε (w n) = ∑ k ∈ range (n + 1), ε k * nodePoly w k (w n) := by
  refine tsum_eq_sum fun k hk ↦ ?_
  have hk' : n < k := by
    simp only [Finset.mem_range, not_lt] at hk
    omega
  rw [nodePoly_eq_zero_of_lt w hk', mul_zero]
