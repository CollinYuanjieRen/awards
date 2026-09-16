import Erdos1119Wetzel.SeriesConvergence

/-!
# Choosing the coefficients

Given injective nodes `w`, functions `g n` to avoid, and a set `S` meeting every punctured open
disc, Erdős chooses the coefficients `ε n` one at a time: the value of the node series at `w n`
is `c n + ε n * nodePoly w n (w n)` where `c n = ∑_{k<n} ε k * nodePoly w k (w n)` depends only
on earlier coefficients, and `nodePoly w n (w n) ≠ 0`, so a small `ε n` puts the value into
`S \ {g n (w n)}`.
-/

open Finset

/-- The prefix approximations of a sequence built one entry at a time: `coeffPrefix F n` has its
first `n` entries chosen by the step rule `F`, which reads off the entries already chosen. -/
def coeffPrefix (F : ℕ → (ℕ → ℂ) → ℂ) : ℕ → ℕ → ℂ
  | 0 => fun _ ↦ 0
  | n + 1 => Function.update (coeffPrefix F n) n (F n (coeffPrefix F n))

/-- The last entry of `coeffPrefix F (n + 1)` is the value chosen at step `n`. -/
theorem coeffPrefix_succ_self (F : ℕ → (ℕ → ℂ) → ℂ) (n : ℕ) :
    coeffPrefix F (n + 1) n = F n (coeffPrefix F n) :=
  Function.update_self n _ _

/-- The prefixes are stable below their length: entry `k` is fixed once step `k` has been taken. -/
theorem coeffPrefix_apply_of_lt (F : ℕ → (ℕ → ℂ) → ℂ) : ∀ {n k : ℕ}, k < n →
    coeffPrefix F n k = coeffPrefix F (k + 1) k
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hk | rfl
    · rw [coeffPrefix, Function.update_of_ne hk.ne _ _, coeffPrefix_apply_of_lt F hk]
    · rfl

/-- Coefficients can be chosen, one at a time, so that the partial value at every node lies in
`S`, avoids `g n (w n)`, and stays within the convergence bound. -/
theorem exists_coefficients {w : ℕ → ℂ} (hw : Function.Injective w) (g : ℕ → ℂ → ℂ) (S : Set ℂ)
    (hS : ∀ c : ℂ, ∀ δ : ℝ, 0 < δ → ∀ v : ℂ, ∃ s ∈ S, s ≠ v ∧ ‖s - c‖ < δ) :
    ∃ ε : ℕ → ℂ, (∀ n, ‖ε n‖ ≤ nodeBound w n) ∧
      ∀ n, (∑ k ∈ range (n + 1), ε k * nodePoly w k (w n)) ∈ S ∧
        (∑ k ∈ range (n + 1), ε k * nodePoly w k (w n)) ≠ g n (w n) := by
  classical
  choose s hsS hsne hsd using hS
  have hP : ∀ n : ℕ, (0 : ℝ) < ‖nodePoly w n (w n)‖ := fun n ↦
    norm_pos_iff.mpr (nodePoly_self_ne_zero hw n)
  have hδ : ∀ n : ℕ, 0 < nodeBound w n * ‖nodePoly w n (w n)‖ := fun n ↦
    mul_pos (nodeBound_pos w n) (hP n)
  set F : ℕ → (ℕ → ℂ) → ℂ := fun n f ↦
    (s (∑ k ∈ range n, f k * nodePoly w k (w n)) (nodeBound w n * ‖nodePoly w n (w n)‖) (hδ n)
        (g n (w n)) - ∑ k ∈ range n, f k * nodePoly w k (w n)) / nodePoly w n (w n)
  have hFapp : ∀ (m : ℕ) (f : ℕ → ℂ), F m f =
      (s (∑ k ∈ range m, f k * nodePoly w k (w m)) (nodeBound w m * ‖nodePoly w m (w m)‖) (hδ m)
        (g m (w m)) - ∑ k ∈ range m, f k * nodePoly w k (w m)) / nodePoly w m (w m) :=
    fun _ _ ↦ rfl
  refine ⟨fun n ↦ coeffPrefix F (n + 1) n, fun n ↦ ?_, fun n ↦ ?_⟩
  · show ‖coeffPrefix F (n + 1) n‖ ≤ nodeBound w n
    rw [coeffPrefix_succ_self, hFapp, norm_div, div_le_iff₀ (hP n)]
    exact (hsd _ _ _ _).le
  · show (∑ k ∈ range (n + 1), coeffPrefix F (k + 1) k * nodePoly w k (w n)) ∈ S ∧
      (∑ k ∈ range (n + 1), coeffPrefix F (k + 1) k * nodePoly w k (w n)) ≠ g n (w n)
    have hpre : ∑ k ∈ range n, coeffPrefix F n k * nodePoly w k (w n)
        = ∑ k ∈ range n, coeffPrefix F (k + 1) k * nodePoly w k (w n) :=
      Finset.sum_congr rfl fun k hk ↦ by
        rw [coeffPrefix_apply_of_lt F (Finset.mem_range.mp hk)]
    have hval : ∑ k ∈ range (n + 1), coeffPrefix F (k + 1) k * nodePoly w k (w n)
        = s (∑ k ∈ range n, coeffPrefix F (k + 1) k * nodePoly w k (w n))
            (nodeBound w n * ‖nodePoly w n (w n)‖) (hδ n) (g n (w n)) := by
      rw [Finset.sum_range_succ, coeffPrefix_succ_self, hFapp, hpre,
        div_mul_cancel₀ _ (nodePoly_self_ne_zero hw n), add_sub_cancel]
    exact ⟨hval ▸ hsS _ _ _ _, hval ▸ hsne _ _ _ _⟩

/-- **Erdős's interpolation lemma.**  For injective nodes `w`, any functions `g n`, and any set
`S` meeting every punctured open disc, there is an entire function taking values in `S` at all
nodes and differing from `g n` at `w n`. -/
theorem exists_entire_interpolant {w : ℕ → ℂ} (hw : Function.Injective w) (g : ℕ → ℂ → ℂ)
    (S : Set ℂ) (hS : ∀ c : ℂ, ∀ δ : ℝ, 0 < δ → ∀ v : ℂ, ∃ s ∈ S, s ≠ v ∧ ‖s - c‖ < δ) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ∀ n, f (w n) ∈ S ∧ f (w n) ≠ g n (w n) := by
  obtain ⟨ε, hε, hvals⟩ := exists_coefficients hw g S hS
  refine ⟨nodeSeries w ε, nodeSeries_differentiable hε, fun n ↦ ?_⟩
  rw [nodeSeries_apply_node hε n]
  exact hvals n
