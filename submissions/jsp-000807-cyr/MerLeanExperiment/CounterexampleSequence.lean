import MerLeanExperiment.FiniteModel

/-!
# Extracting a sequence of finite counterexamples

Failure of the eventual finite-model lower bound supplies counterexamples at
arbitrarily large sizes.  This file makes the recursive choice of strictly
increasing sizes explicit.
-/

open Finset

namespace Erdos973

/-- A configuration at size `n` for which every controlled power sum is at
most the proposed exponential lower bound. -/
def FiniteCounterexampleAt (lambda : ℝ) (n : ℕ) : Prop :=
  ∃ z : Fin n → ℂ, (∀ j, 1 ≤ ‖z j‖) ∧
    ∀ k ∈ Icc 2 (n + 1),
      ‖powerSum z k‖ ≤ Real.exp (-lambda * (n : ℝ))

/-- The eventual finite-model lower bound at one fixed exponent. -/
def EventualFiniteLowerBoundAt (lambda : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : Fin n → ℂ,
    (∀ j, 1 ≤ ‖z j‖) →
    ∃ k ∈ Icc 2 (n + 1),
      Real.exp (-lambda * (n : ℝ)) < ‖powerSum z k‖

/-- A strictly increasing sequence of counterexample sizes and configurations
at a fixed exponent. -/
def CounterexampleSequenceAt (lambda : ℝ) : Prop :=
  ∃ (size : ℕ → ℕ) (z : ∀ m, Fin (size m) → ℂ),
    StrictMono size ∧
    (∀ m j, 1 ≤ ‖z m j‖) ∧
    ∀ m k, k ∈ Icc 2 (size m + 1) →
      ‖powerSum (z m) k‖ ≤ Real.exp (-lambda * (size m : ℝ))

/-- Failure of the eventual lower bound at a positive exponent yields a
strictly increasing sequence of finite counterexamples, with no change to the
controlled interval or to the non-strict upper bound. -/
theorem exists_counterexampleSequence_of_not_eventualFiniteLowerBoundAt
    {lambda : ℝ} (_hlambda : 0 < lambda)
    (hfail : ¬ EventualFiniteLowerBoundAt lambda) :
    ∃ (size : ℕ → ℕ) (z : ∀ m, Fin (size m) → ℂ),
      StrictMono size ∧
      (∀ m j, 1 ≤ ‖z m j‖) ∧
      ∀ m k, k ∈ Icc 2 (size m + 1) →
        ‖powerSum (z m) k‖ ≤ Real.exp (-lambda * (size m : ℝ)) := by
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ FiniteCounterexampleAt lambda n := by
    intro N
    by_contra hnone
    apply hfail
    refine ⟨N, fun n hn z hz => ?_⟩
    by_contra hlarge
    apply hnone
    refine ⟨n, hn, z, hz, ?_⟩
    intro k hk
    by_contra hnotle
    exact hlarge ⟨k, hk, lt_of_not_ge hnotle⟩
  let pick : ℕ → ℕ := fun N => Classical.choose (hbad N)
  have hpick : ∀ N, N ≤ pick N ∧ FiniteCounterexampleAt lambda (pick N) := by
    intro N
    exact Classical.choose_spec (hbad N)
  let size : ℕ → ℕ := Nat.rec (pick 0) (fun _ previous => pick (previous + 1))
  have hsize_succ : ∀ m, size m < size (m + 1) := by
    intro m
    change size m < pick (size m + 1)
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (hpick (size m + 1)).1
  have hsize : StrictMono size := strictMono_nat_of_lt_succ hsize_succ
  have hsize_bad : ∀ m, FiniteCounterexampleAt lambda (size m) := by
    intro m
    cases m with
    | zero =>
        change FiniteCounterexampleAt lambda (pick 0)
        exact (hpick 0).2
    | succ m =>
        change FiniteCounterexampleAt lambda (pick (size m + 1))
        exact (hpick (size m + 1)).2
  let z : ∀ m, Fin (size m) → ℂ :=
    fun m => Classical.choose (hsize_bad m)
  refine ⟨size, z, hsize, ?_, ?_⟩
  · intro m
    exact (Classical.choose_spec (hsize_bad m)).1
  · intro m
    exact (Classical.choose_spec (hsize_bad m)).2

/-- Packaged form of the extraction theorem. -/
theorem counterexampleSequenceAt_of_not_eventualFiniteLowerBoundAt
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hfail : ¬ EventualFiniteLowerBoundAt lambda) :
    CounterexampleSequenceAt lambda :=
  exists_counterexampleSequence_of_not_eventualFiniteLowerBoundAt hlambda hfail

/-- Contradiction interface for the final theorem: ruling out every strictly
increasing counterexample sequence proves the eventual finite-model bound. -/
theorem eventualFiniteLowerBoundAt_of_not_counterexampleSequenceAt
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hno : ¬ CounterexampleSequenceAt lambda) :
    EventualFiniteLowerBoundAt lambda := by
  by_contra hfail
  exact hno (counterexampleSequenceAt_of_not_eventualFiniteLowerBoundAt
    hlambda hfail)

/-- Proving that no positive exponent admits a counterexample sequence closes
the full finite-model lower bound. -/
theorem finiteUniformExteriorLowerBound_of_no_counterexampleSequence
    (hno : ∀ lambda : ℝ, 0 < lambda → ¬ CounterexampleSequenceAt lambda) :
    FiniteUniformExteriorLowerBound := by
  intro lambda hlambda
  exact eventualFiniteLowerBoundAt_of_not_counterexampleSequenceAt
    hlambda (hno lambda hlambda)

end Erdos973
