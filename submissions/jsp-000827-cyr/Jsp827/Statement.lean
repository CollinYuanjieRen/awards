import Mathlib

/-!
# Erdős Problem 994 (JSP-000827): frozen target statement

Source (erdosproblems.com/994, hashed in `ref/erdos994-statement.txt`; Khintchine 1923;
disproved by Marstrand, Proc. LMS 21 (1970) 540–556): "Let `E ⊆ (0,1)` be a measurable
subset with Lebesgue measure `λ(E)`. Is it true that, for almost all `α`,
`lim_{n→∞} (1/n) ∑_{1 ≤ k ≤ n} 1_{{kα} ∈ E} = λ(E)`?"  The historical (fixed-set) reading,
restored in upstream issue #72: `E` is fixed first and the exceptional null set of `α`
may depend on `E`.  Answer: no.

The definitions `visitAverage`, `HasExpectedLimit`, `KhintchineFixedSet` are reproduced
verbatim from plby/lean-proofs `ErdosProblems/Erdos994.lean` (commit 8822f7dd, Apache 2.0,
formal authors Codex / GPT-5.6 Sol; hashed copy in `ref/plby-Erdos994.lean`) so that the
two developments are directly comparable.  plby refutes only the quantifier-swapped
`∀ᵐ α, ∀ E` reading; the fixed-set statement below is what Marstrand disproved.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace Erdos994

attribute [local instance] Classical.propDecidable

/-- The normalized number of visits of the fractional parts
`fract (k * α)`, `1 ≤ k ≤ n`, to `E`.  At `n = 0` this is `0`. -/
noncomputable def visitAverage (E : Set ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n,
      if Int.fract ((k : ℝ) * α) ∈ E then (1 : ℝ) else 0) / (n : ℝ)

/-- The visit averages for `E` and `α` converge to the Lebesgue measure of `E`. -/
def HasExpectedLimit (E : Set ℝ) (α : ℝ) : Prop :=
  Tendsto (visitAverage E α) atTop (𝓝 (volume E).toReal)

/-- The conventional fixed-set quantifier order of Khintchine's historical conjecture.
Here the exceptional null set is allowed to depend on `E`. -/
def KhintchineFixedSet : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → E ⊆ Ioo (0 : ℝ) 1 →
    ∀ᵐ α : ℝ, HasExpectedLimit E α

/-! The two roots `not_khintchineFixedSet` and `exists_counterexample_ae` are proved in
`Jsp827/Root.lean` from the development in `Marstrand/Main.lean`; this file only
fixes the definitions and the bridge below. -/

theorem not_khintchineFixedSet_of_exists
    (h : ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ᵐ α : ℝ, ¬ HasExpectedLimit E α) : ¬ KhintchineFixedSet := by
  intro hK
  obtain ⟨E, hE, hEI, hbad⟩ := h
  have hgood := hK E hE hEI
  have hfalse : ∀ᵐ α : ℝ, False := by
    filter_upwards [hgood, hbad] with α h1 h2
    exact h2 h1
  have hzero : (volume : Measure ℝ) univ = 0 := by simp [ae_iff] at hfalse
  simp at hzero

end Erdos994
