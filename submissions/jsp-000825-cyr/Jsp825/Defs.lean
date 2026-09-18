import Mathlib

/-!
# JSP-000825 / Erdős #992 — definitions

Erdős [Er64b, p. 56]: let `x₁ < x₂ < ⋯` be an infinite sequence of integers.  Is it true that, for
almost all `α ∈ [0,1]`, the discrepancy
`D(N) = max_{I ⊆ [0,1]} |#{n ≤ N : {α xₙ} ∈ I} − |I| N|`
satisfies `D(N) ≪ N^{1/2} (log N)^{o(1)}`?  Or even `D(N) ≪ N^{1/2} (log log N)^{O(1)}`?

Both questions have the answer **no** (Berkes–Philipp 1994): there is a sequence such that, for
almost all `α ∈ [0,1]`, `limsup D(N) / (N log N)^{1/2} > 0`.
-/

open MeasureTheory Filter Set

namespace Erdos992

/-- The sub-intervals of `[0,1]` (any kind of interval: an order-connected subset of `[0,1]`). -/
def SubInterval : Type := {I : Set ℝ // I ⊆ Icc 0 1 ∧ I.OrdConnected}

open Classical in
/-- `#{n ≤ N : {α xₙ} ∈ I}` — the number of the first `N` fractional parts lying in `I`
(the sequence is indexed from `0`, so `x 0, …, x (N-1)` are the first `N` terms). -/
noncomputable def count (x : ℕ → ℤ) (α : ℝ) (N : ℕ) (I : Set ℝ) : ℕ :=
  ((Finset.range N).filter fun n ↦ Int.fract (α * (x n : ℝ)) ∈ I).card

/-- The error of one interval: `#{n ≤ N : {α xₙ} ∈ I} − |I| N`, with `|I|` the length of `I`. -/
noncomputable def err (x : ℕ → ℤ) (α : ℝ) (N : ℕ) (I : Set ℝ) : ℝ :=
  (count x α N I : ℝ) - (volume I).toReal * N

/-- The discrepancy `D(N) = max_{I ⊆ [0,1]} |#{n ≤ N : {α xₙ} ∈ I} − |I| N|` of the problem. -/
noncomputable def D (x : ℕ → ℤ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup (Set.range fun I : SubInterval ↦ |err x α N I.1|)

/-- The first question of the problem: for every sequence and almost all `α ∈ [0,1]`,
`D(N) ≪ N^{1/2} (log N)^{o(1)}`, read as: for every `ε > 0` there is a constant `C` with
`D(N) ≤ C N^{1/2} (log N)^ε` for all large `N`. -/
def Erdos992Statement : Prop :=
  ∀ x : ℕ → ℤ, StrictMono x →
    ∀ᵐ α ∂volume, α ∈ Icc (0 : ℝ) 1 →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
        D x α N ≤ C * Real.sqrt N * Real.log N ^ ε

/-- The "or even" question: for every sequence and almost all `α ∈ [0,1]`,
`D(N) ≪ N^{1/2} (log log N)^{O(1)}`, read as: there are constants `C` and `K` with
`D(N) ≤ C N^{1/2} (log log N)^K` for all large `N`. -/
def Erdos992StatementLogLog : Prop :=
  ∀ x : ℕ → ℤ, StrictMono x →
    ∀ᵐ α ∂volume, α ∈ Icc (0 : ℝ) 1 →
      ∃ C K : ℝ, ∀ᶠ N : ℕ in atTop,
        D x α N ≤ C * Real.sqrt N * Real.log (Real.log N) ^ K

end Erdos992
