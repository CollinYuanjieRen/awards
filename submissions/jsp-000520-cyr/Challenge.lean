/-
Comparator-style challenge module for JSP-000520 / Erdős Problem #640 (scoped component, k = 3).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos640Challenge

/-- `f` is a valid value of the page's `f(k)`: every graph with chromatic number `≥ f` contains an
odd cycle whose vertex set spans a subgraph of chromatic number `≥ k`. -/
def SpansOddCycle (k f : ℕ) : Prop :=
  ∀ (V : Type) (G : SimpleGraph V), (f : ℕ∞) ≤ G.chromaticNumber →
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length ∧
      (k : ℕ∞) ≤ (G.induce {x | x ∈ c.support}).chromaticNumber

/-- The least valid value of `f(k)` (`0` if there is none). -/
noncomputable def spanThreshold (k : ℕ) : ℕ := sInf {f : ℕ | SpansOddCycle k f}

theorem spanThreshold_three : spanThreshold 3 = 3 := by
  sorry

theorem spansOddCycle_three_three : SpansOddCycle 3 3 := by
  sorry

theorem exists_oddCycle_induce_three_le {V : Type*} (G : SimpleGraph V)
    (h : 3 ≤ G.chromaticNumber) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length ∧
      3 ≤ (G.induce {x | x ∈ c.support}).chromaticNumber := by
  sorry

theorem not_spansOddCycle_three_of_le_two (f : ℕ) (hf : f ≤ 2) : ¬ SpansOddCycle 3 f := by
  sorry

theorem three_le_chromaticNumber_induce_of_odd {V : Type*} (G : SimpleGraph V) {v : V}
    (c : G.Walk v v) (hc : Odd c.length) :
    3 ≤ (G.induce {x | x ∈ c.support}).chromaticNumber := by
  sorry

end Erdos640Challenge
