/-
Comparator-style challenge module for JSP-000101 / Erdős Problem #85 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos85Challenge

open SimpleGraph

/-- `f n`: the least `k` such that every graph on `n` vertices with minimum degree `≥ k`
contains a `C₄`. -/
noncomputable def f (n : ℕ) : ℕ :=
  open scoped Classical in
  sInf {k : ℕ | ∀ G : SimpleGraph (Fin n), k ≤ G.minDegree → cycleGraph 4 ⊑ G}

/-- The perfect matching `{0,1}, {2,3}` on four vertices: the witness that `f(4) > 1`. -/
def perfectMatching : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun a b => (a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3))

instance : DecidableRel perfectMatching.Adj := fun a b => by
  unfold perfectMatching; infer_instance

theorem f_four : f 4 = 2 := by
  sorry

theorem f_four_le : f 4 ≤ 2 := by
  sorry

theorem cycleGraph_four_isContained_of_two_le_minDegree (G : SimpleGraph (Fin 4))
    [DecidableRel G.Adj] (h : 2 ≤ G.minDegree) : cycleGraph 4 ⊑ G := by
  sorry

theorem perfectMatching_witness :
    1 ≤ perfectMatching.minDegree ∧ ¬ cycleGraph 4 ⊑ perfectMatching := by
  sorry

theorem two_le_f_four : 2 ≤ f 4 := by
  sorry

end Erdos85Challenge
