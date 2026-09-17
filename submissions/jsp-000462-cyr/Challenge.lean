/-
Comparator-style challenge module for JSP-000462 / Erdős Problem #572 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there. Every object is Mathlib's (`extremalNumber`, `cycleGraph`, `turanGraph`, `Free`,
`Colorable`); nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos572Challenge

open SimpleGraph

theorem le_extremalNumber_oddCycle (n k : ℕ) :
    n ^ 2 / 4 ≤ extremalNumber n (cycleGraph (2 * k + 3)) := by
  sorry

theorem le_extremalNumber_oddCycle' (n k : ℕ) (hk : 1 ≤ k) :
    n ^ 2 / 4 ≤ extremalNumber n (cycleGraph (2 * k + 1)) := by
  sorry

theorem le_extremalNumber_of_not_colorable_two (n : ℕ) {W : Type*} (H : SimpleGraph W)
    (h : ¬ H.Colorable 2) : n ^ 2 / 4 ≤ extremalNumber n H := by
  sorry

theorem extremalNumber_cycleGraph_three (n : ℕ) : extremalNumber n (cycleGraph 3) = n ^ 2 / 4 := by
  sorry

theorem turanGraph_two_colorable (n : ℕ) : (turanGraph n 2).Colorable 2 := by
  sorry

theorem cycleGraph_odd_free_turanGraph_two (n k : ℕ) :
    (cycleGraph (2 * k + 3)).Free (turanGraph n 2) := by
  sorry

end Erdos572Challenge
