import Mathlib

/-!
# Erdős Problem 1011 (Erdős–Gallai `f₃(n)`): definitions and elementary inputs

`f_r(n)` is the least `m` such that every graph on `n` vertices with at least `m` edges and
chromatic number at least `r` contains a triangle.  For `r = 3` (chromatic number `≥ 3`, i.e. not
`2`-colourable) Erdős and Gallai proved `f₃(n) = ⌊(n - 1)² / 4⌋ + 2`.  This file records `f₃`,
Mantel's theorem as a corollary of Mathlib's Turán bound, the arithmetic inequality used in the
upper bound, and the equivalence between "not `2`-colourable" and "chromatic number `≥ 3`".
-/


open Finset SimpleGraph

namespace Erdos1011

/-- Erdős's `f₃(n)`: the least `m` such that every graph on `n` vertices with at least `m` edges and
chromatic number at least `3` (i.e. not `2`-colourable) contains a triangle. -/
noncomputable def f3 (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.Colorable 2 → m ≤ G.edgeSet.ncard → ¬ G.CliqueFree 3}

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **Mantel's theorem** (from Mathlib's Turán bound): a triangle-free graph on `N` vertices has at
most `N² / 4` edges. -/
theorem mantel (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    #G.edgeFinset ≤ Fintype.card V ^ 2 / 4 := by
  have h2 : #G.edgeFinset ≤ turanNumber (Fintype.card V) 2 := h.card_edgeFinset_le
  rwa [turanNumber_two] at h2

/-- The arithmetic behind the upper bound: for odd `m` with `5 ≤ m ≤ n`,
`m + 2 (n - m) + ⌊(n - m)² / 4⌋ ≤ ⌊(n - 1)² / 4⌋ + 1`. -/
theorem bound_arith {n m : ℕ} (hm : Odd m) (h5 : 5 ≤ m) (hmn : m ≤ n) :
    m + 2 * (n - m) + (n - m) ^ 2 / 4 ≤ (n - 1) ^ 2 / 4 + 1 := by
  obtain ⟨t, rfl⟩ := hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have ht : 2 ≤ t := by omega
  rw [show 2 * t + 1 + k - (2 * t + 1) = k by omega, show 2 * t + 1 + k - 1 = 2 * t + k by omega]
  have key : (2 * t + k) ^ 2 / 4 = k ^ 2 / 4 + (t * k + t ^ 2) := by
    rw [show (2 * t + k) ^ 2 = k ^ 2 + 4 * (t * k + t ^ 2) by ring,
      Nat.add_mul_div_left _ _ (by norm_num : 0 < 4)]
  have hlin : 2 * t + 2 * k ≤ t * k + t ^ 2 := by nlinarith
  omega

omit [Fintype V] [DecidableEq V] in
/-- For a finite graph, "not `2`-colourable" is "chromatic number at least `3`". -/
theorem not_colorable_two_iff (G : SimpleGraph V) : ¬ G.Colorable 2 ↔ 3 ≤ G.chromaticNumber := by
  rw [← chromaticNumber_le_iff_colorable, not_le]
  exact ⟨fun h ↦ Order.succ_le_of_lt h, fun h ↦ lt_of_lt_of_le (by norm_num) h⟩

omit [DecidableEq V] in
/-- `edgeSet.ncard` agrees with `#edgeFinset`. -/
theorem edgeSet_ncard_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeSet.ncard = #G.edgeFinset := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]

end Erdos1011
