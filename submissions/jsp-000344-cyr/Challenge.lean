/-
Comparator-style challenge module for JSP-000344 / Erdős Problem #417 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Main.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos417Challenge

/-- The set `{φ(m) : 1 ≤ m ≤ x}`. -/
def totientValues (x : ℕ) : Finset ℕ := (Finset.Icc 1 x).image Nat.totient

open Classical in
/-- The set of totient values `φ(m) ≤ x` (`m ≥ 1`). -/
noncomputable def totientValuesLE (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter (fun v => ∃ m, 1 ≤ m ∧ Nat.totient m = v)

/-- `V'(x) = #{φ(m) : 1 ≤ m ≤ x}`. -/
def V' (x : ℕ) : ℕ := (totientValues x).card

/-- `V(x) = #{φ(m) ≤ x : 1 ≤ m}`. -/
noncomputable def V (x : ℕ) : ℕ := (totientValuesLE x).card

theorem V'_le_V (x : ℕ) : V' x ≤ V x := by
  sorry

theorem totientValues_subset (x : ℕ) : totientValues x ⊆ totientValuesLE x := by
  sorry

theorem mem_totientValues (x v : ℕ) :
    v ∈ totientValues x ↔ ∃ m, 1 ≤ m ∧ m ≤ x ∧ Nat.totient m = v := by
  sorry

theorem mem_totientValuesLE (x v : ℕ) :
    v ∈ totientValuesLE x ↔ v ≤ x ∧ ∃ m, 1 ≤ m ∧ Nat.totient m = v := by
  sorry

theorem V'_le_V_real (x : ℝ) : V' ⌊x⌋₊ ≤ V ⌊x⌋₊ := by
  sorry

end Erdos417Challenge
