/-
JSP-000144: `r_3(14) ≥ 8` via an explicit 3-AP-free subset of `{1, …, 14}`.

The set `S = {1, 2, 4, 5, 10, 11, 13, 14}` has eight elements, lies inside
`Finset.Icc 1 14`, and contains no nontrivial three-term arithmetic progression:
whenever `a, b, c ∈ S` satisfy `a + c = 2 * b`, we must have `a = c`.

This is a finite certificate for the lower bound; no asymptotic statement about
`r_3` is claimed here.
-/
import Mathlib

namespace APFree

def S : Finset ℕ := {1, 2, 4, 5, 10, 11, 13, 14}

/-- `S` is 3-AP-free: the only 3-term APs (a,b,c) inside S are trivial (a = c). -/
theorem S_ap_free : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a + c = 2 * b → a = c := by
  decide

theorem S_card : S.card = 8 := by
  decide

theorem S_subset : S ⊆ Finset.Icc 1 14 := by
  decide

theorem r3_14_ge_8 :
    ∃ T : Finset ℕ, T ⊆ Finset.Icc 1 14 ∧ T.card = 8 ∧
      (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a + c = 2 * b → a = c) :=
  ⟨S, S_subset, S_card, S_ap_free⟩

end APFree

#print axioms APFree.S_ap_free
#print axioms APFree.r3_14_ge_8
