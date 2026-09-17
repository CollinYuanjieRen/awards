/-
Comparator-style challenge module for JSP-000188 / Erdős Problem #201 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos201Challenge

/-- `S` contains a `k`-term arithmetic progression with positive common difference. -/
def HasAP (k : ℕ) (S : Finset ℤ) : Prop := ∃ a d : ℤ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ S

/-- `S` contains no `k`-term arithmetic progression. -/
def APFree (k : ℕ) (S : Finset ℤ) : Prop := ¬ HasAP k S

open Classical in
/-- The size of the largest `k`-AP-free subset of `T`. -/
noncomputable def apFreeMax (k : ℕ) (T : Finset ℤ) : ℕ :=
  (T.powerset.filter (fun S => APFree k S)).sup Finset.card

/-- `R_k(N)`: the largest `k`-AP-free subset of `{1, …, N}`. -/
noncomputable def R (k N : ℕ) : ℕ := apFreeMax k (Finset.Icc (1 : ℤ) N)

/-- `G_k(N)`: the least, over all `N`-element sets of integers, of the largest `k`-AP-free subset
size. -/
noncomputable def G (k N : ℕ) : ℕ := sInf {m : ℕ | ∃ T : Finset ℤ, T.card = N ∧ apFreeMax k T = m}

theorem G_le_R (k N : ℕ) : G k N ≤ R k N := by
  sorry

theorem R_three_five : R 3 5 = 4 := by
  sorry

theorem G_three_five_le : G 3 5 ≤ 3 := by
  sorry

theorem apFreeMax_le_iff (k : ℕ) (T : Finset ℤ) (m : ℕ) :
    apFreeMax k T ≤ m ↔ ∀ S ⊆ T, APFree k S → S.card ≤ m := by
  sorry

theorem G_le_apFreeMax (k N : ℕ) (T : Finset ℤ) (hT : T.card = N) : G k N ≤ apFreeMax k T := by
  sorry

end Erdos201Challenge
