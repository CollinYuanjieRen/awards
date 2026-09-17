/-
Comparator-style challenge module for JSP-000516 / Erdős Problem #635 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Main.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos635Challenge

/-- The page's condition at `t = 1`: `A ⊆ {1, …, N}` and `b − a ∤ b` whenever `a < b` are in `A`. -/
def Adm (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ ∀ a ∈ A, ∀ b ∈ A, a < b → ¬ (b - a) ∣ b

open Classical in
/-- The largest size of an admissible subset of `{1, …, N}`. -/
noncomputable def maxAdm (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun A => Adm N A)).sup Finset.card

theorem maxAdm_eq (N : ℕ) : maxAdm N = (N + 1) / 2 := by
  sorry

theorem isGreatest_adm_card (N : ℕ) :
    IsGreatest {m : ℕ | ∃ A : Finset ℕ, Adm N A ∧ A.card = m} ((N + 1) / 2) := by
  sorry

theorem card_le_of_adm (N : ℕ) (A : Finset ℕ) (h : Adm N A) : A.card ≤ (N + 1) / 2 := by
  sorry

theorem adm_odds (N : ℕ) : Adm N ((Finset.Icc 1 N).filter (fun n => ¬ 2 ∣ n)) := by
  sorry

theorem card_odds (N : ℕ) : ((Finset.Icc 1 N).filter (fun n => ¬ 2 ∣ n)).card = (N + 1) / 2 := by
  sorry

end Erdos635Challenge
