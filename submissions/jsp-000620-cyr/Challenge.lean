/- leanprover/lean4:v4.34.0-rc1  mathlib 1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d -/
/-
Comparator challenge for the JSP-000620 submission (Erdős Problem 754).

This module intentionally contains only statements (proved by `sorry`) and imports only
Mathlib, in the format used by leanprover/comparator challenge modules. The definitions of
`Erdos754.f` below are copied verbatim from the plby/lean-proofs comparator challenge
`src/latest/ComparatorChallenges/ErdosProblems/Erdos754.lean` (commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e), so that `f` is exactly the function of the
existing upper-bound formalization. The solution module is `JSP620.Target`.
-/

import Mathlib

namespace Erdos754

abbrev E4 := EuclideanSpace ℝ (Fin 4)

def IsFavorite {W : Type*} (p : W → E4) (c : W → ℝ) (x y : W) : Prop :=
  x ≠ y ∧ dist (p x) (p y) = c x

noncomputable def favoriteDegree (P : Finset E4) (c : P → ℝ) (x : P) : ℕ :=
  open scoped Classical in
  (Finset.univ.filter fun y : P => IsFavorite (fun z : P => (z : E4)) c x y).card

def Attainable (n k : ℕ) : Prop :=
  ∃ P : Finset E4, P.card = n ∧
    ∃ c : P → ℝ, (∀ x, 0 < c x) ∧ ∀ x, k ≤ favoriteDegree P c x

noncomputable def f (n : ℕ) : ℕ :=
  if n = 0 then 0 else sSup {k : ℕ | Attainable n k}

theorem erdos_754 : ∃ C : ℝ, ∀ n : ℕ, (f n : ℝ) ≤ (n : ℝ) / 2 + C := by
  sorry

end Erdos754

namespace Erdos754Lower

open Erdos754

theorem half_le_f (n : ℕ) : n / 2 ≤ f n := by
  sorry

theorem half_add_two_le_f_of_eight_dvd (n : ℕ) (hn : n ≠ 0) (h8 : 8 ∣ n) :
    n / 2 + 2 ≤ f n := by
  sorry

theorem erdos_754_two_sided :
    (∀ n : ℕ, n / 2 ≤ f n) ∧
    (∀ n : ℕ, n ≠ 0 → 8 ∣ n → n / 2 + 2 ≤ f n) ∧
    (∃ C : ℝ, ∀ n : ℕ, (f n : ℝ) ≤ (n : ℝ) / 2 + C) := by
  sorry

theorem abs_f_sub_half_le : ∃ C : ℝ, ∀ n : ℕ, |(f n : ℝ) - (n : ℝ) / 2| ≤ C := by
  sorry

theorem f_sub_half_isBigO :
    (fun n : ℕ => (f n : ℝ) - (n : ℝ) / 2) =O[Filter.atTop] (fun _ : ℕ => (1 : ℝ)) := by
  sorry

end Erdos754Lower
