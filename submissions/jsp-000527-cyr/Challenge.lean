/- leanprover/lean4:v4.34.0-rc1  mathlib 1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d -/
/-
Comparator challenge for the JSP-000527 submission (Erdős Problem 651, Pohoata–Zakharov 2022:
the three-dimensional Erdős–Szekeres numbers are subexponential).  This module contains only
statements proved by `sorry` and imports only Mathlib, in the format of leanprover/comparator
challenge modules.  Every definition below is copied verbatim (including the surrounding
`noncomputable section` and `open` lines) from plby/lean-proofs
`src/latest/ErdosProblems/Erdos651/Definitions.lean` (commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e) and `Erdos651/PohoataZakharovBridge.lean`.
The solution modules are `JSP527.PZ.Main` (dimension three) and `JSP527.PZ.Dimensions` (all dimensions `d ≥ 3`).
-/

import Mathlib

namespace Erdos651

open Filter Set
open scoped Topology

noncomputable section

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

def InGeneralPosition (d : ℕ) (X : Finset (Point d)) : Prop :=
  ∀ S : Finset (Point d), S ⊆ X → S.card = d + 1 →
    AffineIndependent ℝ (fun p : ↥S ↦ (p : Point d))

def InConvexPosition {d : ℕ} (X : Finset (Point d)) : Prop :=
  ∀ x ∈ X, x ∉ convexHull ℝ (↑(X.erase x) : Set (Point d))

def ContainsConvexSubset (d n : ℕ) (X : Finset (Point d)) : Prop :=
  ∃ Y : Finset (Point d), Y ⊆ X ∧ Y.card = n ∧ InConvexPosition Y

def ForcesConvexSubset (d n N : ℕ) : Prop :=
  ∀ X : Finset (Point d), N ≤ X.card → InGeneralPosition d X →
    ContainsConvexSubset d n X

def HasErdosSzekeresNumber (d n : ℕ) : Prop :=
  Set.Nonempty {N : ℕ | ForcesConvexSubset d n N}

noncomputable def erdosSzekeresNumber (d n : ℕ) : ℕ :=
  sInf {N : ℕ | ForcesConvexSubset d n N}

lemma ForcesConvexSubset.mono {d n N M : ℕ} (hNM : N ≤ M)
    (hN : ForcesConvexSubset d n N) : ForcesConvexSubset d n M := by
  intro X hMX hgp
  exact hN X (hNM.trans hMX) hgp

lemma erdosSzekeresNumber_forces {d n : ℕ}
    (h : HasErdosSzekeresNumber d n) :
    ForcesConvexSubset d n (erdosSzekeresNumber d n) := by
  exact Nat.sInf_mem h

lemma erdosSzekeresNumber_le {d n N : ℕ}
    (hN : ForcesConvexSubset d n N) :
    erdosSzekeresNumber d n ≤ N := by
  exact Nat.sInf_le hN

def HasSubexponentialUpperBound (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in Filter.atTop,
      (f n : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ))

def HasExponentialLowerBound (f : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in Filter.atTop, (1 + c) ^ n < (f n : ℝ)

def Erdos651Claim : Prop :=
  HasExponentialLowerBound (erdosSzekeresNumber 3)

def PohoataZakharovConclusion : Prop :=
  HasSubexponentialUpperBound (erdosSzekeresNumber 3)


/-- The literal point-set, epsilon formulation of Theorem 1.1 in
Pohoata--Zakharov: every sufficiently large general-position point set in
three-space whose cardinality is at least `2 ^ (ε * n)` contains `n` points in
convex position. -/
def PohoataZakharovTheoremOneOne : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ X : Finset (Point 3),
        (2 : ℝ) ^ (ε * (n : ℝ)) ≤ (X.card : ℝ) →
        InGeneralPosition 3 X → ContainsConvexSubset 3 n X

end

end Erdos651

namespace PohoataZakharov

open Filter

/-- Premise-free form of the subexponential bound, indexed by `k` with `ε = 1 / (k + 1)`. -/
theorem erdos_651_subexponential_inv (k : ℕ) : ∀ᶠ n : ℕ in atTop,
    (Erdos651.erdosSzekeresNumber 3 n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) := by
  sorry

/-- Pohoata–Zakharov, Theorem 1.1 (point-set form). -/
theorem theorem_one_one : Erdos651.PohoataZakharovTheoremOneOne := by
  sorry

/-- The Erdős–Szekeres number in dimension three exists for every `n`. -/
theorem hasErdosSzekeresNumber_three (n : ℕ) : Erdos651.HasErdosSzekeresNumber 3 n := by
  sorry

/-- `f₃(n) ≤ 2 ^ (o(n))`: the negative answer to Erdős Problem 651. -/
theorem erdos_651_subexponential :
    Erdos651.HasSubexponentialUpperBound (Erdos651.erdosSzekeresNumber 3) := by
  sorry

/-- Erdős's conjectured exponential lower bound `f₃(n) > (1 + c)^n` fails. -/
theorem erdos_651_disproved : ¬ Erdos651.Erdos651Claim := by
  sorry

/-- Pohoata–Zakharov in every dimension `d ≥ 3`: `f_d(n) ≤ 2 ^ (o(n))`. -/
theorem erdos_651_subexponential_all_dimensions (d : ℕ) :
    Erdos651.HasSubexponentialUpperBound (Erdos651.erdosSzekeresNumber (d + 3)) := by
  sorry

/-- Premise-free `k`-indexed form in every dimension `d ≥ 3`. -/
theorem erdos_651_subexponential_inv_all_dimensions (d k : ℕ) : ∀ᶠ n : ℕ in Filter.atTop,
    (Erdos651.erdosSzekeresNumber (d + 3) n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) := by
  sorry

/-- Erdős's conjectured exponential lower bound fails in every dimension `d ≥ 3`. -/
theorem erdos_651_disproved_all_dimensions (d : ℕ) :
    ¬ Erdos651.HasExponentialLowerBound (Erdos651.erdosSzekeresNumber (d + 3)) := by
  sorry

end PohoataZakharov
