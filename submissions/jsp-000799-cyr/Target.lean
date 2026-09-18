import Mathlib

/-!
Frozen statement of the JSP-000799 / Erdős #960 target, against Mathlib only, with `sorry`.
NOT imported by the build; it freezes the statement for comparison with the proved roots.
-/

open Finset Filter Asymptotics

namespace Erdos960Target

abbrev Point := ℝ × ℝ

def OrdinaryPair (A : Finset Point) (p q : Point) : Prop :=
  p ∈ A ∧ q ∈ A ∧ p ≠ q ∧ ∀ x ∈ A, Collinear ℝ ({p, q, x} : Set Point) → x = p ∨ x = q

theorem ordinaryPair_comm (A : Finset Point) (p q : Point) :
    OrdinaryPair A p q ↔ OrdinaryPair A q p := by
  have key : ∀ x : Point, ({p, q, x} : Set Point) = {q, p, x} := fun x => Set.insert_comm p q {x}
  constructor
  · rintro ⟨hp, hq, hne, h⟩
    exact ⟨hq, hp, hne.symm, fun x hx hc => (h x hx (by rw [key]; exact hc)).symm⟩
  · rintro ⟨hq, hp, hne, h⟩
    exact ⟨hp, hq, hne.symm, fun x hx hc => (h x hx (by rw [← key]; exact hc)).symm⟩

def IsOrdinaryLine (A : Finset Point) (e : Sym2 Point) : Prop :=
  Sym2.lift ⟨fun p q => OrdinaryPair A p q, fun p q => propext (ordinaryPair_comm A p q)⟩ e

open Classical in
noncomputable def ordCount (A : Finset Point) : ℕ :=
  (A.sym2.filter (IsOrdinaryLine A)).card

def NoKCollinear (A : Finset Point) (k : ℕ) : Prop :=
  ∀ B ⊆ A, B.card = k → ¬ Collinear ℝ (B : Set Point)

def HasOrdinaryClique (A : Finset Point) (r : ℕ) : Prop :=
  ∃ B ⊆ A, B.card = r ∧ ∀ p ∈ B, ∀ q ∈ B, p ≠ q → OrdinaryPair A p q

def Forces (r k n t : ℕ) : Prop :=
  ∀ A : Finset Point, A.card = n → NoKCollinear A k → t ≤ ordCount A → HasOrdinaryClique A r

noncomputable def f (r k n : ℕ) : ℕ := sInf {t : ℕ | Forces r k n t}

/-- The resolution (Alexeev–Putterman–Sawhney–Sellke–Valiant, arXiv:2604.06609, Theorem 2.1):
for every fixed `r ≥ 3`, `k ≥ 4`, the threshold satisfies `f_{r,k}(n) ≥ n²/12 − 10n/3` for all
`n ≥ 72`; in particular it is neither `o(n²)` nor `O(n)`. -/
theorem erdos_960 (r k : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) :
    (∀ n : ℕ, 72 ≤ n → (n : ℝ) ^ 2 / 12 - 10 / 3 * n ≤ (f r k n : ℝ)) ∧
    ¬ ((fun n : ℕ => (f r k n : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) ^ 2) ∧
    ¬ ((fun n : ℕ => (f r k n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ)) := by
  sorry

end Erdos960Target
