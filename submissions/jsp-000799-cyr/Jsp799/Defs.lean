import Mathlib

/-!
# JSP-000799 / Erdős #960 — definitions

Erdős [Er84, p.102]: let `r, k ≥ 2` be fixed and let `A ⊂ ℝ²` be a set of `n` points with no `k`
points on a line.  Determine the threshold `f_{r,k}(n)` such that if there are at least
`f_{r,k}(n)` ordinary lines (lines containing exactly two points of `A`) then there is a set
`A' ⊆ A` of `r` points such that all `C(r,2)` lines determined by `A'` are ordinary.
Is it true that `f_{r,k}(n) = o(n²)`, or perhaps even `≪ n`?

Points are pairs of reals; collinearity is Mathlib's affine `Collinear ℝ`.
-/

open Finset

namespace Erdos960

abbrev Point := ℝ × ℝ

/-- The line through the distinct points `p, q ∈ A` is *ordinary* for `A`: no third point of `A`
lies on it. -/
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

/-- The unordered pair `e` spans an ordinary line of `A`. -/
def IsOrdinaryLine (A : Finset Point) (e : Sym2 Point) : Prop :=
  Sym2.lift ⟨fun p q => OrdinaryPair A p q, fun p q => propext (ordinaryPair_comm A p q)⟩ e

open Classical in
/-- The number of ordinary lines of `A` (each ordinary line contains exactly two points of `A`,
so ordinary lines correspond to unordered ordinary pairs). -/
noncomputable def ordCount (A : Finset Point) : ℕ :=
  (A.sym2.filter (IsOrdinaryLine A)).card

/-- Distinct ordinary pairs span distinct lines: if the ordinary pair `{p', q'}` lies on the
line of the ordinary pair `{p, q}` then the two pairs coincide (so `ordCount` is exactly the
number of ordinary lines). -/
theorem ordinaryPair_sym2_eq {A : Finset Point} {p q p' q' : Point} (h : OrdinaryPair A p q)
    (h' : OrdinaryPair A p' q') (hp' : Collinear ℝ ({p, q, p'} : Set Point))
    (hq' : Collinear ℝ ({p, q, q'} : Set Point)) : s(p, q) = s(p', q') := by
  obtain ⟨_, _, _, hline⟩ := h
  obtain ⟨hp'A, hq'A, hp'q', _⟩ := h'
  rcases hline p' hp'A hp' with rfl | rfl <;> rcases hline q' hq'A hq' with rfl | rfl
  · exact absurd rfl hp'q'
  · rfl
  · exact Sym2.eq_swap
  · exact absurd rfl hp'q'

/-- No `k` points of `A` lie on one line. -/
def NoKCollinear (A : Finset Point) (k : ℕ) : Prop :=
  ∀ B ⊆ A, B.card = k → ¬ Collinear ℝ (B : Set Point)

/-- `A` contains `r` points every two of which span an ordinary line of `A`. -/
def HasOrdinaryClique (A : Finset Point) (r : ℕ) : Prop :=
  ∃ B ⊆ A, B.card = r ∧ ∀ p ∈ B, ∀ q ∈ B, p ≠ q → OrdinaryPair A p q

/-- `t` ordinary lines force an all-ordinary `r`-subset in every `n`-point set with no `k`
collinear points. -/
def Forces (r k n t : ℕ) : Prop :=
  ∀ A : Finset Point, A.card = n → NoKCollinear A k → t ≤ ordCount A → HasOrdinaryClique A r

/-- The threshold `f_{r,k}(n)`: the least number of ordinary lines that forces an all-ordinary
`r`-subset (the set of forcing values is nonempty since `t = n² + 1` exceeds every `ordCount`). -/
noncomputable def f (r k n : ℕ) : ℕ := sInf {t : ℕ | Forces r k n t}

end Erdos960
