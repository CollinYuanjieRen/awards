import Mathlib

/-!
# Erdős Problem 1183 — definitions

Let `f(n)` be maximal such that in any `2`-colouring of the subsets of `{1, …, n}` there is
always a monochromatic family of at least `f(n)` sets which is closed under taking unions and
intersections (Erdős–Ulam, [Er78, p. 39]; erdosproblems.com/1183).

We model `{1, …, n}` by `Fin n`, a colouring by `c : Finset (Fin n) → Bool`, and a family by a
`Finset (Finset (Fin n))`.  `Closed F` says `F` is closed under binary unions and intersections,
`Mono c F` says `F` is monochromatic under `c`, and `Good n m` says every colouring admits a
nonempty monochromatic closed family with at least `m` members.  `f n` is the largest such `m`.
-/

namespace Erdos1183

/-- `F` is closed under (binary) unions and intersections. -/
def Closed {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F ∧ A ∩ B ∈ F

/-- `F` is monochromatic under the colouring `c`. -/
def Mono {n : ℕ} (c : Finset (Fin n) → Bool) (F : Finset (Finset (Fin n))) : Prop :=
  ∃ b : Bool, ∀ A ∈ F, c A = b

/-- Every `2`-colouring of the subsets of `Fin n` has a nonempty monochromatic family, closed
under unions and intersections, with at least `m` members. -/
def Good (n m : ℕ) : Prop :=
  ∀ c : Finset (Fin n) → Bool,
    ∃ F : Finset (Finset (Fin n)), F.Nonempty ∧ Closed F ∧ Mono c F ∧ m ≤ F.card

/-- `f n`: the largest `m` such that `Good n m` (the page's `f(n)`). -/
noncomputable def f (n : ℕ) : ℕ := sSup {m : ℕ | Good n m}

end Erdos1183
