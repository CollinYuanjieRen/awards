import Mathlib

/-!
# Erdős Problem 210 — ordinary lines: definitions

Points live in `ℝ × ℝ`. `D a b c` is twice the signed area of the triangle `a b c`; the line
through `a ≠ b` is the zero set of `D a b ·`, and the strict sides of that line are the two strict
sign classes of `D a b ·`.

For a finite set `P` of points, an *ordinary line* is a line containing exactly two points of `P`.
Internally an ordinary line is represented by its two-element point set (`ordinaryPairs`); for the
audited statement the ordinary lines are the corresponding affine subspaces `line[ℝ, a, b]`
(`ordinaryLines`), and `f n` is the least number of ordinary lines determined by `n` points of the
plane that are not all on a line.
-/

namespace Erdos210

/-- Twice the signed area of the triangle `a b c`: `det (b - a, c - a)`. -/
def D (a b c : ℝ × ℝ) : ℝ := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- `z` lies on the line through `a` and `b` (meaningful for `a ≠ b`). -/
def OnLine (a b z : ℝ × ℝ) : Prop := D a b z = 0

/-- `z` and `w` lie strictly on the same side of the line `a b`. -/
def SameSide (a b z w : ℝ × ℝ) : Prop := 0 < D a b z * D a b w

/-- `z` and `w` lie strictly on opposite sides of the line `a b`. -/
def OppSide (a b z w : ℝ × ℝ) : Prop := D a b z * D a b w < 0

/-- `P` is not contained in a line: some three of its points are not collinear. -/
def NotCollinear (P : Finset (ℝ × ℝ)) : Prop := ∃ a ∈ P, ∃ b ∈ P, ∃ c ∈ P, ¬ OnLine a b c

open scoped Classical in
/-- The ordinary pairs of `P`: two-element subsets `{a, b}` of `P` such that every point of `P` on
the line `a b` is `a` or `b`. Each ordinary line of `P` corresponds to exactly one ordinary pair. -/
noncomputable def ordinaryPairs (P : Finset (ℝ × ℝ)) : Finset (Finset (ℝ × ℝ)) :=
  (P.powersetCard 2).filter fun e => ∀ a ∈ e, ∀ b ∈ e, a ≠ b → ∀ c ∈ P, OnLine a b c → c ∈ e

open scoped Classical in
/-- The ordinary lines of `P`: the lines `line[ℝ, a, b]` through two distinct points of `P` that
contain exactly two points of `P`. -/
noncomputable def ordinaryLines (P : Finset (ℝ × ℝ)) : Set (AffineSubspace ℝ (ℝ × ℝ)) :=
  {L | ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ L = line[ℝ, a, b] ∧ (P.filter (· ∈ L)).card = 2}

/-- `f n`: the least number of ordinary lines determined by `n` points of `ℝ²` not all on a line. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ ¬ Collinear ℝ (P : Set (ℝ × ℝ)) ∧
    (ordinaryLines P).ncard = m}

open scoped Classical in
/-- The points of `P` lying on no ordinary line (Kelly–Moser's points of order zero). -/
noncomputable def orderZero (P : Finset (ℝ × ℝ)) : Finset (ℝ × ℝ) :=
  P.filter fun p => ∀ e ∈ ordinaryPairs P, p ∉ e

/-- The open ordinary cell of `p`: the points strictly on the same side as `p` of every ordinary
line of `P`. -/
def W (P : Finset (ℝ × ℝ)) (p : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {z | ∀ e ∈ ordinaryPairs P, ∀ a ∈ e, ∀ b ∈ e, a ≠ b → SameSide a b p z}

end Erdos210
