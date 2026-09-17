import Mathlib

/-!
# JSP-000490 / Erdős #603 — definitions

Komjáth's question (Erdős 1987): let `(A_i)` be a family of countably infinite sets with
`|A_i ∩ A_j| ≠ 2` for all `i ≠ j`.  Find the smallest cardinal `C` such that `⋃ A_i` can always
be coloured with at most `C` colours so that no `A_i` is monochromatic.

This file only fixes the notion "`C` colours always suffice"; the theorem (`Main.lean`) is that
it fails for every cardinal `C`, so no smallest such cardinal exists.
-/

universe u

open Cardinal

namespace Erdos603

/-- "`C` colours always suffice": every family `𝒜` of countably infinite sets whose distinct
members never intersect in exactly two elements admits a colouring of its union with at most
`C` colours in which no member of `𝒜` is monochromatic. -/
def AlwaysColourable (C : Cardinal.{u}) : Prop :=
  ∀ (X : Type u) (𝒜 : Set (Set X)), (∀ A ∈ 𝒜, A.Countable ∧ A.Infinite) →
    (∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → (A ∩ B).encard ≠ 2) →
    ∃ (Y : Type u) (col : ⋃₀ 𝒜 → Y), #Y ≤ C ∧
      ∀ A ∈ 𝒜, ∃ x y : ⋃₀ 𝒜, (x : X) ∈ A ∧ (y : X) ∈ A ∧ col x ≠ col y

end Erdos603
