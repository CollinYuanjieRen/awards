import Mathlib

/-!
# Erdős problem #311: definitions for the minimal non-zero unit-fraction deviation

This module fixes the objects used by the scoped component of Erdős problem #311.
For a finite set `A` of positive integers, `unitSum A` is `∑_{n ∈ A} 1/n`, computed in `ℚ`;
`lcmUpTo N` is the least common multiple `[1, …, N]` of `{1, …, N}`; `deviations N` is the
finite set of non-zero values `|1 - ∑_{n ∈ A} 1/n|` as `A` ranges over the subsets of
`{1, …, N}`; and `delta N` is the minimum of that finite set, which is the problem page's
`δ(N)`. The set is non-empty because `A = ∅` contributes the value `1`.

Also proved here are the two elementary facts about `lcmUpTo` that the main argument needs
(it is positive, and every element of `{1, …, N}` divides it) and a membership
characterisation of `deviations`.
-/

namespace Erdos311

/-- `unitSum A = ∑_{n ∈ A} 1/n`, computed in `ℚ`. -/
def unitSum (A : Finset ℕ) : ℚ := ∑ n ∈ A, (n : ℚ)⁻¹

/-- `lcmUpTo N = [1, …, N]`, the least common multiple of `{1, …, N}`. -/
def lcmUpTo (N : ℕ) : ℕ := (Finset.Icc 1 N).lcm id

/-- `deviations N` is the finite set of non-zero values `|1 - ∑_{n ∈ A} 1/n|` obtained from
subsets `A ⊆ {1, …, N}`. -/
def deviations (N : ℕ) : Finset ℚ := ((Finset.Icc 1 N).powerset.image (fun A => |1 - unitSum A|)).filter (fun d => d ≠ 0)

/-- `deviations N` is non-empty: the subset `A = ∅` has `unitSum ∅ = 0`, hence contributes
the value `|1 - 0| = 1 ≠ 0`. -/
theorem deviations_nonempty (N : ℕ) : (deviations N).Nonempty := by
  refine ⟨1, ?_⟩
  simp only [deviations, Finset.mem_filter, Finset.mem_image, Finset.mem_powerset]
  refine ⟨⟨∅, Finset.empty_subset _, ?_⟩, one_ne_zero⟩
  simp [unitSum]

/-- `delta N` is the problem page's `δ(N)`: the minimum of the finite non-empty set
`deviations N` of non-zero deviations. -/
noncomputable def delta (N : ℕ) : ℚ := (deviations N).min' (deviations_nonempty N)

/-- (T6) The least common multiple `[1, …, N]` is positive: no element of `{1, …, N}` is `0`. -/
theorem lcmUpTo_pos (N : ℕ) : 0 < lcmUpTo N := by
  refine Nat.pos_of_ne_zero ?_
  show (Finset.Icc 1 N).lcm id ≠ 0
  refine Finset.lcm_ne_zero_iff.2 ?_
  intro x hx
  have h1 : 1 ≤ x := (Finset.mem_Icc.1 hx).1
  simp only [id_eq]
  omega

/-- Every element of `{1, …, N}` divides `lcmUpTo N`. -/
theorem dvd_lcmUpTo {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) : n ∣ lcmUpTo N :=
  Finset.dvd_lcm hn

/-- Membership in `deviations N`: the elements are exactly the non-zero deviations
`|1 - unitSum A|` coming from subsets `A ⊆ {1, …, N}`. -/
theorem mem_deviations (N : ℕ) (d : ℚ) :
    d ∈ deviations N ↔ ∃ A ⊆ Finset.Icc 1 N, 1 - unitSum A ≠ 0 ∧ d = |1 - unitSum A| := by
  simp only [deviations, Finset.mem_filter, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨A, hA, rfl⟩, hd⟩
    exact ⟨A, hA, abs_ne_zero.1 hd, rfl⟩
  · rintro ⟨A, hA, h, rfl⟩
    exact ⟨⟨A, hA, rfl⟩, abs_ne_zero.2 h⟩

end Erdos311
