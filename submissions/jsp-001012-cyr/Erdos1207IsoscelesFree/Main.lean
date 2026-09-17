import Mathlib

/-!
# Erdős Problem #1207: `P_d(n) ≥ f_d(n)` (distinct-distance subsets are isosceles-free)

Let `P_d(n)` be such that any set of `n` points in `ℝ^d` contains at least `P_d(n)` points with
no isosceles triangle.  Erdős (after Riddell) asked to estimate `P_d(n)`, in particular whether
`P_2(n) < n^{1 − c}` (OPEN; not addressed here, nor the lower bounds `n^{1/(3d−3) − o(1)}`,
`n^{0.432}` or the upper bound `n^{1/2}` quoted on the page).  The problem page records: "Indeed,
one can take any subset of points with all distinct distances, whence `P_d(n) ≥ f_d(n)`", where
`f_d(n)` is the largest number such that any `n` points in `ℝ^d` contain `f_d(n)` points with all
pairwise distances distinct.  This file proves that inequality.

The definitions `Set.Triplewise`, `IsIsosceles`, `Set.IsIsoscelesFree`, the notation `ℝ^d` and
`Erdos1207.P` are copied verbatim from formal-conjectures; there is no formal-conjectures
statement for `f_d(n)`, so `IsDistinctDistances` and `f` are ours, mirroring `P` with
"isosceles-free" replaced by "all pairwise distances of distinct pairs are distinct".
-/

open scoped EuclideanGeometry

scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

namespace Set

variable {α : Type*} {r : α → α → α → Prop} {s t : Set α} {x y z : α}

/--
The ternary relation `r` holds triplewise on the set `s`
if `r x y z` for all *distinct* `x y z ∈ s`.
-/
protected def Triplewise (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

end Set

def IsIsosceles {α : Type*} [Dist α] (p q r : α) : Prop :=
  dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q

/-- A set is isosceles-free if no three distinct points in it form an isosceles triangle. -/
def Set.IsIsoscelesFree {α : Type*} [Dist α] (A : Set α) : Prop :=
  A.Triplewise fun x y z ↦ ¬ _root_.IsIsosceles x y z

namespace Erdos1207

/--
`P d n` is the largest number $m$ such that every set of $n$ points in $\mathbb{R}^d$ has an
isosceles-free subset of size at least $m$.
-/
noncomputable def P (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset (ℝ^d), S.card = n ∧
    m = sSup {k : ℕ | ∃ A ⊆ S, (A : Set (ℝ^d)).IsIsoscelesFree ∧ A.card = k}}

end Erdos1207

open Erdos1207

/-- A set has all distinct distances if distinct pairs of distinct points have distinct
distances. -/
def IsDistinctDistances {α : Type*} [Dist α] (A : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → ∀ ⦃c⦄, c ∈ A → ∀ ⦃e⦄, e ∈ A →
    a ≠ b → c ≠ e → dist a b = dist c e → (a = c ∧ b = e) ∨ (a = e ∧ b = c)

/-- `f d n` is the largest number `m` such that every set of `n` points in `ℝ^d` has a subset of
size at least `m` with all distinct distances (the `f_d(n)` of Erdős #1208, defined here as
`P` with "isosceles-free" replaced by "all distinct distances"). -/
noncomputable def f (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset (ℝ^d), S.card = n ∧
    m = sSup {k : ℕ | ∃ A ⊆ S, IsDistinctDistances (A : Set (ℝ^d)) ∧ A.card = k}}

/-- A set with all distinct distances is isosceles-free. -/
theorem isIsoscelesFree_of_isDistinctDistances {α : Type*} [Dist α] (A : Set α)
    (h : IsDistinctDistances A) : A.IsIsoscelesFree := by
  intro x hx y hy z hz hxy hyz hxz hiso
  rcases hiso with h1 | h2 | h3
  · rcases h hx hy hy hz hxy hyz h1 with ⟨hxy', -⟩ | ⟨hxz', -⟩
    · exact hxy hxy'
    · exact hxz hxz'
  · rcases h hy hz hz hx hyz (Ne.symm hxz) h2 with ⟨hyz', -⟩ | ⟨hyx', -⟩
    · exact hyz hyz'
    · exact hxy hyx'.symm
  · rcases h hz hx hx hy (Ne.symm hxz) hxy h3 with ⟨hzx', -⟩ | ⟨hzy', -⟩
    · exact hxz hzx'.symm
    · exact hyz hzy'.symm

/-- For every point set `S`, the largest distinct-distance subset is at most the largest
isosceles-free subset. -/
theorem sSup_distinct_le_sSup_isoscelesFree (d : ℕ) (S : Finset (ℝ^d)) :
    sSup {k : ℕ | ∃ A ⊆ S, IsDistinctDistances (A : Set (ℝ^d)) ∧ A.card = k} ≤
      sSup {k : ℕ | ∃ A ⊆ S, (A : Set (ℝ^d)).IsIsoscelesFree ∧ A.card = k} := by
  refine csSup_le_csSup ?_ ?_ ?_
  · refine ⟨S.card, ?_⟩
    rintro k ⟨A, hA, -, rfl⟩
    exact Finset.card_le_card hA
  · refine ⟨0, ∅, Finset.empty_subset _, ?_, Finset.card_empty⟩
    intro a ha
    simp at ha
  · rintro k ⟨A, hA, hd, hk⟩
    exact ⟨A, hA, isIsoscelesFree_of_isDistinctDistances _ hd, hk⟩

/-- **Erdős #1207, the page's remark**: `f_d(n) ≤ P_d(n)` for all `d`, `n`. -/
theorem erdos_1207_f_le_P (d n : ℕ) : f d n ≤ P d n := by
  show f d n ≤ sInf {m : ℕ | ∃ S : Finset (ℝ^d), S.card = n ∧
    m = sSup {k : ℕ | ∃ A ⊆ S, (A : Set (ℝ^d)).IsIsoscelesFree ∧ A.card = k}}
  by_cases hT : ∃ S : Finset (ℝ^d), S.card = n
  · obtain ⟨S₀, hS₀⟩ := hT
    refine le_csInf ?hne ?hle
    · exact ⟨_, S₀, hS₀, rfl⟩
    rintro m ⟨S, hS, rfl⟩
    refine le_trans ?_ (sSup_distinct_le_sSup_isoscelesFree d S)
    exact Nat.sInf_le ⟨S, hS, rfl⟩
  · have h1 : {m : ℕ | ∃ S : Finset (ℝ^d), S.card = n ∧
        m = sSup {k : ℕ | ∃ A ⊆ S, IsDistinctDistances (A : Set (ℝ^d)) ∧ A.card = k}} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun m hm => hT ⟨hm.choose, hm.choose_spec.1⟩
    have h2 : f d n = 0 := by
      show sInf {m : ℕ | ∃ S : Finset (ℝ^d), S.card = n ∧
        m = sSup {k : ℕ | ∃ A ⊆ S, IsDistinctDistances (A : Set (ℝ^d)) ∧ A.card = k}} = 0
      rw [h1, Nat.sInf_empty]
    exact h2 ▸ Nat.zero_le _

/-- Closed form of `erdos_1207_f_le_P`. -/
theorem erdos_1207_f_le_P_closed : ¬ ∃ d n : ℕ, P d n < f d n := by
  rintro ⟨d, n, h⟩
  exact absurd (erdos_1207_f_le_P d n) (not_le.mpr h)
