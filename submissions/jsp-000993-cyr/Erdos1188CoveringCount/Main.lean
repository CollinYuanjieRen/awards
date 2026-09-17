import Mathlib

/-!
# Erdős Problem #1188: without minimality there are `≫ 2^x` distinct covering systems

A distinct covering system is a set of congruence classes `a_i (mod n_i)` with distinct moduli
`1 < n_1 < ⋯ < n_k` such that every integer satisfies at least one of them; it is minimal if no
proper subset covers.  Erdős asked to estimate `F(x)`, the number of minimal distinct covering
systems with all moduli in `[1, x]` (OPEN as posed on the page; the estimate
`log log F(x) / log x → 1` and the count of irreducible covering sets are not addressed).  The
problem page records that Erdős "asked this without the minimal assumption, but otherwise this
is trivial (since e.g. any system containing some fixed covering system would work, resulting in
`≫ 2^x` many such systems)".  This file proves that remark: the number of (not necessarily
minimal) distinct covering systems with moduli in `[1, x]` is at least `2^(x − 6)` for `x ≥ 12`,
because adding any set of further moduli (each with residue `0`) to the fixed covering system
`0 (mod 2), 0 (mod 3), 1 (mod 4), 1 (mod 6), 11 (mod 12)` gives a distinct covering system.

The definitions `CongruenceClass`, `ValidClass`, `Satisfies`, `Covers`, `HasDistinctModuli` and
`ClassesUpTo` are copied verbatim from the formal-conjectures rendering of #1188; the count of
all distinct covering systems (`distinctCoveringCount`, without minimality) is ours and mirrors
formal-conjectures' `coveringCount` with the minimality clause removed.
-/

namespace Erdos1188

/-- A congruence class `(n, a)` represents `a (mod n)`. -/
abbrev CongruenceClass := ℕ × ℕ

/-- The modulus is `> 1` and the residue is reduced. -/
def ValidClass (c : CongruenceClass) : Prop := 2 ≤ c.1 ∧ c.2 < c.1

/-- `z` lies in the class `(n, a)`. -/
def Satisfies (z : ℤ) (c : CongruenceClass) : Prop := z % (c.1 : ℤ) = (c.2 : ℤ)

/-- Every integer satisfies some congruence of `S`. -/
def Covers (S : Finset CongruenceClass) : Prop := ∀ z : ℤ, ∃ c ∈ S, Satisfies z c

/-- No two classes of `S` share a modulus. -/
def HasDistinctModuli (S : Finset CongruenceClass) : Prop :=
  ∀ ⦃c₁⦄, c₁ ∈ S → ∀ ⦃c₂⦄, c₂ ∈ S → c₁.1 = c₂.1 → c₁ = c₂

/-- All classes `(n, a)` with `2 ≤ n ≤ x` and `a < n`. -/
def ClassesUpTo (x : ℕ) : Finset CongruenceClass :=
  (Finset.Icc 2 x).biUnion fun n => (Finset.range n).image fun a => (n, a)

/-- A distinct covering system (not necessarily minimal): valid classes with distinct moduli
that cover `ℤ`. -/
def IsDistinctCoveringSystem (S : Finset CongruenceClass) : Prop :=
  (∀ c ∈ S, ValidClass c) ∧ HasDistinctModuli S ∧ Covers S

open scoped Classical in
/-- The distinct covering systems (not necessarily minimal) all of whose moduli lie in `[1, x]`. -/
noncomputable def coveringSystemsUpTo (x : ℕ) : Finset (Finset CongruenceClass) :=
  (ClassesUpTo x).powerset.filter IsDistinctCoveringSystem

/-- The number of distinct covering systems (not necessarily minimal) all of whose moduli lie in
`[1, x]`. -/
noncomputable def distinctCoveringCount (x : ℕ) : ℕ := (coveringSystemsUpTo x).card

/-- The fixed covering system `0 (mod 2), 0 (mod 3), 1 (mod 4), 1 (mod 6), 11 (mod 12)`. -/
def baseSystem : Finset CongruenceClass := {(2, 0), (3, 0), (4, 1), (6, 1), (12, 11)}

/-- Membership criterion for `ClassesUpTo`. -/
theorem mem_ClassesUpTo {x n a : ℕ} (h2 : 2 ≤ n) (hnx : n ≤ x) (ha : a < n) :
    ((n, a) : CongruenceClass) ∈ ClassesUpTo x := by
  rw [ClassesUpTo, Finset.mem_biUnion]
  exact ⟨n, Finset.mem_Icc.mpr ⟨h2, hnx⟩,
    Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr ha, rfl⟩⟩

/-- The moduli occurring in `baseSystem`. -/
theorem modulus_of_mem_baseSystem {c : CongruenceClass} (hc : c ∈ baseSystem) :
    c.1 = 2 ∨ c.1 = 3 ∨ c.1 = 4 ∨ c.1 = 6 ∨ c.1 = 12 := by
  simp only [baseSystem, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Membership of a residue-`0` class in an extension of the base system. -/
theorem mem_baseSystem_union_image {T : Finset ℕ} {n : ℕ} (h2 : n ≠ 2) (h3 : n ≠ 3) :
    ((n, 0) : CongruenceClass) ∈ baseSystem ∪ T.image (fun m => (m, 0)) ↔ n ∈ T := by
  simp [baseSystem, h2, h3]

/-- The base system covers `ℤ`. -/
theorem baseSystem_covers : Covers baseSystem := by
  intro z
  have e2 : z % 12 % 2 = z % 2 := Int.emod_emod_of_dvd z (by norm_num)
  have e3 : z % 12 % 3 = z % 3 := Int.emod_emod_of_dvd z (by norm_num)
  have e4 : z % 12 % 4 = z % 4 := Int.emod_emod_of_dvd z (by norm_num)
  have e6 : z % 12 % 6 = z % 6 := Int.emod_emod_of_dvd z (by norm_num)
  have h : z % 2 = 0 ∨ z % 3 = 0 ∨ z % 4 = 1 ∨ z % 6 = 1 ∨ z % 12 = 11 := by
    have key : z % 12 = 0 ∨ z % 12 = 1 ∨ z % 12 = 2 ∨ z % 12 = 3 ∨ z % 12 = 4 ∨ z % 12 = 5 ∨
        z % 12 = 6 ∨ z % 12 = 7 ∨ z % 12 = 8 ∨ z % 12 = 9 ∨ z % 12 = 10 ∨ z % 12 = 11 := by omega
    rcases key with h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  rcases h with h | h | h | h | h
  · exact ⟨(2, 0), by simp [baseSystem], by simpa [Satisfies] using h⟩
  · exact ⟨(3, 0), by simp [baseSystem], by simpa [Satisfies] using h⟩
  · exact ⟨(4, 1), by simp [baseSystem], by simpa [Satisfies] using h⟩
  · exact ⟨(6, 1), by simp [baseSystem], by simpa [Satisfies] using h⟩
  · exact ⟨(12, 11), by simp [baseSystem], by simpa [Satisfies] using h⟩

/-- Extending the base system by the classes `0 (mod n)`, `n ∈ T`, for any set `T` of moduli in
`[2, x]` avoiding `{2, 3, 4, 6, 12}`, gives a distinct covering system with moduli in `[1, x]`. -/
theorem extended_mem (x : ℕ) (hx : 12 ≤ x) (T : Finset ℕ)
    (hT : T ⊆ (Finset.Icc 2 x) \ {2, 3, 4, 6, 12}) :
    baseSystem ∪ T.image (fun n => (n, 0)) ∈ coveringSystemsUpTo x := by
  classical
  have hTmem : ∀ n ∈ T, 2 ≤ n ∧ n ≤ x ∧ n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 6 ∧ n ≠ 12 := by
    intro n hn
    have h := hT hn
    rw [Finset.mem_sdiff, Finset.mem_Icc] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    refine ⟨h.1.1, h.1.2, ?_, ?_, ?_, ?_, ?_⟩ <;> (rintro rfl; exact h.2 (by norm_num))
  rw [coveringSystemsUpTo, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · simp only [baseSystem, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;>
        exact mem_ClassesUpTo (by norm_num) (by omega) (by norm_num)
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨h2, hnx, -⟩ := hTmem n hn
      exact mem_ClassesUpTo h2 hnx (by omega)
  · intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · simp only [baseSystem, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨h2, -, -⟩ := hTmem n hn
      exact ⟨h2, by omega⟩
  · intro c₁ h₁ c₂ h₂ hmod
    rcases Finset.mem_union.mp h₁ with hb₁ | hi₁ <;> rcases Finset.mem_union.mp h₂ with hb₂ | hi₂
    · simp only [baseSystem, Finset.mem_insert, Finset.mem_singleton] at hb₁ hb₂
      rcases hb₁ with rfl | rfl | rfl | rfl | rfl <;> rcases hb₂ with rfl | rfl | rfl | rfl | rfl <;>
        simp_all
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hi₂
      obtain ⟨-, -, hn2, hn3, hn4, hn6, hn12⟩ := hTmem n hn
      have hmod' : c₁.1 = n := hmod
      rcases modulus_of_mem_baseSystem hb₁ with h | h | h | h | h <;> omega
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hi₁
      obtain ⟨-, -, hn2, hn3, hn4, hn6, hn12⟩ := hTmem n hn
      have hmod' : n = c₂.1 := hmod
      rcases modulus_of_mem_baseSystem hb₂ with h | h | h | h | h <;> omega
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hi₁
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hi₂
      have hmod' : n = m := hmod
      rw [hmod']
  · intro z
    obtain ⟨c, hc, hz⟩ := baseSystem_covers z
    exact ⟨c, Finset.mem_union_left _ hc, hz⟩

/-- Different sets of extra moduli give different systems. -/
theorem extended_injective (x : ℕ) :
    Set.InjOn (fun T : Finset ℕ => baseSystem ∪ T.image (fun n => (n, 0)))
      ((Finset.Icc 2 x \ {2, 3, 4, 6, 12}).powerset : Set (Finset ℕ)) := by
  intro T₁ hT₁ T₂ hT₂ heq
  rw [Finset.mem_coe, Finset.mem_powerset] at hT₁ hT₂
  have heq' : baseSystem ∪ T₁.image (fun n => (n, 0))
      = baseSystem ∪ T₂.image (fun n => (n, 0)) := heq
  have key : ∀ {S₁ S₂ : Finset ℕ}, S₁ ⊆ Finset.Icc 2 x \ {2, 3, 4, 6, 12} →
      baseSystem ∪ S₁.image (fun n => (n, 0)) = baseSystem ∪ S₂.image (fun n => (n, 0)) →
      ∀ n ∈ S₁, n ∈ S₂ := by
    intro S₁ S₂ hS₁ hS hn hnS₁
    have h := hS₁ hnS₁
    rw [Finset.mem_sdiff] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    have h2 : hn ≠ 2 := by rintro rfl; exact h.2 (by norm_num)
    have h3 : hn ≠ 3 := by rintro rfl; exact h.2 (by norm_num)
    refine (mem_baseSystem_union_image h2 h3).mp ?_
    rw [← hS]
    exact (mem_baseSystem_union_image h2 h3).mpr hnS₁
  exact Finset.ext fun n => ⟨fun hn => key hT₁ heq' n hn, fun hn => key hT₂ heq'.symm n hn⟩

end Erdos1188

open Erdos1188

/-- **Erdős #1188, the page's remark**: without minimality there are at least `2^(x − 6)` distinct
covering systems with moduli in `[1, x]` (for `x ≥ 12`). -/
theorem erdos_1188_trivial_count (x : ℕ) (hx : 12 ≤ x) : 2 ^ (x - 6) ≤ distinctCoveringCount x := by
  have hsub : ({2, 3, 4, 6, 12} : Finset ℕ) ⊆ Finset.Icc 2 x := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rw [Finset.mem_Icc]
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hcard : (Finset.Icc 2 x \ {2, 3, 4, 6, 12} : Finset ℕ).card = x - 6 := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.card_Icc]
    have : ({2, 3, 4, 6, 12} : Finset ℕ).card = 5 := by decide
    rw [this]
    omega
  have hle := Finset.card_le_card_of_injOn
    (fun T : Finset ℕ => baseSystem ∪ T.image (fun n => (n, 0)))
    (fun T hT => extended_mem x hx T (Finset.mem_powerset.mp hT)) (extended_injective x)
  rw [Finset.card_powerset, hcard] at hle
  exact hle

/-- Closed form of `erdos_1188_trivial_count`. -/
theorem erdos_1188_trivial_count_closed :
    ¬ ∃ x : ℕ, 12 ≤ x ∧ distinctCoveringCount x < 2 ^ (x - 6) := by
  rintro ⟨x, hx, h⟩
  exact absurd (erdos_1188_trivial_count x hx) (not_le.mpr h)
