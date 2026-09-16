import Mathlib

/-!
# Erdős Problem 1084 (contact numbers): the one-dimensional case

For a finite set `A ⊆ ℝ`, `unitPairs A` counts the pairs `{x, y} ⊆ A` at distance exactly `1`
(as ordered pairs `(x, x + 1)`, so each unordered pair is counted once).  `A` is *separated* when
all pairwise distances are at least `1`.  The contact number `f₁ n` is the largest number of unit
pairs among separated `n`-point sets of reals.  Every finite set of reals has at most `|A| - 1` unit
pairs (the map `(x, x + 1) ↦ x` is injective and misses the maximum), so separation is not even
needed for the upper bound, and `{0, 1, …, n - 1}` attains `n - 1`.
-/

open Finset

namespace Erdos1084

/-- All pairwise distances are at least `1`. -/
def IsSeparated (A : Finset ℝ) : Prop := ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ |x - y|

/-- The number of pairs of points of `A` at distance exactly `1`, counted as ordered pairs
`(x, x + 1)`. -/
noncomputable def unitPairs (A : Finset ℝ) : ℕ := ((A ×ˢ A).filter fun p => p.2 - p.1 = 1).card

/-- The one-dimensional contact number `f₁ n`: the largest number of unit pairs among separated
`n`-point sets of reals. -/
noncomputable def contactOne (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℝ, A.card = n ∧ IsSeparated A ∧ unitPairs A = m}

/-- Every finite set of reals has at most `|A| - 1` pairs at distance `1`. -/
theorem unitPairs_le (A : Finset ℝ) : unitPairs A ≤ A.card - 1 := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp [unitPairs]
  · have hmax : A.max' hne ∈ A := A.max'_mem hne
    have hcard : (A.erase (A.max' hne)).card = A.card - 1 := Finset.card_erase_of_mem hmax
    refine le_trans ?_ hcard.le
    refine Finset.card_le_card_of_injOn (fun p : ℝ × ℝ => p.1) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
      have hlt : p.1 + 1 ≤ A.max' hne := by
        have : p.2 ≤ A.max' hne := Finset.le_max' A p.2 hp2
        linarith
      refine Finset.mem_coe.2 (Finset.mem_erase.2 ⟨?_, hp1⟩)
      intro h
      have h' : p.1 = A.max' hne := h
      rw [h'] at hlt
      linarith
    · intro p hp q hq hpq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hq
      have hpq' : p.1 = q.1 := hpq
      refine Prod.ext hpq' ?_
      have h1 : p.2 = p.1 + 1 := by linarith [hp.2]
      have h2 : q.2 = q.1 + 1 := by linarith [hq.2]
      rw [h1, h2, hpq']

/-- The set `{0, 1, …, n - 1}` of reals. -/
noncomputable def segment (n : ℕ) : Finset ℝ := (range n).image (fun i : ℕ => (i : ℝ))

/-- The segment `{0, 1, …, n - 1}` has exactly `n` points. -/
theorem card_segment (n : ℕ) : (segment n).card = n := by
  rw [segment, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]

/-- The segment `{0, 1, …, n - 1}` is separated. -/
theorem isSeparated_segment (n : ℕ) : IsSeparated (segment n) := by
  intro x hx y hy hxy
  simp only [segment, Finset.mem_image, Finset.mem_range] at hx hy
  obtain ⟨i, -, rfl⟩ := hx
  obtain ⟨j, -, rfl⟩ := hy
  have hij : i ≠ j := fun h => hxy (by rw [h])
  rcases hij.lt_or_gt with h | h
  · have hle : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have hle : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- The segment `{0, 1, …, n - 1}` attains `n - 1` pairs at distance `1`. -/
theorem unitPairs_segment (n : ℕ) : unitPairs (segment n) = n - 1 := by
  have hinj : Function.Injective (fun i : ℕ => ((i : ℝ), (i : ℝ) + 1)) := by
    intro a b hab
    have : (a : ℝ) = (b : ℝ) := congrArg Prod.fst hab
    exact_mod_cast this
  have hset : ((segment n ×ˢ segment n).filter fun p => p.2 - p.1 = 1)
      = (range (n - 1)).image (fun i : ℕ => ((i : ℝ), (i : ℝ) + 1)) := by
    ext p
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_filter, Finset.mem_product, segment, Finset.mem_image,
      Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩, hd⟩
      have hji : (j : ℝ) = (i : ℝ) + 1 := by linarith
      have hji' : j = i + 1 := by exact_mod_cast hji
      exact ⟨i, by omega, rfl, hji.symm⟩
    · rintro ⟨i, hi, rfl, rfl⟩
      refine ⟨⟨⟨i, by omega, rfl⟩, ⟨i + 1, by omega, by push_cast; ring⟩⟩, by ring⟩
  rw [unitPairs, hset, Finset.card_image_of_injective _ hinj, Finset.card_range]

end Erdos1084
