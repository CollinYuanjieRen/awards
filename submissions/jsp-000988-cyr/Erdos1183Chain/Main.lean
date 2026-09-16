import Mathlib

/-!
# Erdős Problem #1183: the chain lower bound `f(n) ≥ (n + 1) / 2`

Erdős and Ulam asked for the order of magnitude of `f(n)`, the largest `f` such that every
`2`-colouring of the subsets of `{1, …, n}` contains a monochromatic family of at least `f` sets
closed under unions and intersections (and of the analogue `F(n)` for union-closed families).
The problem is OPEN.  The problem page records the only known lower bound: "It is trivial that
`f(n) ≥ (n+1)/2`, since there is a sequence of `n+1` many nested subsets."  This file proves
exactly that bound: the chain `∅ ⊂ {0} ⊂ {0, 1} ⊂ ⋯ ⊂ {0, …, n-1}` has `n + 1` members, so by
the pigeonhole principle some colour class contains at least `⌈(n+1)/2⌉` of them, and any
subfamily of a chain is closed under unions and intersections.

The asymptotic questions (the true order of `f(n)`, and the bounds `F(n) ≥ n^{ω(n)}`,
`F(n) < (1 + o(1))^n` for the union-closed variant) are not addressed here.
-/

open Finset

/-- A family of finite sets closed under pairwise unions and intersections. -/
def IsUnionInterClosed {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F ∧ A ∩ B ∈ F

/-- A family on which a `2`-colouring `c` is constant. -/
def IsMonochromatic {α : Type*} (c : Finset α → Fin 2) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, c A = c B

/-- `f n` is the largest `k` such that every `2`-colouring of the subsets of `Fin n` admits a
monochromatic family of at least `k` sets closed under unions and intersections (the function
`f(n)` of Erdős #1183; the set of such `k` is bounded by `2 ^ n`, so `sSup` is its maximum). -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ c : Finset (Fin n) → Fin 2,
    ∃ F : Finset (Finset (Fin n)), IsMonochromatic c F ∧ IsUnionInterClosed F ∧ k ≤ F.card}

/-- The initial segment `{0, …, k - 1}` of `Fin n`. -/
def initialSegment (n : ℕ) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ (i : ℕ) < k

/-- Initial segments of `Fin n` increase with the cut-off. -/
private lemma initialSegment_mono (n : ℕ) {k k' : ℕ} (h : k ≤ k') :
    initialSegment n k ⊆ initialSegment n k' := by
  intro i hi
  simp only [initialSegment, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

/-- The cut-offs `0, …, n` give pairwise distinct initial segments of `Fin n`. -/
private lemma initialSegment_injOn (n : ℕ) :
    Set.InjOn (initialSegment n) (Finset.range (n + 1) : Finset ℕ) := by
  intro k hk k' hk' h
  simp only [Finset.coe_range, Set.mem_Iio, Nat.lt_succ_iff] at hk hk'
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · have hkn : k < n := lt_of_lt_of_le hlt hk'
    have hmem := Finset.ext_iff.mp h ⟨k, hkn⟩
    simp only [initialSegment, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    omega
  · exact heq
  · have hkn : k' < n := lt_of_lt_of_le hgt hk
    have hmem := Finset.ext_iff.mp h ⟨k', hkn⟩
    simp only [initialSegment, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    omega

/-- The chain bound in explicit form: every `2`-colouring of the subsets of `Fin n` has a
monochromatic union- and intersection-closed family of at least `⌈(n + 1) / 2⌉` sets. -/
theorem exists_monochromatic_closed_family (n : ℕ) (c : Finset (Fin n) → Fin 2) :
    ∃ F : Finset (Finset (Fin n)),
      IsMonochromatic c F ∧ IsUnionInterClosed F ∧ n + 1 ≤ 2 * F.card := by
  classical
  set C : Finset (Finset (Fin n)) := (Finset.range (n + 1)).image (initialSegment n) with hC
  have hCcard : C.card = n + 1 := by
    rw [hC, Finset.card_image_of_injOn (initialSegment_injOn n), Finset.card_range]
  have hmaps : ∀ A ∈ C, c A ∈ (Finset.univ : Finset (Fin 2)) := fun A _ ↦ Finset.mem_univ _
  have hlt : (Finset.univ : Finset (Fin 2)).card * (n / 2) < C.card := by
    rw [hCcard, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
  refine ⟨C.filter fun A ↦ c A = y, ?_, ?_, ?_⟩
  · intro A hA B hB
    rw [Finset.mem_filter] at hA hB
    rw [hA.2, hB.2]
  · intro A hA B hB
    obtain ⟨hA1, hA2⟩ := Finset.mem_filter.mp hA
    obtain ⟨hB1, hB2⟩ := Finset.mem_filter.mp hB
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hA1
    obtain ⟨k', -, rfl⟩ := Finset.mem_image.mp hB1
    rcases le_total k k' with hle | hle
    · have hsub := initialSegment_mono n hle
      rw [Finset.union_eq_right.mpr hsub, Finset.inter_eq_left.mpr hsub]
      exact ⟨Finset.mem_filter.mpr ⟨hB1, hB2⟩, Finset.mem_filter.mpr ⟨hA1, hA2⟩⟩
    · have hsub := initialSegment_mono n hle
      rw [Finset.union_eq_left.mpr hsub, Finset.inter_eq_right.mpr hsub]
      exact ⟨Finset.mem_filter.mpr ⟨hA1, hA2⟩, Finset.mem_filter.mpr ⟨hB1, hB2⟩⟩
  · omega

/-- **Erdős Problem #1183, the chain lower bound.**  `f(n) ≥ (n + 1) / 2`, i.e.
`n + 1 ≤ 2 f(n)`, for every `n`.  The true order of magnitude of `f(n)` is open and not claimed. -/
theorem erdos_1183_f_lower_bound (n : ℕ) : n + 1 ≤ 2 * f n := by
  classical
  set S : Set ℕ := {k : ℕ | ∀ c : Finset (Fin n) → Fin 2,
    ∃ F : Finset (Finset (Fin n)), IsMonochromatic c F ∧ IsUnionInterClosed F ∧ k ≤ F.card}
  have hbdd : BddAbove S := by
    refine ⟨2 ^ n, fun k hk ↦ ?_⟩
    obtain ⟨F, -, -, hF⟩ := hk (fun _ ↦ 0)
    have h1 : F.card ≤ Fintype.card (Finset (Fin n)) := Finset.card_le_univ F
    rw [Fintype.card_finset, Fintype.card_fin] at h1
    exact hF.trans h1
  have hmem : n / 2 + 1 ∈ S := by
    intro c
    obtain ⟨F, h1, h2, h3⟩ := exists_monochromatic_closed_family n c
    exact ⟨F, h1, h2, by omega⟩
  have hf : n / 2 + 1 ≤ f n := le_csSup hbdd hmem
  omega
