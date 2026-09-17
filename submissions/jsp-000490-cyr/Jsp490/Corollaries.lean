import Jsp490.Main

/-!
# JSP-000490 / Erdős #603 — corollaries closing possible reading gaps

* `erdos_603_anyUniverse`: colourings whose colour type lives in an arbitrary universe still
  produce a monochromatic member (no universe loophole in "at most `C` colours").
* `erdos_603_indexed`: the literal indexed-family reading `(A_i)`, `i ≠ j`, with `⋃ A_i = X`.
* `witness_nontrivial`: the statement of `erdos_603` itself forces the family to be nonempty
  and the ground set infinite, for every `C` including `C = 0` (anti-vacuity certificate).
-/

universe u v

open Cardinal

namespace Erdos603

theorem erdos_603_anyUniverse (C : Cardinal.{u}) : ∃ (X : Type u) (𝒜 : Set (Set X)),
    (∀ A ∈ 𝒜, A.Countable ∧ A.Infinite) ∧
    (∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → (A ∩ B).encard ≠ 2) ∧
    (∀ x : X, ∃ A ∈ 𝒜, x ∈ A) ∧
    ∀ (Y : Type v) (col : X → Y), lift.{u} #Y ≤ lift.{v} C →
      ∃ A ∈ 𝒜, ∀ x ∈ A, ∀ y ∈ A, col x = col y := by
  obtain ⟨X, 𝒜, h1, h2, h3, h4⟩ := erdos_603 C
  refine ⟨X, 𝒜, h1, h2, h3, ?_⟩
  intro Y col hY
  -- replace `Y` by the quotient of `X` by the colour classes, which lives in `Type u`
  have hquot : lift.{v} #(Quotient (Setoid.ker col)) = lift.{u} #(Set.range col) :=
    Cardinal.lift_mk_eq'.mpr ⟨Setoid.quotientKerEquivRange col⟩
  have hle : #(Quotient (Setoid.ker col)) ≤ C := by
    refine Cardinal.lift_le.{v}.mp ?_
    rw [hquot]
    exact (Cardinal.lift_le.mpr (Cardinal.mk_set_le _)).trans hY
  obtain ⟨A, hA, hmono⟩ := h4 (Quotient (Setoid.ker col)) (fun x => Quotient.mk _ x) hle
  exact ⟨A, hA, fun x hx y hy => Quotient.exact (hmono x hx y hy)⟩

/-- Helper: the ground set produced by `erdos_603` is nonempty (else colour it with no colours). -/
private theorem nonempty_of_root {C : Cardinal.{u}} {X : Type u} {𝒜 : Set (Set X)}
    (h1 : ∀ A ∈ 𝒜, A.Countable ∧ A.Infinite)
    (h4 : ∀ (Y : Type u) (col : X → Y), #Y ≤ C → ∃ A ∈ 𝒜, ∀ x ∈ A, ∀ y ∈ A, col x = col y) :
    Nonempty X := by
  rcases isEmpty_or_nonempty X with hX | hX
  · obtain ⟨A, hA, -⟩ := h4 PEmpty.{u+1} (fun x => (hX.false x).elim)
      (by simp [Cardinal.mk_eq_zero])
    exact absurd (h1 A hA).2 (by simp [Set.Finite.ofFinset (∅ : Finset X)])
  · exact hX

theorem erdos_603_indexed (C : Cardinal.{u}) :
    ∃ (X : Type u) (I : Type u) (A : I → Set X), Nonempty I ∧
      (∀ i, (A i).Countable ∧ (A i).Infinite) ∧
      (∀ i j, i ≠ j → (A i ∩ A j).encard ≠ 2) ∧
      (⋃ i, A i) = Set.univ ∧
      ∀ (Y : Type u) (col : X → Y), #Y ≤ C → ∃ i, ∀ x ∈ A i, ∀ y ∈ A i, col x = col y := by
  obtain ⟨X, 𝒜, h1, h2, h3, h4⟩ := erdos_603 C
  refine ⟨X, {A : Set X // A ∈ 𝒜}, fun i => (i : Set X), ?_, fun i => h1 i i.2,
    fun i j hij => h2 i i.2 j j.2 (fun h => hij (Subtype.ext h)), ?_, ?_⟩
  · obtain ⟨x⟩ := nonempty_of_root h1 h4
    obtain ⟨A, hA, -⟩ := h3 x
    exact ⟨⟨A, hA⟩⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨A, hA, hx⟩ := h3 x
    exact Set.mem_iUnion.mpr ⟨⟨A, hA⟩, hx⟩
  · intro Y col hY
    obtain ⟨A, hA, hmono⟩ := h4 Y col hY
    exact ⟨⟨A, hA⟩, hmono⟩

theorem witness_nontrivial (C : Cardinal.{u}) : ∃ (X : Type u) (𝒜 : Set (Set X)),
    ((∀ A ∈ 𝒜, A.Countable ∧ A.Infinite) ∧
     (∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → (A ∩ B).encard ≠ 2) ∧
     (∀ x : X, ∃ A ∈ 𝒜, x ∈ A) ∧
     ∀ (Y : Type u) (col : X → Y), #Y ≤ C → ∃ A ∈ 𝒜, ∀ x ∈ A, ∀ y ∈ A, col x = col y) ∧
    𝒜.Nonempty ∧ Infinite X := by
  obtain ⟨X, 𝒜, h1, h2, h3, h4⟩ := erdos_603 C
  obtain ⟨x⟩ := nonempty_of_root h1 h4
  obtain ⟨A, hA, hx⟩ := h3 x
  refine ⟨X, 𝒜, ⟨h1, h2, h3, h4⟩, ⟨A, hA⟩, ?_⟩
  exact Set.infinite_univ_iff.mp ((h1 A hA).2.mono (Set.subset_univ A))

end Erdos603
