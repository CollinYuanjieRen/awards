import Proof.Shift

/-!
# Erdős Problem 627: the lower bound for the shift graph

The shift graph on `2 ^ k` points needs at least `k` colours.  Given a proper colouring `C` with
`m` colours, attach to every point `i < 2 ^ k` the *palette*

`palette C i = {C (i, j) | i < j}`,

the set of colours used on the vertices whose first coordinate is `i`.  If `i < j` then the colour
`C (i, j)` lies in `palette C i` but not in `palette C j`: every vertex with first coordinate `j`
is adjacent to `(i, j)`, so it gets a different colour.  Hence `palette C` is injective, giving
`2 ^ k ≤ 2 ^ m` and therefore `k ≤ m`.
-/

namespace Erdos627

/-- The shift-graph vertex determined by a pair `i < j`. -/
def vert {N : ℕ} {i j : Fin N} (h : i < j) : ShiftVertex N := ⟨(i, j), h⟩

/-- The first coordinate of `vert h` is `i`. -/
theorem vert_fst {N : ℕ} {i j : Fin N} (h : i < j) : (vert h).1.1 = i := rfl

/-- The second coordinate of `vert h` is `j`. -/
theorem vert_snd {N : ℕ} {i j : Fin N} (h : i < j) : (vert h).1.2 = j := rfl

/-- The palette of a point `i` under a colouring `C` of the shift graph on `2 ^ k` points: the set
of colours taken by the vertices whose first coordinate is `i`. -/
def palette {k m : ℕ} (C : (shiftGraph (2 ^ k)).Coloring (Fin m)) (i : Fin (2 ^ k)) :
    Finset (Fin m) :=
  (Finset.univ.filter (fun p : ShiftVertex (2 ^ k) => p.1.1 = i)).image (fun p => C p)

/-- Membership in a palette. -/
theorem mem_palette {k m : ℕ} {C : (shiftGraph (2 ^ k)).Coloring (Fin m)} {i : Fin (2 ^ k)}
    {c : Fin m} : c ∈ palette C i ↔ ∃ p : ShiftVertex (2 ^ k), p.1.1 = i ∧ C p = c := by
  simp only [palette, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

/-- If `i < j` then `palette C i ≠ palette C j`: the colour of `(i, j)` belongs to the first but
not to the second, since every vertex starting at `j` is adjacent to `(i, j)`. -/
theorem palette_ne {k m : ℕ} (C : (shiftGraph (2 ^ k)).Coloring (Fin m)) {i j : Fin (2 ^ k)}
    (hlt : i < j) : palette C i ≠ palette C j := by
  intro heq
  have hmem : C (vert hlt) ∈ palette C i := mem_palette.mpr ⟨vert hlt, vert_fst hlt, rfl⟩
  rw [heq] at hmem
  obtain ⟨p, hp, hc⟩ := mem_palette.mp hmem
  have hne : vert hlt ≠ p := by
    intro hvp
    rw [← hvp, vert_fst hlt] at hp
    exact absurd hp (Fin.ne_of_lt hlt)
  have hadj : (shiftGraph (2 ^ k)).Adj (vert hlt) p :=
    shiftGraph_adj.mpr ⟨hne, Or.inl (by rw [vert_snd hlt, hp])⟩
  exact C.valid hadj hc.symm

/-- **Lower bound**: any proper colouring of the shift graph on `2 ^ k` points uses at least `k`
colours. -/
theorem le_of_colorable (k m : ℕ) (h : (shiftGraph (2 ^ k)).Colorable m) : k ≤ m := by
  obtain ⟨C⟩ := h
  have hinj : Function.Injective (palette C) := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact absurd hij (palette_ne C hlt)
    · exact heq
    · exact absurd hij.symm (palette_ne C hgt)
  have hcard := Fintype.card_le_of_injective (palette C) hinj
  rw [Fintype.card_fin, Fintype.card_finset, Fintype.card_fin] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega)).mp hcard

end Erdos627
