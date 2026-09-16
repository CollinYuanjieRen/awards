import Erdos1019Planar.BipyramidLines

/-!
# Spokes of the bipyramid drawing

The spokes of `bipyramidGraph l` join an equatorial vertex `i` to an apex.  In the drawing of
`BipyramidLines` the inner spoke to `(i, i²)` lies in the closed region `tangentFun i ≥ 0`,
touching the tangent line only at `(i, i²)`, and on the line `innerSpokeFun i = 0`; the outer
spoke lies in `tangentFun i ≤ 0`, touching only at `(i, i²)`, and on `outerSpokeFun l i = 0`.
Chords lie on `chordFun`/`longFun` lines on which the apices have strict signs.  These signs
give every required non-crossing statement involving a spoke.
-/

open Set
open scoped SimpleGraph

namespace Bipyramid

/-! ### Sign-flipped separation lemmas -/

/-- Negating the coefficients negates the affine functional. -/
private theorem lineFun_neg (a b c : ℝ) (z : ℝ × ℝ) :
    lineFun (-a) (-b) (-c) z = -lineFun a b c z := by
  simp only [lineFun]
  ring

/-- Two segments are disjoint when a functional is negative on one and nonnegative on the
other. -/
private theorem segment_disjoint_of_neg_of_nonneg {a b c : ℝ} {p q r s : ℝ × ℝ}
    (hp : lineFun a b c p < 0) (hq : lineFun a b c q < 0) (hr : 0 ≤ lineFun a b c r)
    (hs : 0 ≤ lineFun a b c s) : Disjoint (segment ℝ p q) (segment ℝ r s) :=
  segment_disjoint_of_pos_of_nonpos (a := -a) (b := -b) (c := -c)
    (by rw [lineFun_neg]; linarith) (by rw [lineFun_neg]; linarith)
    (by rw [lineFun_neg]; linarith) (by rw [lineFun_neg]; linarith)

/-- If a functional vanishes at `p`, is negative at `q`, and is nonnegative on `[r, s]`, then
`[p, q]` meets `[r, s]` at most in `p`. -/
private theorem segment_inter_segment_subset_singleton_of_neg {a b c : ℝ} {p q r s : ℝ × ℝ}
    (hp : lineFun a b c p = 0) (hq : lineFun a b c q < 0) (hr : 0 ≤ lineFun a b c r)
    (hs : 0 ≤ lineFun a b c s) : segment ℝ p q ∩ segment ℝ r s ⊆ {p} :=
  segment_inter_segment_subset_singleton (a := -a) (b := -b) (c := -c)
    (by rw [lineFun_neg]; linarith) (by rw [lineFun_neg]; linarith)
    (by rw [lineFun_neg]; linarith) (by rw [lineFun_neg]; linarith)

/-! ### From separation statements to the image form -/

/-- Disjoint segments trivially meet inside any image. -/
private theorem subset_image_of_disjoint {l : ℕ} {S T : Set (ℝ × ℝ)} {P : Set (Fin l ⊕ Bool)}
    (h : Disjoint S T) : S ∩ T ⊆ pos l '' P := by
  rw [Set.disjoint_iff_inter_eq_empty.1 h]
  exact Set.empty_subset _

/-- An intersection contained in the position of a vertex of `P` lies in the image of `P`. -/
private theorem subset_image_of_subset_singleton {l : ℕ} {S T : Set (ℝ × ℝ)}
    {P : Set (Fin l ⊕ Bool)} {w : Fin l ⊕ Bool} (hw : w ∈ P) (h : S ∩ T ⊆ {pos l w}) :
    S ∩ T ⊆ pos l '' P :=
  h.trans (Set.singleton_subset_iff.2 ⟨w, hw, rfl⟩)

/-! ### Vertices on spokes -/

/-- A vertex on the segment of a spoke is one of its endpoints. -/
theorem vertex_mem_spoke (l : ℕ) (hl : 3 ≤ l) (i : Fin l) (b : Bool) (w : Fin l ⊕ Bool)
    (hw : pos l w ∈ segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inr b))) :
    w = Sum.inl i ∨ w = Sum.inr b := by
  have _ := hl
  rcases w with j | c
  · by_cases hji : j = i
    · exact Or.inl (congrArg Sum.inl hji)
    exfalso
    have hji' : (j : ℕ) ≠ i := Fin.val_ne_of_ne hji
    cases b
    · exact notMem_segment_of_ne_zero (innerSpokeFun_equator_ne_zero i j hji')
        (innerSpokeFun_equator_self i) (innerSpokeFun_innerApex i) hw
    · exact notMem_segment_of_pos_of_nonpos (tangentFun_equator_pos i j hji')
        (tangentFun_equator_self i).le (tangentFun_outerApex_neg i l i.isLt).le hw
  · cases b <;> cases c
    · exact Or.inr rfl
    · exact absurd (lineFun_nonneg_of_mem_segment (tangentFun_equator_self i).ge
        (tangentFun_innerApex_pos i).le hw) (not_le.2 (tangentFun_outerApex_neg i l i.isLt))
    · exact absurd (lineFun_nonpos_of_mem_segment (tangentFun_equator_self i).le
        (tangentFun_outerApex_neg i l i.isLt).le hw) (not_le.2 (tangentFun_innerApex_pos i))
    · exact Or.inr rfl

/-! ### Chords against spokes -/

/-- Adjacency in the cycle graph, in terms of the underlying naturals. -/
private theorem cycle_adj_cases {l : ℕ} {i j : Fin l} (h : (SimpleGraph.cycleGraph l).Adj i j) :
    (j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1 ∨ ((i : ℕ) = 0 ∧ (j : ℕ) + 1 = l) ∨
      ((j : ℕ) = 0 ∧ (i : ℕ) + 1 = l) := by
  have hi := i.isLt
  have hj := j.isLt
  rw [SimpleGraph.cycleGraph_adj', Fin.val_sub, Fin.val_sub] at h
  rcases h with h | h
  · rcases lt_or_ge (l - (j : ℕ) + i) l with hlt | hle
    · rw [Nat.mod_eq_of_lt hlt] at h
      omega
    · rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)] at h
      omega
  · rcases lt_or_ge (l - (i : ℕ) + j) l with hlt | hle
    · rw [Nat.mod_eq_of_lt hlt] at h
      omega
    · rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)] at h
      omega

/-- A chord `{i, j}` on the zero set of a functional that is positive at the apex, and a spoke
from `k` to that apex: if the functional is positive at `equator k` whenever `k ∉ {i, j}`,
the two segments meet only in positions of common endpoints. -/
private theorem chord_inter_spoke_of_fun (l : ℕ) (i j k : Fin l) (b : Bool) {a₁ a₂ a₃ : ℝ}
    (hi : lineFun a₁ a₂ a₃ (equator i) = 0) (hj : lineFun a₁ a₂ a₃ (equator j) = 0)
    (hb : 0 < lineFun a₁ a₂ a₃ (pos l (Sum.inr b)))
    (hk : k ≠ i → k ≠ j → 0 < lineFun a₁ a₂ a₃ (equator k)) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inr b)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inl j) ∧ w ∈ s(Sum.inl k, Sum.inr b)} := by
  by_cases hki : k = i
  · subst hki
    refine subset_image_of_subset_singleton ⟨Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩ ?_
    rw [Set.inter_comm]
    exact segment_inter_segment_subset_singleton hi hb hi.le hj.le
  by_cases hkj : k = j
  · subst hkj
    refine subset_image_of_subset_singleton ⟨Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩ ?_
    rw [Set.inter_comm]
    exact segment_inter_segment_subset_singleton hj hb hi.le hj.le
  · exact subset_image_of_disjoint
      (segment_disjoint_of_pos_of_nonpos (hk hki hkj) hb hi.le hj.le).symm

/-- The short chord `{i, i+1}` against a spoke. -/
private theorem chord_inter_spoke_succ (l : ℕ) (i j k : Fin l) (b : Bool)
    (hj : (j : ℕ) = i + 1) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inr b)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inl j) ∧ w ∈ s(Sum.inl k, Sum.inr b)} := by
  have hkl := k.isLt
  have hil := i.isLt
  have hjl := j.isLt
  cases b
  · refine chord_inter_spoke_of_fun l i j k false (chordFun_equator_self i) ?_
      (chordFun_innerApex_pos i) ?_
    · rw [hj]
      exact chordFun_equator_succ i
    · intro hki hkj
      exact chordFun_equator_pos i k (Fin.val_ne_of_ne hki) (hj ▸ Fin.val_ne_of_ne hkj)
  · by_cases hki : k = i
    · subst hki
      refine subset_image_of_subset_singleton ⟨Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩ ?_
      exact segment_inter_segment_subset_singleton_of_ne_zero (outerSpokeFun_equator_self l _)
        (outerSpokeFun_equator_pos l _ _ (Fin.isLt _) (Fin.isLt _) (by omega)).ne'
        (outerSpokeFun_equator_self l _) (outerSpokeFun_outerApex l _)
    by_cases hkj : k = j
    · subst hkj
      refine subset_image_of_subset_singleton ⟨Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩ ?_
      rw [segment_symm ℝ (pos l (Sum.inl i))]
      exact segment_inter_segment_subset_singleton_of_ne_zero (outerSpokeFun_equator_self l _)
        (outerSpokeFun_equator_neg l _ _ (Fin.isLt _) (Fin.isLt _) (by omega)).ne
        (outerSpokeFun_equator_self l _) (outerSpokeFun_outerApex l _)
    have hki' : (k : ℕ) ≠ i := Fin.val_ne_of_ne hki
    have hkj' : (k : ℕ) ≠ j := Fin.val_ne_of_ne hkj
    refine subset_image_of_disjoint ?_
    rcases lt_or_gt_of_ne hki' with h | h
    · exact segment_disjoint_of_pos_of_nonpos (outerSpokeFun_equator_pos l k i hkl hil h)
        (outerSpokeFun_equator_pos l k j hkl hjl (by omega)) (outerSpokeFun_equator_self l k).le
        (outerSpokeFun_outerApex l k).le
    · exact segment_disjoint_of_neg_of_nonneg (outerSpokeFun_equator_neg l k i hkl hil h)
        (outerSpokeFun_equator_neg l k j hkl hjl (by omega)) (outerSpokeFun_equator_self l k).ge
        (outerSpokeFun_outerApex l k).ge

/-- The long chord `{0, l-1}` against a spoke. -/
private theorem chord_inter_spoke_long (l : ℕ) (hl : 3 ≤ l) (i j k : Fin l) (b : Bool)
    (hi : (i : ℕ) = 0) (hj : (j : ℕ) + 1 = l) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inr b)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inl j) ∧ w ∈ s(Sum.inl k, Sum.inr b)} := by
  have hi0 : longFun l (equator i) = 0 := by
    rw [hi]
    exact longFun_equator_zero l
  have hj0 : longFun l (equator j) = 0 := by
    have hj' : (j : ℕ) = l - 1 := by omega
    rw [hj']
    exact longFun_equator_last l (by omega)
  have hk : k ≠ i → k ≠ j → 0 < longFun l (equator k) := fun hki hkj ↦
    longFun_equator_pos l k k.isLt (fun h ↦ Fin.val_ne_of_ne hki (h.trans hi.symm))
      (fun h ↦ Fin.val_ne_of_ne hkj (by omega))
  cases b
  · exact chord_inter_spoke_of_fun l i j k false hi0 hj0 (longFun_innerApex_pos l hl) hk
  · exact chord_inter_spoke_of_fun l i j k true hi0 hj0 (longFun_outerApex_pos l (by omega)) hk

/-- An equatorial edge and a spoke meet only in positions of common endpoints. -/
theorem chord_inter_spoke (l : ℕ) (hl : 3 ≤ l) (i j k : Fin l) (b : Bool)
    (hij : (SimpleGraph.cycleGraph l).Adj i j) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inr b)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inl j) ∧ w ∈ s(Sum.inl k, Sum.inr b)} := by
  rcases cycle_adj_cases hij with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact chord_inter_spoke_succ l i j k b h
  · have := chord_inter_spoke_succ l j i k b h
    rwa [segment_symm ℝ (pos l (Sum.inl j)), Sym2.eq_swap (a := Sum.inl j)] at this
  · exact chord_inter_spoke_long l hl i j k b h1 h2
  · have := chord_inter_spoke_long l hl j i k b h1 h2
    rwa [segment_symm ℝ (pos l (Sum.inl j)), Sym2.eq_swap (a := Sum.inl j)] at this

/-! ### Spokes against spokes -/

/-- An inner spoke and an outer spoke meet only in positions of common endpoints. -/
private theorem inner_inter_outer (l : ℕ) (i k : Fin l) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inr false)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inr true)) ⊆
      pos l '' {w : Fin l ⊕ Bool |
        w ∈ s(Sum.inl i, Sum.inr false) ∧ w ∈ s(Sum.inl k, Sum.inr true)} := by
  have hB := tangentFun_outerApex_neg k l k.isLt
  have hA := tangentFun_innerApex_pos k
  by_cases hki : k = i
  · subst hki
    have hv : 0 ≤ tangentFun k (equator k) := (tangentFun_equator_self k).ge
    refine subset_image_of_subset_singleton ⟨Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩ ?_
    rw [Set.inter_comm]
    exact segment_inter_segment_subset_singleton_of_neg (tangentFun_equator_self k) hB hv hA.le
  · exact subset_image_of_disjoint (segment_disjoint_of_pos_of_nonpos
      (tangentFun_equator_pos k i (Fin.val_ne_of_ne (Ne.symm hki))) hA
      (tangentFun_equator_self k).le hB.le)

/-- Two distinct spokes meet only in positions of common endpoints. -/
theorem spoke_inter_spoke (l : ℕ) (hl : 3 ≤ l) (i k : Fin l) (b c : Bool)
    (hne : s(Sum.inl i, Sum.inr b) ≠ s((Sum.inl k : Fin l ⊕ Bool), Sum.inr c)) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inr b)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inr c)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inr b) ∧ w ∈ s(Sum.inl k, Sum.inr c)} := by
  have _ := hl
  cases b <;> cases c
  · have hik : (i : ℕ) ≠ k := fun h ↦ hne (by rw [Fin.ext h])
    refine subset_image_of_subset_singleton ⟨Sym2.mem_mk_right _ _, Sym2.mem_mk_right _ _⟩ ?_
    rw [Set.inter_comm, segment_symm ℝ (pos l (Sum.inl k))]
    exact segment_inter_segment_subset_singleton_of_ne_zero (innerSpokeFun_innerApex i)
      (innerSpokeFun_equator_ne_zero i k (Ne.symm hik)) (innerSpokeFun_equator_self i)
      (innerSpokeFun_innerApex i)
  · exact inner_inter_outer l i k
  · have := inner_inter_outer l k i
    rw [Set.inter_comm] at this
    exact this.trans (Set.image_mono fun w hw ↦ ⟨hw.2, hw.1⟩)
  · have hik : (i : ℕ) ≠ k := fun h ↦ hne (by rw [Fin.ext h])
    refine subset_image_of_subset_singleton ⟨Sym2.mem_mk_right _ _, Sym2.mem_mk_right _ _⟩ ?_
    rw [Set.inter_comm, segment_symm ℝ (pos l (Sum.inl k))]
    refine segment_inter_segment_subset_singleton_of_ne_zero (outerSpokeFun_outerApex l i) ?_
      (outerSpokeFun_equator_self l i) (outerSpokeFun_outerApex l i)
    rcases lt_or_gt_of_ne hik with h | h
    · exact (outerSpokeFun_equator_pos l i k i.isLt k.isLt h).ne'
    · exact (outerSpokeFun_equator_neg l i k i.isLt k.isLt h).ne

end Bipyramid
