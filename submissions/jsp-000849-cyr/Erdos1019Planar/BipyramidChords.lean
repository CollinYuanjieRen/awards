import Erdos1019Planar.BipyramidLines

/-!
# Chords of the bipyramid drawing

The equatorial edges of `bipyramidGraph l` are the edges of `cycleGraph l`: the short chords
`{i, i+1}` (`i + 1 < l`) and the long chord `{l-1, 0}`.  In the drawing of `BipyramidLines`
every short chord lies on the line `chordFun i = 0`, with all other vertices strictly above it
except the outer apex, which is strictly below; the long chord lies on `longFun l = 0` with all
other vertices strictly on one side.  Hence no vertex lies on a non-incident chord and two
distinct chords meet only in a common endpoint.
-/

open Set
open scoped SimpleGraph

namespace Bipyramid

/-- Adjacent vertices of `cycleGraph l` differ by one, cyclically. -/
private theorem cycle_adj_cases {l : ℕ} {i j : Fin l} (h : (SimpleGraph.cycleGraph l).Adj i j) :
    (j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1 ∨ ((i : ℕ) = 0 ∧ (j : ℕ) + 1 = l) ∨
      ((j : ℕ) = 0 ∧ (i : ℕ) + 1 = l) := by
  have hi := i.isLt
  have hj := j.isLt
  rw [SimpleGraph.cycleGraph_adj'] at h
  rcases h with h | h
  · rcases le_or_gt j i with hle | hlt
    · rw [Fin.sub_val_of_le hle] at h
      omega
    · rw [Fin.coe_sub_iff_lt.2 hlt] at h
      have := Fin.lt_def.1 hlt
      omega
  · rcases le_or_gt i j with hle | hlt
    · rw [Fin.sub_val_of_le hle] at h
      omega
    · rw [Fin.coe_sub_iff_lt.2 hlt] at h
      have := Fin.lt_def.1 hlt
      omega

/-- The short chord `{i, i+1}` lies on `chordFun i = 0`, and no other vertex does. -/
private theorem short_chord_zero {l : ℕ} {i j : Fin l} (hij : (j : ℕ) = i + 1) :
    chordFun i (pos l (Sum.inl i)) = 0 ∧ chordFun i (pos l (Sum.inl j)) = 0 ∧
      ∀ w : Fin l ⊕ Bool, chordFun i (pos l w) = 0 → w = Sum.inl i ∨ w = Sum.inl j := by
  have hj := j.isLt
  refine ⟨chordFun_equator_self i, ?_, ?_⟩
  · show chordFun i (equator j) = 0
    rw [hij]
    exact chordFun_equator_succ i
  · rintro (n | b) hn
    · by_contra hne
      rw [not_or] at hne
      refine (chordFun_equator_pos i n ?_ ?_).ne' hn
      · exact fun h ↦ hne.1 (congrArg Sum.inl (Fin.ext h))
      · exact fun h ↦ hne.2 (congrArg Sum.inl (Fin.ext (by omega)))
    · cases b
      · exact absurd hn (chordFun_innerApex_pos i).ne'
      · exact absurd hn (chordFun_outerApex_neg i l (by omega)).ne

/-- The long chord `{0, l-1}` lies on `longFun l = 0`, and no other vertex does. -/
private theorem long_chord_zero {l : ℕ} (hl : 3 ≤ l) {i j : Fin l} (hi : (i : ℕ) = 0)
    (hj : (j : ℕ) + 1 = l) :
    longFun l (pos l (Sum.inl i)) = 0 ∧ longFun l (pos l (Sum.inl j)) = 0 ∧
      ∀ w : Fin l ⊕ Bool, longFun l (pos l w) = 0 → w = Sum.inl i ∨ w = Sum.inl j := by
  refine ⟨?_, ?_, ?_⟩
  · show longFun l (equator i) = 0
    rw [hi]
    exact longFun_equator_zero l
  · show longFun l (equator j) = 0
    rw [show (j : ℕ) = l - 1 by omega]
    exact longFun_equator_last l (by omega)
  · rintro (n | b) hn
    · by_contra hne
      rw [not_or] at hne
      refine (longFun_equator_pos l n n.isLt ?_ ?_).ne' hn
      · exact fun h ↦ hne.1 (congrArg Sum.inl (Fin.ext (by omega)))
      · exact fun h ↦ hne.2 (congrArg Sum.inl (Fin.ext (by omega)))
    · cases b
      · exact absurd hn (longFun_innerApex_pos l hl).ne'
      · exact absurd hn (longFun_outerApex_pos l (by omega)).ne'

/-- If a functional vanishes on the chord `{i, j}`, and `{k, m}` has `k` a common endpoint
while the functional is positive at `m`, the chords meet only in `pos l (inl k)`. -/
private theorem chord_inter_of_shared {l : ℕ} {a b c : ℝ} {i j k m : Fin l}
    (hi : lineFun a b c (pos l (Sum.inl i)) = 0) (hj : lineFun a b c (pos l (Sum.inl j)) = 0)
    (hk : k = i ∨ k = j) (hm : 0 < lineFun a b c (pos l (Sum.inl m))) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inl m)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inl j) ∧ w ∈ s(Sum.inl k, Sum.inl m)} := by
  have hk0 : lineFun a b c (pos l (Sum.inl k)) = 0 := by
    rcases hk with h | h <;> rw [h] <;> assumption
  rw [Set.inter_comm]
  refine (segment_inter_segment_subset_singleton hk0 hm hi.le hj.le).trans ?_
  rw [Set.singleton_subset_iff]
  refine ⟨Sum.inl k, ⟨?_, Sym2.mem_mk_left _ _⟩, rfl⟩
  exact Sym2.mem_iff.2 (hk.imp (congrArg Sum.inl) (congrArg Sum.inl))

/-- Core of `chord_inter_chord`: a functional vanishing exactly on the endpoints of the chord
`{i, j}` among all vertices, and nonnegative on the equator, separates this chord from every
other chord `{k, m}` except at common endpoints. -/
private theorem chord_inter_of_lineFun {l : ℕ} {a b c : ℝ} {i j k m : Fin l}
    (hi : lineFun a b c (pos l (Sum.inl i)) = 0) (hj : lineFun a b c (pos l (Sum.inl j)) = 0)
    (hnn : ∀ n : Fin l, 0 ≤ lineFun a b c (pos l (Sum.inl n)))
    (hzero : ∀ w : Fin l ⊕ Bool, lineFun a b c (pos l w) = 0 → w = Sum.inl i ∨ w = Sum.inl j)
    (hkm : k ≠ m) (hne : s(i, j) ≠ s(k, m)) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inl m)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inl j) ∧ w ∈ s(Sum.inl k, Sum.inl m)} := by
  have key : ∀ n : Fin l, ¬(n = i ∨ n = j) → 0 < lineFun a b c (pos l (Sum.inl n)) :=
    fun n hn ↦ lt_of_le_of_ne (hnn n)
      fun h ↦ hn ((hzero _ h.symm).imp Sum.inl.inj Sum.inl.inj)
  by_cases hk : k = i ∨ k = j
  · by_cases hm : m = i ∨ m = j
    · exfalso
      apply hne
      rcases hk with rfl | rfl <;> rcases hm with rfl | rfl
      · exact absurd rfl hkm
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hkm
    · exact chord_inter_of_shared hi hj hk (key m hm)
  · by_cases hm : m = i ∨ m = j
    · rw [segment_symm ℝ (pos l (Sum.inl k)), Sym2.eq_swap (a := Sum.inl k)]
      exact chord_inter_of_shared hi hj hm (key k hk)
    · have hd := segment_disjoint_of_pos_of_nonpos (key k hk) (key m hm) hi.le hj.le
      rw [Set.inter_comm, Set.disjoint_iff_inter_eq_empty.1 hd]
      exact Set.empty_subset _

/-- A vertex on the segment of an equatorial edge is one of its endpoints. -/
theorem vertex_mem_chord (l : ℕ) (hl : 3 ≤ l) (i j : Fin l)
    (hij : (SimpleGraph.cycleGraph l).Adj i j) (w : Fin l ⊕ Bool)
    (hw : pos l w ∈ segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j))) :
    w = Sum.inl i ∨ w = Sum.inl j := by
  rcases cycle_adj_cases hij with h | h | h | h
  · obtain ⟨h1, h2, h3⟩ := short_chord_zero h
    exact h3 w (lineFun_eq_zero_of_mem_segment h1 h2 hw)
  · obtain ⟨h1, h2, h3⟩ := short_chord_zero h
    rw [segment_symm] at hw
    exact (h3 w (lineFun_eq_zero_of_mem_segment h1 h2 hw)).symm
  · obtain ⟨h1, h2, h3⟩ := long_chord_zero hl h.1 h.2
    exact h3 w (lineFun_eq_zero_of_mem_segment h1 h2 hw)
  · obtain ⟨h1, h2, h3⟩ := long_chord_zero hl h.1 h.2
    rw [segment_symm] at hw
    exact (h3 w (lineFun_eq_zero_of_mem_segment h1 h2 hw)).symm

/-- Two distinct equatorial edges meet only in positions of common endpoints. -/
theorem chord_inter_chord (l : ℕ) (hl : 3 ≤ l) (i j k m : Fin l)
    (hij : (SimpleGraph.cycleGraph l).Adj i j) (hkm : (SimpleGraph.cycleGraph l).Adj k m)
    (hne : s(i, j) ≠ s(k, m)) :
    segment ℝ (pos l (Sum.inl i)) (pos l (Sum.inl j)) ∩
        segment ℝ (pos l (Sum.inl k)) (pos l (Sum.inl m)) ⊆
      pos l '' {w : Fin l ⊕ Bool | w ∈ s(Sum.inl i, Sum.inl j) ∧ w ∈ s(Sum.inl k, Sum.inl m)} := by
  have hne' : s(j, i) ≠ s(k, m) := by rwa [Sym2.eq_swap (a := j)]
  rcases cycle_adj_cases hij with h | h | h | h
  · obtain ⟨h1, h2, h3⟩ := short_chord_zero h
    exact chord_inter_of_lineFun h1 h2 (fun n ↦ chordFun_equator_nonneg _ _) h3 hkm.ne hne
  · obtain ⟨h1, h2, h3⟩ := short_chord_zero h
    rw [segment_symm ℝ (pos l (Sum.inl i)), Sym2.eq_swap (a := Sum.inl i)]
    exact chord_inter_of_lineFun h1 h2 (fun n ↦ chordFun_equator_nonneg _ _) h3 hkm.ne hne'
  · obtain ⟨h1, h2, h3⟩ := long_chord_zero hl h.1 h.2
    exact chord_inter_of_lineFun h1 h2 (fun n ↦ longFun_equator_nonneg _ _ n.isLt) h3 hkm.ne hne
  · obtain ⟨h1, h2, h3⟩ := long_chord_zero hl h.1 h.2
    rw [segment_symm ℝ (pos l (Sum.inl i)), Sym2.eq_swap (a := Sum.inl i)]
    exact chord_inter_of_lineFun h1 h2 (fun n ↦ longFun_equator_nonneg _ _ n.isLt) h3 hkm.ne hne'

end Bipyramid
