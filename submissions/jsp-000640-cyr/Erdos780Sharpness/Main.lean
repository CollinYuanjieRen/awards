import Mathlib

/-!
# Erdős Problem #780: sharpness of the Alon–Frankl–Lovász bound

Erdős asked to prove that if `n ≥ kr + (t − 1)(k − 1)` and the edges of the complete `r`-uniform
hypergraph on `n` vertices are `t`-coloured, then some colour class contains `k` pairwise
disjoint edges (PROVED by Alon–Frankl–Lovász; the Kneser-graph chromatic number; NOT formalized
here).  The problem page records that the bound is best possible: "if `n = kr − 1 + (t − 1)(k − 1)`
then decomposing `[n]` as one set `X_1` of size `kr − 1` and `t − 1` sets `X_2, …, X_t` of size
`k − 1`, a colouring without `k` pairwise disjoint edges is given colouring all subsets of `X_1`
in colour `1` and assigning an edge with colour `2 ≤ i ≤ t` if `i` is minimal such that `X_i`
intersects the edge."  (The page writes `X_0` once for `X_1`.)  This file proves that sharpness
statement for all `k, r, t ≥ 1`.

Vertices are `Fin n` with `n = k * r - 1 + (t - 1) * (k - 1)`; `X_1 = {v | v < kr − 1}` and, for
`2 ≤ i ≤ t`, `X_i = {v | kr − 1 + (i − 2)(k − 1) ≤ v < kr − 1 + (i − 1)(k − 1)}`.  We index colours
by `Fin t` (`0` for the page's colour `1`, and `i − 1` for colour `i`): `blockOf v` is `0` on `X_1`
and `i − 1` on `X_i`; the colour of an edge `e` is `0` if `e ⊆ X_1` and otherwise the least
nonzero block index met by `e` (an `sInf`, which is `0` exactly when `e ⊆ X_1`).

Why it works: a colour-`0` family of `k` pairwise disjoint `r`-edges would need `kr` vertices of
`X_1`, which has only `kr − 1`; a family of pairwise disjoint edges of colour `i ≥ 1` picks
distinct vertices of `X_{i+1}`, which has only `k − 1`.  The theorem itself (the lower bound) is
out of scope; there is no formal-conjectures rendering of this problem, and the definitions are
ours.
-/

namespace Erdos780

/-- The block index of a vertex: `0` on `X_1 = [0, kr − 1)`, and `1 + (v − (kr − 1)) / (k − 1)`
(the index `i − 1` of the block `X_i`) beyond. -/
def blockOf (k r v : ℕ) : ℕ :=
  if v < k * r - 1 then 0 else 1 + (v - (k * r - 1)) / (k - 1)

/-- The colour of an edge (as a natural number): `0` if all its vertices lie in `X_1`, otherwise
the least nonzero block index among its vertices. -/
noncomputable def colourNat (k r : ℕ) {n : ℕ} (e : Finset (Fin n)) : ℕ :=
  sInf {i | 0 < i ∧ ∃ v ∈ e, blockOf k r v = i}

/-- The colouring with `t` colours, clipping the (always in-range) value into `Fin t`. -/
noncomputable def colour (k r t : ℕ) (ht : 1 ≤ t) {n : ℕ} (e : Finset (Fin n)) : Fin t :=
  ⟨min (colourNat k r e) (t - 1), by omega⟩

/-- A vertex has block index `0` exactly when it lies in `X_1 = [0, kr − 1)`. -/
theorem blockOf_eq_zero_iff (k r v : ℕ) : blockOf k r v = 0 ↔ v < k * r - 1 := by
  by_cases h : v < k * r - 1 <;> simp [blockOf, h]

/-- Every vertex of `[n]`, `n = kr − 1 + (t − 1)(k − 1)`, has block index at most `t − 1`. -/
theorem blockOf_le (k r t v : ℕ) (hv : v < k * r - 1 + (t - 1) * (k - 1)) :
    blockOf k r v ≤ t - 1 := by
  rw [blockOf]
  split
  · omega
  · rename_i hnl
    have h1 : (v - (k * r - 1)) / (k - 1) < t - 1 := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm (k - 1) (t - 1)]
      omega
    omega

/-- A nonzero colour of an edge is realised by one of its vertices. -/
theorem exists_blockOf_of_colourNat_pos (k r : ℕ) {n : ℕ} (e : Finset (Fin n))
    (h : 0 < colourNat k r e) : ∃ v ∈ e, blockOf k r (v : ℕ) = colourNat k r e := by
  have hne : Set.Nonempty {j | 0 < j ∧ ∃ v ∈ e, blockOf k r (v : ℕ) = j} := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have : colourNat k r e = 0 := by
      rw [colourNat, hc]
      exact Nat.sInf_empty
    omega
  exact (Nat.sInf_mem hne).2

/-- Every vertex of an edge of colour `0` lies in `X_1`. -/
theorem lt_of_colourNat_eq_zero (k r : ℕ) {n : ℕ} (e : Finset (Fin n))
    (h : colourNat k r e = 0) {v : Fin n} (hv : v ∈ e) : (v : ℕ) < k * r - 1 := by
  rw [← blockOf_eq_zero_iff]
  by_contra hc
  have hne : Set.Nonempty {j | 0 < j ∧ ∃ w ∈ e, blockOf k r (w : ℕ) = j} :=
    ⟨blockOf k r (v : ℕ), Nat.pos_of_ne_zero hc, v, hv, rfl⟩
  have h0 : 0 < colourNat k r e := (Nat.sInf_mem hne).1
  omega

/-- The colour of an edge of `[n]` is always at most `t − 1`, so `colour` does not clip. -/
theorem colourNat_le (k r t : ℕ) (e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1)))) :
    colourNat k r e ≤ t - 1 := by
  rcases Nat.eq_zero_or_pos (colourNat k r e) with h | h
  · omega
  · obtain ⟨v, -, hv⟩ := exists_blockOf_of_colourNat_pos k r e h
    rw [← hv]
    exact blockOf_le k r t (v : ℕ) v.isLt

/-- For `i ≥ 1` and `k ≥ 2` the block `X_{i+1}` contains at most `k − 1` vertices. -/
theorem card_block_le (k r t c : ℕ) (hk : 2 ≤ k) (hc : 0 < c) :
    ((Finset.range (k * r - 1 + (t - 1) * (k - 1))).filter
      (fun v => blockOf k r v = c)).card ≤ k - 1 := by
  have hk1 : 0 < k - 1 := by omega
  have hsub : (Finset.range (k * r - 1 + (t - 1) * (k - 1))).filter (fun v => blockOf k r v = c)
      ⊆ Finset.Ico (k * r - 1 + (c - 1) * (k - 1))
          (k * r - 1 + (c - 1) * (k - 1) + (k - 1)) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    have hb := hv.2
    rw [blockOf] at hb
    split at hb
    · exact absurd hb (by omega)
    · rename_i hnl
      have hmod : (v - (k * r - 1)) / (k - 1) * (k - 1) + (v - (k * r - 1)) % (k - 1)
          = v - (k * r - 1) := Nat.div_add_mod' _ _
      have hlt : (v - (k * r - 1)) % (k - 1) < k - 1 := Nat.mod_lt _ hk1
      have hq : (v - (k * r - 1)) / (k - 1) = c - 1 := by omega
      rw [hq] at hmod
      rw [Finset.mem_Ico]
      omega
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Nat.card_Ico]
  omega

/-- A choice-free selection of a vertex of block `c` from an edge meeting that block: the least
such vertex, described by an `sInf` on `ℕ`. -/
theorem exists_mem_of_sInf (k r c : ℕ) {n : ℕ} (e : Finset (Fin n))
    (h : ∃ w ∈ e, blockOf k r (w : ℕ) = c) :
    ∃ w ∈ e, (w : ℕ) = sInf {v : ℕ | ∃ w ∈ e, (w : ℕ) = v ∧ blockOf k r v = c} ∧
      blockOf k r (sInf {v : ℕ | ∃ w ∈ e, (w : ℕ) = v ∧ blockOf k r v = c}) = c := by
  obtain ⟨w, hw, hb⟩ := h
  have hne : Set.Nonempty {v : ℕ | ∃ w ∈ e, (w : ℕ) = v ∧ blockOf k r v = c} :=
    ⟨(w : ℕ), w, hw, rfl, hb⟩
  exact Nat.sInf_mem hne

/-- **Erdős #780, sharpness (page-faithful form)**: for `k, r, t ≥ 1` and
`n = kr − 1 + (t − 1)(k − 1)`, the colouring `colour k r t` of the `r`-subsets of `[n]` has no `k`
pairwise disjoint edges of one colour. -/
theorem no_k_disjoint (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t) (i : Fin t)
    (F : Finset (Finset (Fin (k * r - 1 + (t - 1) * (k - 1)))))
    (hF : ∀ e ∈ F, e.card = r ∧ colour k r t ht e = i)
    (hdisj : ∀ e ∈ F, ∀ e' ∈ F, e ≠ e' → Disjoint e e') : F.card < k := by
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · -- `k = 1`: there is no `r`-subset at all, since `n = r - 1 < r`.
    have hk1' : k = 1 := by omega
    subst hk1'
    have hempty : F = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      have hc := (hF e he).1
      have h1 : e.card ≤ 1 * r - 1 + (t - 1) * (1 - 1) := by
        simpa [Finset.card_univ] using Finset.card_le_univ e
      omega
    rw [hempty, Finset.card_empty]
    omega
  · -- `k ≥ 2`.
    have hcol : ∀ e ∈ F, colourNat k r e = (i : ℕ) := by
      intro e he
      have h2 := (hF e he).2
      have h3 : min (colourNat k r e) (t - 1) = (i : ℕ) := congrArg Fin.val h2
      have h4 : colourNat k r e ≤ t - 1 := colourNat_le k r t e
      omega
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
    · -- colour `0`: all edges live inside `X_1`, which has only `kr - 1` vertices.
      have hsub : ∀ e ∈ F, ∀ v ∈ e, (v : ℕ) < k * r - 1 := by
        intro e he v hv
        exact lt_of_colourNat_eq_zero k r e (by rw [hcol e he, hi0]) hv
      have hbu : (F.biUnion (fun e => e)).card ≤ k * r - 1 := by
        have h := Finset.card_le_card_of_injOn
          (f := fun v : Fin (k * r - 1 + (t - 1) * (k - 1)) => (v : ℕ))
          (s := F.biUnion (fun e => e)) (t := Finset.range (k * r - 1))
          (fun v hv => by
            simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, exists_prop] at hv
            obtain ⟨e, he, hve⟩ := hv
            exact Finset.mem_coe.mpr (Finset.mem_range.mpr (hsub e he v hve)))
          (fun a _ b _ hab => Fin.val_injective hab)
        simpa using h
      have hcard : (F.biUnion (fun e => e)).card = F.card * r :=
        calc (F.biUnion (fun e => e)).card = ∑ e ∈ F, e.card := Finset.card_biUnion hdisj
          _ = ∑ _e ∈ F, r := Finset.sum_congr rfl (fun e he => (hF e he).1)
          _ = F.card * r := by rw [Finset.sum_const, smul_eq_mul]
      have hkr : 0 < k * r := Nat.mul_pos (by omega) hr
      have hmul : F.card * r < k * r := by omega
      exact lt_of_mul_lt_mul_right hmul (Nat.zero_le r)
    · -- colour `i ≥ 1`: distinct edges pick distinct vertices of the block `X_{i+1}`.
      have hex : ∀ e ∈ F, ∃ w ∈ e, blockOf k r (w : ℕ) = (i : ℕ) := by
        intro e he
        have h0 : 0 < colourNat k r e := by rw [hcol e he]; exact hipos
        obtain ⟨w, hw, hb⟩ := exists_blockOf_of_colourNat_pos k r e h0
        exact ⟨w, hw, by rw [hb, hcol e he]⟩
      by_contra hcon
      push Not at hcon
      have hlt : ((Finset.range (k * r - 1 + (t - 1) * (k - 1))).filter
          (fun v => blockOf k r v = (i : ℕ))).card < F.card := by
        have := card_block_le k r t (i : ℕ) hk2 hipos
        omega
      have hmaps : ∀ e ∈ F,
          (fun e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) =>
            sInf {v : ℕ | ∃ w ∈ e, (w : ℕ) = v ∧ blockOf k r v = (i : ℕ)}) e ∈
          (Finset.range (k * r - 1 + (t - 1) * (k - 1))).filter
            (fun v => blockOf k r v = (i : ℕ)) := by
        intro e he
        obtain ⟨w, -, hwv, hb⟩ := exists_mem_of_sInf k r (i : ℕ) e (hex e he)
        have hlt' : sInf {v : ℕ | ∃ w ∈ e, (w : ℕ) = v ∧ blockOf k r v = (i : ℕ)}
            < k * r - 1 + (t - 1) * (k - 1) := by
          rw [← hwv]; exact w.isLt
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt', hb⟩
      obtain ⟨e, he, e', he', hne, hfe⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
      obtain ⟨w, hw, hwv, -⟩ := exists_mem_of_sInf k r (i : ℕ) e (hex e he)
      obtain ⟨w', hw', hwv', -⟩ := exists_mem_of_sInf k r (i : ℕ) e' (hex e' he')
      have hww : w = w' := Fin.val_injective (by rw [hwv, hwv']; exact hfe)
      exact Finset.disjoint_left.mp (hdisj e he e' he' hne) hw (hww ▸ hw')

/-- **Erdős #780, sharpness**: for `k, r, t ≥ 1` there is a `t`-colouring of the `r`-subsets of
`[kr − 1 + (t − 1)(k − 1)]` with no `k` pairwise disjoint edges of one colour. -/
theorem erdos_780_sharp (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    ∃ c : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) → Fin t,
      ∀ (i : Fin t) (F : Finset (Finset (Fin (k * r - 1 + (t - 1) * (k - 1))))),
        (∀ e ∈ F, e.card = r ∧ c e = i) → (∀ e ∈ F, ∀ e' ∈ F, e ≠ e' → Disjoint e e') →
          F.card < k := by
  exact ⟨colour k r t ht, fun i F hF hdisj => no_k_disjoint k r t hk hr ht i F hF hdisj⟩

end Erdos780

/-- **Erdős #780, sharpness, closed form**: there are no `k, r, t ≥ 1` such that every
`t`-colouring of the `r`-subsets of `[kr − 1 + (t − 1)(k − 1)]` has `k` pairwise disjoint edges
of one colour. -/
theorem erdos_780_sharpness_closed :
    ¬ ∃ k r t : ℕ, 1 ≤ k ∧ 1 ≤ r ∧ 1 ≤ t ∧
      ∀ c : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) → Fin t,
        ∃ (i : Fin t) (F : Finset (Finset (Fin (k * r - 1 + (t - 1) * (k - 1))))),
          (∀ e ∈ F, e.card = r ∧ c e = i) ∧ (∀ e ∈ F, ∀ e' ∈ F, e ≠ e' → Disjoint e e') ∧
            k ≤ F.card := by
  rintro ⟨k, r, t, hk, hr, ht, hall⟩
  obtain ⟨c, hc⟩ := Erdos780.erdos_780_sharp k r t hk hr ht
  obtain ⟨i, F, hF, hdisj, hkF⟩ := hall c
  exact absurd (hc i F hF hdisj) (not_lt.mpr hkF)
