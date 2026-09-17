import Erdos1078Haxell.Invariants

/-! Terminal steps of the augmenting procedure: completion and improvement. -/

set_option linter.unusedSectionVars false

namespace Erdos1078

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → ι)

private lemma mem_leaves_iff {M : Finset V} {x y : V} :
    y ∈ leaves G M x ↔ y ∈ M ∧ G.Adj x y := by
  rw [leaves, Finset.mem_filter]

/-- A centre without leaves has no neighbour in `M`. -/
private lemma not_adj_of_leaves_empty {M : Finset V} {x : V} (h : leaves G M x = ∅) :
    ∀ v ∈ M, ¬ G.Adj x v := by
  intro v hv hadj
  have hmem : v ∈ leaves G M x := (mem_leaves_iff G).mpr ⟨hv, hadj⟩
  rw [h] at hmem
  exact absurd hmem (Finset.notMem_empty v)

/-- Validity restricts to prefixes of the list of centres. -/
private lemma valid_take {a : ι} {M : Finset V} {xs : List V} (hV : Valid G part a M xs) (k : ℕ) :
    Valid G part a M (xs.take k) := by
  refine { pit := hV.pit, miss := hV.miss, chain := ?_, nonempty := ?_ }
  · intro i hi
    have h := hi
    rw [List.length_take] at h
    have htake : (xs.take k).take i = xs.take i := by
      rw [List.take_take, min_eq_left (by omega : i ≤ k)]
    rw [List.getElem_take, htake]
    exact hV.chain i (by omega)
  · intro i hi
    have h := hi
    rw [List.length_take] at h
    rw [List.getElem_take]
    exact hV.nonempty i (by omega)

/-- Completion: a last centre without leaves lying in the root class extends `M`. -/
theorem step_done {a : ι} {M : Finset V} {xs : List V} (hV : Valid G part a M xs)
    (hne : xs ≠ []) (hlast : leaves G M (xs.getLast hne) = ∅) (ha : part (xs.getLast hne) = a) :
    IsPIT G part (insert (xs.getLast hne) M) ∧
      (insert (xs.getLast hne) M).image part = insert a (M.image part) := by
  set x := xs.getLast hne with hxdef
  have hnadj : ∀ v ∈ M, ¬ G.Adj x v := not_adj_of_leaves_empty G hlast
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v hv w hw
    rw [Finset.mem_insert] at hv hw
    rcases hv with rfl | hv
    · rcases hw with rfl | hw
      · exact G.irrefl
      · exact hnadj w hw
    · rcases hw with rfl | hw
      · exact fun hadj => hnadj v hv hadj.symm
      · exact hV.pit.1 v hv w hw
  · intro v hv w hw hvw
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hv hw
    rcases hv with rfl | hv
    · rcases hw with rfl | hw
      · rfl
      · exact absurd (by rw [← hvw]; exact ha : part w = a) (hV.miss w hw)
    · rcases hw with rfl | hw
      · exact absurd (by rw [hvw]; exact ha : part v = a) (hV.miss v hv)
      · exact hV.pit.2 (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hw) hvw
  · rw [Finset.image_insert, ha]

/-- Improvement: a last centre without leaves in a non-root class replaces the leaf of its class,
truncating the constellation; validity is kept, the signature decreases and the classes covered
by `M` are unchanged. -/
theorem step_improve {a : ι} {M : Finset V} {xs : List V} (hV : Valid G part a M xs)
    (hne : xs ≠ []) (hlast : leaves G M (xs.getLast hne) = ∅) (ha : part (xs.getLast hne) ≠ a) :
    ∃ (M' : Finset V) (xs' : List V), Valid G part a M' xs' ∧ vec ι G M' xs' < vec ι G M xs ∧
      M'.image part = M.image part := by
  have htpos : 0 < xs.length := List.length_pos_iff.mpr hne
  have hlt1 : xs.length - 1 < xs.length := by omega
  have hxeq : xs.getLast hne = xs[xs.length - 1] := List.getLast_eq_getElem hne
  rw [hxeq] at hlast ha
  have hnadjM : ∀ v ∈ M, ¬ G.Adj xs[xs.length - 1] v := not_adj_of_leaves_empty G hlast
  obtain ⟨hch1, hch2⟩ := hV.chain (xs.length - 1) hlt1
  -- The class of the last centre is the class of some earlier leaf `y`.
  rw [classes, Finset.mem_insert] at hch1
  rcases hch1 with hcon | hch1
  · exact absurd hcon ha
  obtain ⟨y, hy, hpy⟩ := Finset.mem_image.mp hch1
  obtain ⟨c, hc, hyc⟩ := Finset.mem_biUnion.mp hy
  rw [List.mem_toFinset, List.mem_iff_getElem] at hc
  obtain ⟨j, hjlen, hcj⟩ := hc
  have hjlen' := hjlen
  rw [List.length_take] at hjlen'
  have hj1 : j < xs.length - 1 := by omega
  have hjt : j < xs.length := by omega
  rw [List.getElem_take] at hcj
  subst hcj
  -- `y` is a leaf of `xs[j]`.
  have hyM : y ∈ M := leaves_subset G M _ hyc
  have hadjjy : G.Adj xs[j] y := ((mem_leaves_iff G).mp hyc).2
  have hpartx : part xs[xs.length - 1] = part y := hpy.symm
  -- Earlier centres belong to the constellation, hence are not adjacent to the last centre.
  have hcentreT : ∀ i (hi : i < xs.length - 1),
      (xs[i]'(by omega)) ∈ Tset G M (xs.take (xs.length - 1)) := by
    intro i hi
    rw [Tset]
    refine Finset.mem_union_left _ ?_
    rw [List.mem_toFinset]
    have hlen : i < (xs.take (xs.length - 1)).length := by rw [List.length_take]; omega
    have hmem := List.getElem_mem hlen
    rwa [List.getElem_take] at hmem
  have hnadjx : ∀ i (hi : i < xs.length - 1),
      ¬ G.Adj (xs[i]'(by omega)) xs[xs.length - 1] := fun i hi => hch2 _ (hcentreT i hi)
  -- The last centre is not in `M`.
  have hxnotM : xs[xs.length - 1] ∉ M := by
    intro hmem
    have hyx : y = xs[xs.length - 1] :=
      hV.pit.2 (Finset.mem_coe.mpr hyM) (Finset.mem_coe.mpr hmem) hpy
    exact hnadjx j hj1 (hyx ▸ hadjjy)
  -- Leaves of the new state.
  have hleavesM' : ∀ i (hi : i ≤ j),
      leaves G (insert xs[xs.length - 1] (M.erase y)) (xs[i]'(by omega))
        = (leaves G M (xs[i]'(by omega))).erase y := by
    intro i hi
    ext z
    rw [Finset.mem_erase, mem_leaves_iff, mem_leaves_iff, Finset.mem_insert]
    constructor
    · rintro ⟨hz, hadj⟩
      rcases hz with rfl | hz
      · exact absurd hadj (hnadjx i (by omega))
      · exact ⟨(Finset.mem_erase.mp hz).1, (Finset.mem_erase.mp hz).2, hadj⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨Or.inr (Finset.mem_erase.mpr ⟨h1, h2⟩), h3⟩
  have hleavesEq : ∀ i (hi : i < j),
      leaves G (insert xs[xs.length - 1] (M.erase y)) (xs[i]'(by omega))
        = leaves G M (xs[i]'(by omega)) := by
    intro i hi
    rw [hleavesM' i (le_of_lt hi)]
    refine Finset.erase_eq_of_notMem ?_
    intro hmem
    exact Finset.disjoint_left.mp
      (leaves_disjoint G part hV (show i < xs.length by omega) hjt (by omega)) hmem hyc
  have hprefix : ∀ i, i ≤ j → ∀ c ∈ (xs.take i).toFinset,
      leaves G (insert xs[xs.length - 1] (M.erase y)) c = leaves G M c := by
    intro i hi c hc
    rw [List.mem_toFinset, List.mem_iff_getElem] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    have hk' := hk
    rw [List.length_take] at hk'
    rw [List.getElem_take]
    exact hleavesEq k (by omega)
  have hTsetEq : ∀ i, i ≤ j →
      Tset G (insert xs[xs.length - 1] (M.erase y)) (xs.take i) = Tset G M (xs.take i) := by
    intro i hi
    rw [Tset, Tset]
    congr 1
    exact Finset.biUnion_congr rfl (hprefix i hi)
  have hclassesEq : ∀ i, i ≤ j →
      classes G part (insert xs[xs.length - 1] (M.erase y)) a (xs.take i)
        = classes G part M a (xs.take i) := by
    intro i hi
    rw [classes, classes]
    congr 2
    exact Finset.biUnion_congr rfl (hprefix i hi)
  -- Validity of the new state.
  have hV' : Valid G part a (insert xs[xs.length - 1] (M.erase y)) (xs.take (j + 1)) := by
    refine { pit := ⟨?_, ?_⟩, miss := ?_, chain := ?_, nonempty := ?_ }
    · intro v hv w hw
      rw [Finset.mem_insert] at hv hw
      rcases hv with rfl | hv
      · rcases hw with rfl | hw
        · exact G.irrefl
        · exact hnadjM w (Finset.mem_of_mem_erase hw)
      · rcases hw with rfl | hw
        · exact fun hadj => hnadjM v (Finset.mem_of_mem_erase hv) hadj.symm
        · exact hV.pit.1 v (Finset.mem_of_mem_erase hv) w (Finset.mem_of_mem_erase hw)
    · intro v hv w hw hvw
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hv hw
      rcases hv with rfl | hv
      · rcases hw with rfl | hw
        · rfl
        · exfalso
          have hyw : y = w := hV.pit.2 (Finset.mem_coe.mpr hyM)
            (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hw)) (by rw [← hpartx]; exact hvw)
          exact (Finset.mem_erase.mp hw).1 hyw.symm
      · rcases hw with rfl | hw
        · exfalso
          have hyv : y = v := hV.pit.2 (Finset.mem_coe.mpr hyM)
            (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hv)) (by rw [← hpartx]; exact hvw.symm)
          exact (Finset.mem_erase.mp hv).1 hyv.symm
        · exact hV.pit.2 (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hv))
            (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hw)) hvw
    · intro v hv
      rw [Finset.mem_insert] at hv
      rcases hv with rfl | hv
      · exact ha
      · exact hV.miss v (Finset.mem_of_mem_erase hv)
    · intro i hi
      have h := hi
      rw [List.length_take] at h
      have hij : i ≤ j := by omega
      have htake : (xs.take (j + 1)).take i = xs.take i := by
        rw [List.take_take, min_eq_left (by omega : i ≤ j + 1)]
      rw [List.getElem_take, htake, hclassesEq i hij, hTsetEq i hij]
      exact hV.chain i (by omega)
    · intro i hi
      have h := hi
      rw [List.length_take] at h
      rw [List.getElem_take, hleavesEq i (by omega)]
      exact hV.nonempty i (by omega)
  -- The witness index for the lexicographic decrease.
  have hjcard : j < Fintype.card ι + 1 := by
    have hVt : Valid G part a M (xs.take (xs.length - 1)) := valid_take G part hV _
    have hall : ∀ k (hk : k < (xs.take (xs.length - 1)).length),
        (leaves G M (xs.take (xs.length - 1))[k]).Nonempty := by
      intro k hk
      have h := hk
      rw [List.length_take] at h
      rw [List.getElem_take]
      exact hV.nonempty k (by omega)
    have h1 := length_le_card G part hVt hall
    rw [List.length_take] at h1
    have h2 := card_lt_of_valid G part hV
    omega
  -- Reading off a coordinate of the signature.
  have hvecT : ∀ (N : Finset V) (ys : List V) (m : Fin (Fintype.card ι + 1))
      (h : (m : ℕ) < ys.length), vec ι G N ys m = (leaves G N (ys[(m : ℕ)]'h)).card := by
    intro N ys m h
    simp only [vec, Pi.toLex_apply]
    split_ifs
    rfl
  refine ⟨insert xs[xs.length - 1] (M.erase y), xs.take (j + 1), hV', ?_, ?_⟩
  · -- `<` on `Lex (Fin k → ℕ)` is `Pi.Lex (· < ·) (· < ·)`, i.e. definitionally
    -- `∃ i, (∀ j, j < i → f j = g j) ∧ f i < g i`.
    show Pi.Lex (· < ·) (· < ·) _ _
    refine ⟨⟨j, hjcard⟩, ?_, ?_⟩
    · intro k hk
      have hkj : (k : ℕ) < j := hk
      have h1 : (k : ℕ) < (xs.take (j + 1)).length := by rw [List.length_take]; omega
      have h2 : (k : ℕ) < xs.length := by omega
      have e : (xs.take (j + 1))[(k : ℕ)]'h1 = xs[(k : ℕ)]'h2 := List.getElem_take
      have eL : leaves G (insert xs[xs.length - 1] (M.erase y)) ((xs.take (j + 1))[(k : ℕ)]'h1)
          = leaves G M (xs[(k : ℕ)]'h2) := by rw [e]; exact hleavesEq (k : ℕ) hkj
      rw [hvecT _ _ k h1, hvecT _ _ k h2, eL]
    · have h1 : j < (xs.take (j + 1)).length := by rw [List.length_take]; omega
      have e : (xs.take (j + 1))[j]'h1 = xs[j]'hjt := List.getElem_take
      have eL : leaves G (insert xs[xs.length - 1] (M.erase y)) ((xs.take (j + 1))[j]'h1)
          = (leaves G M (xs[j]'hjt)).erase y := by rw [e]; exact hleavesM' j le_rfl
      have hlhs : vec ι G (insert xs[xs.length - 1] (M.erase y)) (xs.take (j + 1)) ⟨j, hjcard⟩
          = ((leaves G M (xs[j]'hjt)).erase y).card :=
        (hvecT _ _ ⟨j, hjcard⟩ h1).trans (congrArg Finset.card eL)
      have hrhs : vec ι G M xs ⟨j, hjcard⟩ = (leaves G M (xs[j]'hjt)).card :=
        hvecT _ _ ⟨j, hjcard⟩ hjt
      have hpos : 0 < (leaves G M (xs[j]'hjt)).card := Finset.card_pos.mpr ⟨y, hyc⟩
      rw [hlhs, hrhs, Finset.card_erase_of_mem hyc]
      omega
  · rw [Finset.image_insert, hpartx, ← Finset.image_insert, Finset.insert_erase hyM]

end Erdos1078
