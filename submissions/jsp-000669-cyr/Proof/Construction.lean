import Proof.Defs

/-!
# Erdős problem #812 — the Burr–Erdős–Faudree–Schelp construction

Starting from an `(m, n)`-good colouring `G` of `K_N` containing a red `K_{m-2}` with
vertices `u 0, …, u (m-3)`, we build an `(m, n+1)`-good colouring of `K_{N + 2m - 3}`.

The new vertex set is `Fin N ⊕ (Fin (m-2) ⊕ Fin (m-1))`:

* `Sum.inl a` is an old vertex;
* `Sum.inr (Sum.inl i)` is the duplicate `v i` of `u i` (blue to `u i`, coloured like `u i`
  towards every other old vertex, red to the other duplicates);
* `Sum.inr (Sum.inr j)` is a new vertex `x j` (red to the other `x`'s, blue to every old
  vertex outside the range of `u`, red to `u i` iff `j ≤ i`, red to `v i` iff `i < j`).
-/

namespace Erdos812

open SimpleGraph

section Construction

variable {N m n : ℕ}

/-- The vertex type of the extended colouring: the old vertices, the `m-2` duplicates and
the `m-1` new vertices. -/
abbrev Vtx (N m : ℕ) : Type := Fin N ⊕ (Fin (m - 2) ⊕ Fin (m - 1))

/-- Membership of an old vertex in the "old part" of a finset of extended vertices. -/
theorem mem_toLeft_iff {s : Finset (Vtx N m)} {a : Fin N} :
    a ∈ s.toLeft ↔ (Sum.inl a : Vtx N m) ∈ s := Finset.mem_toLeft

/-- Membership of a duplicate index in the "duplicate part" of a finset of extended vertices. -/
theorem mem_V_iff {s : Finset (Vtx N m)} {i : Fin (m - 2)} :
    i ∈ s.toRight.toLeft ↔ (Sum.inr (Sum.inl i) : Vtx N m) ∈ s := by
  rw [Finset.mem_toLeft, Finset.mem_toRight]

/-- Membership of a new-vertex index in the "new part" of a finset of extended vertices. -/
theorem mem_X_iff {s : Finset (Vtx N m)} {j : Fin (m - 1)} :
    j ∈ s.toRight.toRight ↔ (Sum.inr (Sum.inr j) : Vtx N m) ∈ s := by
  rw [Finset.mem_toRight, Finset.mem_toRight]

/-- The red relation of the extended colouring. -/
def redRel (G : SimpleGraph (Fin N)) (u : Fin (m - 2) → Fin N) : Vtx N m → Vtx N m → Prop
  | .inl a, .inl b => G.Adj a b
  | .inl a, .inr (.inl i) => a ≠ u i ∧ G.Adj a (u i)
  | .inr (.inl i), .inl a => a ≠ u i ∧ G.Adj a (u i)
  | .inr (.inl i), .inr (.inl i') => i ≠ i'
  | .inl a, .inr (.inr j) => ∃ i, a = u i ∧ (j : ℕ) ≤ (i : ℕ)
  | .inr (.inr j), .inl a => ∃ i, a = u i ∧ (j : ℕ) ≤ (i : ℕ)
  | .inr (.inl i), .inr (.inr j) => (i : ℕ) < (j : ℕ)
  | .inr (.inr j), .inr (.inl i) => (i : ℕ) < (j : ℕ)
  | .inr (.inr j), .inr (.inr j') => j ≠ j'

/-- The extended colouring of the complete graph on `Vtx N m`. -/
def extend (G : SimpleGraph (Fin N)) (u : Fin (m - 2) → Fin N) : SimpleGraph (Vtx N m) where
  Adj := redRel G u
  symm := ⟨by
    rintro (a | i | j) (b | i' | j') h <;>
      first
        | exact h
        | exact Ne.symm h
        | exact G.adj_symm h⟩
  loopless := ⟨by
    rintro (a | i | j) h
    · exact G.irrefl h
    · exact h rfl
    · exact h rfl⟩

variable (G : SimpleGraph (Fin N)) (u : Fin (m - 2) → Fin N)

/-- Two old vertices are red iff they were red in `G`. -/
@[simp] theorem extend_adj_oo (a b : Fin N) :
    (extend G u).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b := Iff.rfl

/-- An old vertex is red to `v i` iff it differs from `u i` and is red to `u i`. -/
@[simp] theorem extend_adj_ov (a : Fin N) (i : Fin (m - 2)) :
    (extend G u).Adj (Sum.inl a) (Sum.inr (Sum.inl i)) ↔ a ≠ u i ∧ G.Adj a (u i) := Iff.rfl

/-- `v i` is red to an old vertex iff that vertex differs from `u i` and is red to `u i`. -/
@[simp] theorem extend_adj_vo (i : Fin (m - 2)) (a : Fin N) :
    (extend G u).Adj (Sum.inr (Sum.inl i)) (Sum.inl a) ↔ a ≠ u i ∧ G.Adj a (u i) := Iff.rfl

/-- Distinct duplicates are red to each other. -/
@[simp] theorem extend_adj_vv (i i' : Fin (m - 2)) :
    (extend G u).Adj (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl i')) ↔ i ≠ i' := Iff.rfl

/-- An old vertex is red to `x j` iff it is some `u i` with `j ≤ i`. -/
@[simp] theorem extend_adj_ox (a : Fin N) (j : Fin (m - 1)) :
    (extend G u).Adj (Sum.inl a) (Sum.inr (Sum.inr j)) ↔ ∃ i, a = u i ∧ (j : ℕ) ≤ (i : ℕ) :=
  Iff.rfl

/-- `x j` is red to an old vertex iff that vertex is some `u i` with `j ≤ i`. -/
@[simp] theorem extend_adj_xo (j : Fin (m - 1)) (a : Fin N) :
    (extend G u).Adj (Sum.inr (Sum.inr j)) (Sum.inl a) ↔ ∃ i, a = u i ∧ (j : ℕ) ≤ (i : ℕ) :=
  Iff.rfl

/-- `v i` is red to `x j` iff `i < j`. -/
@[simp] theorem extend_adj_vx (i : Fin (m - 2)) (j : Fin (m - 1)) :
    (extend G u).Adj (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)) ↔ (i : ℕ) < (j : ℕ) := Iff.rfl

/-- `x j` is red to `v i` iff `i < j`. -/
@[simp] theorem extend_adj_xv (j : Fin (m - 1)) (i : Fin (m - 2)) :
    (extend G u).Adj (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inl i)) ↔ (i : ℕ) < (j : ℕ) := Iff.rfl

/-- Distinct new vertices are red to each other. -/
@[simp] theorem extend_adj_xx (j j' : Fin (m - 1)) :
    (extend G u).Adj (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inr j')) ↔ j ≠ j' := Iff.rfl

/-- **No red `K_m`**: the extended colouring inherits red clique-freeness. -/
theorem extend_cliqueFree_red (hm : 2 ≤ m) (hG : G.CliqueFree m)
    (hu : Function.Injective u) (hured : ∀ i j, i ≠ j → G.Adj (u i) (u j)) :
    (extend G u).CliqueFree m := by
  classical
  intro s hs
  have hadj : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (extend G u).Adj x y := fun x hx y hy hxy =>
    hs.1 (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  have hc2 : s.toLeft.card + s.toRight.card = s.card := Finset.card_toLeft_add_card_toRight
  have hc1 : s.toRight.toLeft.card + s.toRight.toRight.card = s.toRight.card :=
    Finset.card_toLeft_add_card_toRight
  have hcard : s.card = m := hs.2
  rcases Finset.eq_empty_or_nonempty s.toRight.toRight with hX | hX
  · -- No new vertex is used: replace each `v i` by `u i`.
    have hXcard : s.toRight.toRight.card = 0 := by rw [hX]; rfl
    have hdisj : Disjoint s.toLeft (s.toRight.toLeft.image u) := by
      rw [Finset.disjoint_left]
      intro a haO haU
      simp only [Finset.mem_image] at haU
      obtain ⟨i, hiV, rfl⟩ := haU
      have h1 : (Sum.inl (u i) : Vtx N m) ∈ s := mem_toLeft_iff.mp haO
      have h2 : (Sum.inr (Sum.inl i) : Vtx N m) ∈ s := mem_V_iff.mp hiV
      have h3 := hadj _ h1 _ h2 (by simp)
      rw [extend_adj_ov] at h3
      exact h3.1 rfl
    have htcard : (s.toLeft ∪ s.toRight.toLeft.image u).card = m := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hu]
      omega
    have htclique : G.IsClique ((s.toLeft ∪ s.toRight.toLeft.image u : Finset (Fin N)) :
        Set (Fin N)) := by
      intro a ha b hb hab
      simp only [Finset.coe_union, Set.mem_union, Finset.coe_image, Set.mem_image,
        Finset.mem_coe] at ha hb
      rcases ha with ha | ⟨i, hiV, rfl⟩ <;> rcases hb with hb | ⟨i', hi'V, rfl⟩
      · exact hadj _ (mem_toLeft_iff.mp ha) _ (mem_toLeft_iff.mp hb) (by simpa using hab)
      · have h3 := hadj _ (mem_toLeft_iff.mp ha) _ (mem_V_iff.mp hi'V) (by simp)
        rw [extend_adj_ov] at h3
        exact h3.2
      · have h3 := hadj _ (mem_toLeft_iff.mp hb) _ (mem_V_iff.mp hiV) (by simp)
        rw [extend_adj_ov] at h3
        exact h3.2.symm
      · exact hured i i' (fun h => hab (by rw [h]))
    have := card_lt_of_cliqueFree hG htclique
    omega
  · -- Some new vertex is used: count the three parts separately.
    obtain ⟨k, hkmem⟩ : ∃ k, k = s.toRight.toRight.min' hX := ⟨_, rfl⟩
    obtain ⟨l, hlmem⟩ : ∃ l, l = s.toRight.toRight.max' hX := ⟨_, rfl⟩
    have hk : k ∈ s.toRight.toRight := by rw [hkmem]; exact Finset.min'_mem _ _
    have hl : l ∈ s.toRight.toRight := by rw [hlmem]; exact Finset.max'_mem _ _
    have hkl : (k : ℕ) ≤ (l : ℕ) := by
      rw [hkmem, hlmem]; exact Finset.min'_le_max' _ hX
    have hks : (Sum.inr (Sum.inr k) : Vtx N m) ∈ s := mem_X_iff.mp hk
    have hls : (Sum.inr (Sum.inr l) : Vtx N m) ∈ s := mem_X_iff.mp hl
    -- the new vertices used lie between `k` and `l`
    have hsXcard : s.toRight.toRight.card ≤ (l : ℕ) - (k : ℕ) + 1 := by
      have hsub : s.toRight.toRight.image Fin.val ⊆ Finset.Icc (k : ℕ) (l : ℕ) := by
        intro y hy
        simp only [Finset.mem_image] at hy
        obtain ⟨j, hj, rfl⟩ := hy
        simp only [Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · rw [hkmem]; exact Finset.min'_le _ j hj
        · rw [hlmem]; exact Finset.le_max' _ j hj
      have h4 := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Icc] at h4
      omega
    -- the duplicates used have index `< k`
    have hsVcard : s.toRight.toLeft.card ≤ (k : ℕ) := by
      have hsub : s.toRight.toLeft.image Fin.val ⊆ Finset.range (k : ℕ) := by
        intro y hy
        simp only [Finset.mem_image] at hy
        obtain ⟨i, hi, rfl⟩ := hy
        have h3 := hadj _ (mem_V_iff.mp hi) _ hks (by simp)
        rw [extend_adj_vx] at h3
        simpa using h3
      have h4 := Finset.card_le_card hsub
      rwa [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_range] at h4
    -- the old vertices used are among the `u i` with `i ≥ l`
    have hOu : ∀ a ∈ s.toLeft, ∃ i, a = u i ∧ (l : ℕ) ≤ (i : ℕ) := by
      intro a ha
      have h3 := hadj _ (mem_toLeft_iff.mp ha) _ hls (by simp)
      rwa [extend_adj_ox] at h3
    have hOsub : s.toLeft ⊆ (Finset.univ.filter fun i : Fin (m - 2) => u i ∈ s.toLeft).image u := by
      intro a ha
      obtain ⟨i, rfl, _⟩ := hOu a ha
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, ha, rfl⟩
    have hsOcard : s.toLeft.card ≤ (m - 2) - (l : ℕ) := by
      have hsub : (Finset.univ.filter fun i : Fin (m - 2) => u i ∈ s.toLeft).image Fin.val
          ⊆ Finset.Ico (l : ℕ) (m - 2) := by
        intro y hy
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        obtain ⟨i, hi, rfl⟩ := hy
        obtain ⟨i', hi', hle⟩ := hOu _ hi
        have : i = i' := hu hi'
        subst this
        simp only [Finset.mem_Ico]
        exact ⟨hle, i.isLt⟩
      have h4 := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Ico] at h4
      exact le_trans (le_trans (Finset.card_le_card hOsub) Finset.card_image_le) h4
    have hlt : (l : ℕ) < m - 1 := l.isLt
    omega

/-- A blue clique of the extended colouring which avoids the new vertices has at most `n`
vertices, and can have `n` vertices only if it contains a pair `u i`, `v i`. -/
theorem extend_blue_no_x (hG : Gᶜ.CliqueFree n) (t : Finset (Vtx N m))
    (ht : (extend G u)ᶜ.IsClique (t : Set (Vtx N m)))
    (hx : ∀ j : Fin (m - 1), (Sum.inr (Sum.inr j) : Vtx N m) ∉ t) :
    t.card < n ∨ (t.card ≤ n ∧ ∃ i : Fin (m - 2),
      (Sum.inr (Sum.inl i) : Vtx N m) ∈ t ∧ (Sum.inl (u i) : Vtx N m) ∈ t) := by
  classical
  have hblue : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ (extend G u).Adj x y := by
    intro x hx' y hy hxy
    have := ht (Finset.mem_coe.mpr hx') (Finset.mem_coe.mpr hy) hxy
    rw [SimpleGraph.compl_adj] at this
    exact this.2
  have hc2 : t.toLeft.card + t.toRight.card = t.card := Finset.card_toLeft_add_card_toRight
  have hc1 : t.toRight.toLeft.card + t.toRight.toRight.card = t.toRight.card :=
    Finset.card_toLeft_add_card_toRight
  have hXcard : t.toRight.toRight.card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro j hj
    exact hx j (mem_X_iff.mp hj)
  -- the old part is a blue clique of `G`
  have hOclique : Gᶜ.IsClique ((t.toLeft : Finset (Fin N)) : Set (Fin N)) := by
    intro a ha b hb hab
    have h3 := hblue _ (mem_toLeft_iff.mp (Finset.mem_coe.mp ha)) _
      (mem_toLeft_iff.mp (Finset.mem_coe.mp hb)) (by simpa using hab)
    rw [extend_adj_oo] at h3
    exact SimpleGraph.compl_adj _ _ _ |>.mpr ⟨hab, h3⟩
  have hOlt : t.toLeft.card < n := card_lt_of_cliqueFree hG hOclique
  -- at most one duplicate is used
  have hV1 : t.toRight.toLeft.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi i' hi'
    by_contra hne
    have h3 := hblue _ (mem_V_iff.mp hi) _ (mem_V_iff.mp hi') (by simpa using hne)
    rw [extend_adj_vv] at h3
    exact h3 hne
  rcases Finset.eq_empty_or_nonempty t.toRight.toLeft with hV | ⟨i, hi⟩
  · left
    rw [hV] at hc1
    simp only [Finset.card_empty] at hc1
    omega
  · have hVcard : t.toRight.toLeft.card = 1 := by
      have := Finset.card_pos.mpr ⟨i, hi⟩
      omega
    have hit : (Sum.inr (Sum.inl i) : Vtx N m) ∈ t := mem_V_iff.mp hi
    by_cases hui : (Sum.inl (u i) : Vtx N m) ∈ t
    · right
      exact ⟨by omega, i, hit, hui⟩
    · left
      have hnotmem : u i ∉ t.toLeft := fun h => hui (mem_toLeft_iff.mp h)
      have hins : Gᶜ.IsClique ((insert (u i) t.toLeft : Finset (Fin N)) : Set (Fin N)) := by
        rw [Finset.coe_insert]
        refine hOclique.insert ?_
        intro b hb hne
        have hbt : (Sum.inl b : Vtx N m) ∈ t := mem_toLeft_iff.mp (Finset.mem_coe.mp hb)
        have h3 := hblue _ hbt _ hit (by simp)
        rw [extend_adj_ov] at h3
        simp only [not_and] at h3
        have hbne : b ≠ u i := fun h => hnotmem (h ▸ Finset.mem_coe.mp hb)
        exact SimpleGraph.compl_adj _ _ _ |>.mpr ⟨Ne.symm hbne, fun hadj => h3 hbne hadj.symm⟩
      have := card_lt_of_cliqueFree hG hins
      rw [Finset.card_insert_of_notMem hnotmem] at this
      omega

/-- **No blue `K_{n+1}`**: the extended colouring has blue clique number at most `n`. -/
theorem extend_cliqueFree_blue (hG : Gᶜ.CliqueFree n) :
    (extend G u)ᶜ.CliqueFree (n + 1) := by
  classical
  intro s hs
  have hblue : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ (extend G u).Adj x y := by
    intro x hx y hy hxy
    have := hs.1 (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
    rw [SimpleGraph.compl_adj] at this
    exact this.2
  by_cases hnox : ∀ j : Fin (m - 1), (Sum.inr (Sum.inr j) : Vtx N m) ∉ s
  · rcases extend_blue_no_x G u hG s hs.1 hnox with h | ⟨h, -⟩ <;> rw [hs.2] at h <;> omega
  · simp only [not_forall, not_not] at hnox
    obtain ⟨j, hjs⟩ := hnox
    set t := s.erase (Sum.inr (Sum.inr j) : Vtx N m) with hts
    have htsub : t ⊆ s := Finset.erase_subset _ _
    have htclique : (extend G u)ᶜ.IsClique ((t : Finset (Vtx N m)) : Set (Vtx N m)) :=
      hs.1.subset (Finset.coe_subset.mpr htsub)
    have htcard : t.card = n := by
      rw [hts, Finset.card_erase_of_mem hjs, hs.2]
      omega
    have hnox' : ∀ j' : Fin (m - 1), (Sum.inr (Sum.inr j') : Vtx N m) ∉ t := by
      intro j' hj'
      have hne : (Sum.inr (Sum.inr j') : Vtx N m) ≠ Sum.inr (Sum.inr j) :=
        Finset.ne_of_mem_erase hj'
      have hmem : (Sum.inr (Sum.inr j') : Vtx N m) ∈ s := Finset.mem_of_mem_erase hj'
      have h3 := hblue _ hmem _ hjs hne
      rw [extend_adj_xx] at h3
      exact h3 (by simpa using hne)
    rcases extend_blue_no_x G u hG t htclique hnox' with h | ⟨-, i, hiv, hiu⟩
    · omega
    · have hivs : (Sum.inr (Sum.inl i) : Vtx N m) ∈ s := htsub hiv
      have hius : (Sum.inl (u i) : Vtx N m) ∈ s := htsub hiu
      have h1 := hblue _ hius _ hjs (by simp)
      have h2 := hblue _ hivs _ hjs (by simp)
      rw [extend_adj_ox] at h1
      rw [extend_adj_vx] at h2
      have h1' : ¬ ((j : ℕ) ≤ (i : ℕ)) := fun hle => h1 ⟨i, rfl, hle⟩
      omega

/-- **Theorem 1 of BEFS 1989 (construction step).**  From an `(m, n)`-good colouring of `K_N`
containing a red `K_{m-2}` one builds an `(m, n+1)`-good colouring of `K_{N + 2m - 3}`. -/
theorem exists_good_succ (hm : 2 ≤ m) (hG : IsGood G m n) (hu : Function.Injective u)
    (hured : ∀ i j, i ≠ j → G.Adj (u i) (u j)) :
    ∃ G' : SimpleGraph (Fin (N + (2 * m - 3))), IsGood G' m (n + 1) := by
  have hgood : IsGood (extend G u) m (n + 1) :=
    ⟨extend_cliqueFree_red G u hm hG.1 hu hured, extend_cliqueFree_blue G u hG.2⟩
  have hEq : N + ((m - 2) + (m - 1)) = N + (2 * m - 3) := by omega
  let E : Vtx N m ≃ Fin (N + ((m - 2) + (m - 1))) :=
    (Equiv.sumCongr (Equiv.refl (Fin N)) finSumFinEquiv).trans finSumFinEquiv
  rw [← hEq]
  exact ⟨(extend G u).comap E.symm.toEmbedding, isGood_comap _ hgood⟩

end Construction

end Erdos812
