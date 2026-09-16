import Mathlib
import JSP895.External.Erdos207.Basic

/-!
# Erdős Problem 1076 (JSP-000895): the locally sparse extremal problem

For `k ≥ 4` let `𝓕_{≤k}` be the family of all three-uniform hypergraphs with `j` vertices
and `j - 2` edges for some `4 ≤ j ≤ k`.  Write `exLe k n` for the largest number of
triples of a three-uniform hypergraph on `n` vertices containing no member of `𝓕_{≤k}`,
i.e. in which no `j - 2` triples span at most `j` vertices for every `4 ≤ j ≤ k`.
This is the "locally sparse" reading of Problem 1076, the one proved by Bohman–Warnke
and Glock–Kühn–Lo–Osthus and marked as proved on erdosproblems.com; the literal
per-`k` reading is false already for `k = 5` (Glock), as formalized in plby/lean-proofs `Erdos1076.not_erdos_1076`.

This file proves the elementary upper bound `3 * exLe k n ≤ n.choose 2` (each pair of
vertices lies in at most one triple when no two triples span four vertices) and the
transport of a locally sparse Steiner triple system from `Fin m` to `Fin n` for `m ≤ n`.
The lower bound itself comes from the high-girth Steiner triple systems of
Kwan–Sah–Sawhney–Simkin (`Erdos207.erdos_207`) in `Assembly.lean`.
-/

open Finset

namespace Erdos1076Sparse

open Erdos207 (verticesOn TripleOn TripleSystemOn TripleSystem)

/-- `FkFree k G` means that no `k - 2` triples of `G` span at most `k` vertices, i.e. `G`
contains no member of the family `𝓕_k` of three-uniform hypergraphs with `k` vertices and
`k - 2` edges (isolated vertices may be added to a configuration spanning fewer vertices).
This is the same definition as `Erdos1076.FkFree` in plby/lean-proofs. -/
def FkFree {V : Type*} [DecidableEq V] (k : ℕ) (G : TripleSystemOn V) : Prop :=
  ∀ C : TripleSystemOn V, C ⊆ G → C.card = k - 2 → k < (verticesOn C).card

/-- `FamilyFree k G`: `G` contains no configuration of `j - 2` triples on at most `j`
vertices for any `4 ≤ j ≤ k`, i.e. no member of `𝓕_{≤k}`. -/
def FamilyFree {V : Type*} [DecidableEq V] (k : ℕ) (G : TripleSystemOn V) : Prop :=
  ∀ j : ℕ, 4 ≤ j → j ≤ k → FkFree j G

/-- The extremal number `ex₃(n, 𝓕_{≤k})` as a finite maximum over all three-uniform
hypergraphs on `Fin n`. -/
noncomputable def exLe (k n : ℕ) : ℕ := by
  classical
  exact (Finset.univ : Finset (TripleSystem n)).sup fun G ↦
    if FamilyFree k G then G.card else 0

lemma card_le_exLe {k n : ℕ} {G : TripleSystem n} (hG : FamilyFree k G) :
    G.card ≤ exLe k n := by
  classical
  unfold exLe
  have hs := Finset.le_sup
    (s := (Finset.univ : Finset (TripleSystem n)))
    (f := fun H ↦ if FamilyFree k H then H.card else 0)
    (Finset.mem_univ G)
  simpa [hG] using hs

lemma exLe_le {k n m : ℕ} (h : ∀ G : TripleSystem n, FamilyFree k G → G.card ≤ m) :
    exLe k n ≤ m := by
  classical
  unfold exLe
  apply Finset.sup_le
  intro G _
  split_ifs with hG
  · exact h G hG
  · exact Nat.zero_le _

/-! ## The upper bound: no two triples share a pair -/

/-- The three pairs carried by a triple. -/
def pairs {V : Type*} [DecidableEq V] (T : TripleOn V) : Finset (Sym2 V) :=
  T.1.offDiag.image Sym2.mk.uncurry

lemma mem_pairs {V : Type*} [DecidableEq V] {T : TripleOn V} {u v : V} :
    s(u, v) ∈ pairs T ↔ u ∈ T.1 ∧ v ∈ T.1 ∧ u ≠ v := by
  simp [pairs, Prod.ext_iff, eq_comm]
  aesop

lemma card_pairs {V : Type*} [DecidableEq V] (T : TripleOn V) : (pairs T).card = 3 := by
  rw [pairs, Sym2.card_image_offDiag, T.2]
  decide

lemma pairs_subset_diag {V : Type*} [DecidableEq V] [Fintype V] (T : TripleOn V) :
    pairs T ⊆ (Finset.univ : Finset V).offDiag.image Sym2.mk.uncurry := by
  intro e he
  rw [pairs, mem_image] at he
  obtain ⟨p, hp, rfl⟩ := he
  rw [mem_offDiag] at hp
  exact mem_image.mpr ⟨p, mem_offDiag.mpr ⟨mem_univ _, mem_univ _, hp.2.2⟩, rfl⟩

/-- Two distinct triples of a `4`-free system share at most one vertex, hence no pair. -/
lemma pairs_disjoint_of_fkFree_four {V : Type*} [DecidableEq V] {G : TripleSystemOn V}
    (hG : FkFree 4 G) {S T : TripleOn V} (hS : S ∈ G) (hT : T ∈ G) (hST : S ≠ T) :
    Disjoint (pairs S) (pairs T) := by
  rw [Finset.disjoint_left]
  intro e heS heT
  induction e using Sym2.ind with
  | h u v =>
    rw [mem_pairs] at heS heT
    have hC : ({S, T} : TripleSystemOn V) ⊆ G := by
      intro X hX
      rcases mem_insert.mp hX with rfl | hX
      · exact hS
      · rw [mem_singleton] at hX
        subst hX
        exact hT
    have hcard : ({S, T} : TripleSystemOn V).card = 4 - 2 := by
      rw [card_pair hST]
    have h4 := hG {S, T} hC hcard
    -- the vertex span of `{S, T}` is `S.1 ∪ T.1`, which has at most `3 + 3 - 2 = 4` elements
    have hspan : verticesOn ({S, T} : TripleSystemOn V) = S.1 ∪ T.1 := by
      unfold verticesOn
      rw [biUnion_insert, singleton_biUnion]
    rw [hspan] at h4
    have hsub : ({u, v} : Finset V) ⊆ S.1 ∩ T.1 := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact mem_inter.mpr ⟨heS.1, heT.1⟩
      · rw [mem_singleton] at hx
        subst hx
        exact mem_inter.mpr ⟨heS.2.1, heT.2.1⟩
    have hinter : 2 ≤ (S.1 ∩ T.1).card := by
      have := card_le_card hsub
      rwa [card_pair heS.2.2] at this
    have hunion := card_union_add_card_inter S.1 T.1
    rw [S.2, T.2] at hunion
    omega

/-- In a `4`-free system, the triples carry pairwise disjoint pair sets, so three times
the number of triples is at most the number of pairs of vertices. -/
theorem three_mul_card_le_choose {n : ℕ} {G : TripleSystem n} (hG : FkFree 4 G) :
    3 * G.card ≤ n.choose 2 := by
  classical
  have hdisj : (↑G : Set (TripleOn (Fin n))).PairwiseDisjoint pairs := by
    intro S hS T hT hST
    exact pairs_disjoint_of_fkFree_four hG hS hT hST
  have hcardU : (G.biUnion pairs).card = ∑ T ∈ G, (pairs T).card :=
    card_biUnion hdisj
  have hsum : ∑ T ∈ G, (pairs T).card = 3 * G.card := by
    rw [Finset.sum_congr rfl fun T _ => card_pairs T]
    simp [mul_comm]
  have hsub : G.biUnion pairs ⊆ (Finset.univ : Finset (Fin n)).offDiag.image Sym2.mk.uncurry := by
    intro e he
    rw [mem_biUnion] at he
    obtain ⟨T, -, heT⟩ := he
    exact pairs_subset_diag T heT
  have hall : ((Finset.univ : Finset (Fin n)).offDiag.image Sym2.mk.uncurry).card = n.choose 2 := by
    rw [Sym2.card_image_offDiag, card_univ, Fintype.card_fin]
  calc 3 * G.card = (G.biUnion pairs).card := by rw [hcardU, hsum]
    _ ≤ _ := card_le_card hsub
    _ = n.choose 2 := hall

theorem three_mul_exLe_le_choose (k n : ℕ) (hk : 4 ≤ k) : 3 * exLe k n ≤ n.choose 2 := by
  have h : ∀ G : TripleSystem n, FamilyFree k G → 3 * G.card ≤ n.choose 2 :=
    fun G hG => three_mul_card_le_choose (hG 4 le_rfl hk)
  have : exLe k n ≤ n.choose 2 / 3 := by
    apply exLe_le
    intro G hG
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by simpa [mul_comm] using h G hG)
  calc 3 * exLe k n ≤ 3 * (n.choose 2 / 3) := by omega
    _ ≤ n.choose 2 := Nat.mul_div_le _ _

/-! ## Steiner triple systems have exactly `n.choose 2 / 3` triples -/

/-- Every pair of a Steiner triple system lies in some triple, and distinct triples carry
disjoint pair sets; hence `3 * H.card = n.choose 2`. -/
theorem three_mul_card_of_isSteiner {n : ℕ} {H : Erdos207.TripleSystem n}
    (hH : Erdos207.IsSteiner H) : 3 * H.card = n.choose 2 := by
  classical
  have hdisj : (↑H : Set (TripleOn (Fin n))).PairwiseDisjoint pairs := by
    intro S hS T hT hST
    rw [Function.onFun, Finset.disjoint_left]
    intro e heS heT
    induction e using Sym2.ind with
    | h u v =>
      rw [mem_pairs] at heS heT
      obtain ⟨U, -, hU⟩ := hH u v heS.2.2
      have h1 := hU S ⟨hS, heS.1, heS.2.1⟩
      have h2 := hU T ⟨hT, heT.1, heT.2.1⟩
      exact hST (h1.trans h2.symm)
  have hcardU : (H.biUnion pairs).card = ∑ T ∈ H, (pairs T).card := card_biUnion hdisj
  have hsum : ∑ T ∈ H, (pairs T).card = 3 * H.card := by
    rw [Finset.sum_congr rfl fun T _ => card_pairs T]
    simp [mul_comm]
  have heq : H.biUnion pairs = (Finset.univ : Finset (Fin n)).offDiag.image Sym2.mk.uncurry := by
    apply Finset.Subset.antisymm
    · intro e he
      rw [mem_biUnion] at he
      obtain ⟨T, -, heT⟩ := he
      exact pairs_subset_diag T heT
    · intro e he
      rw [mem_image] at he
      obtain ⟨⟨u, v⟩, huv, rfl⟩ := he
      rw [mem_offDiag] at huv
      obtain ⟨T, ⟨hT, huT, hvT⟩, -⟩ := hH u v huv.2.2
      exact mem_biUnion.mpr ⟨T, hT, mem_pairs.mpr ⟨huT, hvT, huv.2.2⟩⟩
  have hall : ((Finset.univ : Finset (Fin n)).offDiag.image Sym2.mk.uncurry).card = n.choose 2 := by
    rw [Sym2.card_image_offDiag, card_univ, Fintype.card_fin]
  rw [← hsum, ← hcardU, heq, hall]

/-! ## Locally sparse systems are family-free -/

theorem familyFree_of_locallySparse {n k : ℕ} {H : Erdos207.TripleSystem n}
    (hH : Erdos207.LocallySparse (k - 2) H) : FamilyFree k H := by
  intro j hj4 hjk C hC hcard
  have h := hH C hC (by omega) (by omega)
  omega

/-! ## Transport along `Fin.castLE` -/

/-- Push a triple on `Fin m` forward to `Fin n` along the inclusion `Fin.castLE`. -/
def castTriple {m n : ℕ} (h : m ≤ n) (T : TripleOn (Fin m)) : TripleOn (Fin n) :=
  ⟨T.1.map (Fin.castLEEmb h), by rw [card_map, T.2]⟩

lemma castTriple_injective {m n : ℕ} (h : m ≤ n) : Function.Injective (castTriple h) := by
  intro S T hST
  apply Subtype.ext
  have := congrArg Subtype.val hST
  simpa [castTriple] using Finset.map_injective (Fin.castLEEmb h) this

/-- Push a triple system on `Fin m` forward to `Fin n`. -/
def castSystem {m n : ℕ} (h : m ≤ n) (H : TripleSystemOn (Fin m)) : TripleSystem n :=
  H.map ⟨castTriple h, castTriple_injective h⟩

lemma card_castSystem {m n : ℕ} (h : m ≤ n) (H : TripleSystemOn (Fin m)) :
    (castSystem h H).card = H.card := card_map _

lemma verticesOn_castSystem {m n : ℕ} (h : m ≤ n) (C : TripleSystemOn (Fin m)) :
    verticesOn (castSystem h C) = (verticesOn C).map (Fin.castLEEmb h) := by
  ext x
  simp only [verticesOn, castSystem, castTriple, mem_biUnion, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨T', ⟨T, hT, rfl⟩, hx⟩
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    exact ⟨y, ⟨T, hT, hy⟩, rfl⟩
  · rintro ⟨y, ⟨T, hT, hy⟩, rfl⟩
    exact ⟨castTriple h T, ⟨T, hT, rfl⟩, mem_map.mpr ⟨y, hy, rfl⟩⟩

/-- A subsystem of a pushed-forward system is the push-forward of a subsystem. -/
lemma exists_preimage_of_subset_castSystem {m n : ℕ} (h : m ≤ n)
    {H : TripleSystemOn (Fin m)} {C : TripleSystem n} (hC : C ⊆ castSystem h H) :
    ∃ D : TripleSystemOn (Fin m), D ⊆ H ∧ castSystem h D = C := by
  classical
  refine ⟨H.filter fun T => castTriple h T ∈ C, filter_subset _ _, ?_⟩
  ext X
  simp only [castSystem, mem_map, mem_filter, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨T, ⟨-, hTC⟩, rfl⟩
    exact hTC
  · intro hX
    obtain ⟨T, hT, rfl⟩ := mem_map.mp (hC hX)
    exact ⟨T, ⟨hT, hX⟩, rfl⟩

theorem familyFree_castSystem {m n k : ℕ} (h : m ≤ n) {H : TripleSystemOn (Fin m)}
    (hH : FamilyFree k H) : FamilyFree k (castSystem h H) := by
  intro j hj4 hjk C hC hcard
  obtain ⟨D, hDH, rfl⟩ := exists_preimage_of_subset_castSystem h hC
  rw [card_castSystem] at hcard
  have := hH j hj4 hjk D hDH hcard
  rwa [verticesOn_castSystem, card_map]

/-! ## Admissible orders are dense -/

/-- Every `n ≥ 3` has an admissible `m ≡ 1, 3 (mod 6)` with `n - 3 ≤ m ≤ n`. -/
lemma exists_admissible_near (n : ℕ) (hn : 3 ≤ n) :
    ∃ m : ℕ, Erdos207.Admissible m ∧ m ≤ n ∧ n ≤ m + 3 := by
  unfold Erdos207.Admissible
  rcases Nat.lt_or_ge (n % 6) 1 with h0 | h0
  · exact ⟨n - 3, by omega, by omega, by omega⟩
  rcases Nat.lt_or_ge (n % 6) 2 with h1 | h1
  · exact ⟨n, by omega, le_rfl, by omega⟩
  rcases Nat.lt_or_ge (n % 6) 3 with h2 | h2
  · exact ⟨n - 1, by omega, by omega, by omega⟩
  rcases Nat.lt_or_ge (n % 6) 4 with h3 | h3
  · exact ⟨n, by omega, le_rfl, by omega⟩
  rcases Nat.lt_or_ge (n % 6) 5 with h4 | h4
  · exact ⟨n - 1, by omega, by omega, by omega⟩
  · exact ⟨n - 2, by omega, by omega, by omega⟩

/-! ## From the two-sided binomial bounds to the asymptotic `n^2 / 6` -/

open Filter Topology in
/-- A sequence squeezed between `(n-3).choose 2 / 3` and `n.choose 2 / 3` is asymptotic to
`n^2 / 6`. -/
theorem tendsto_div_sq_of_choose_bounds {f : ℕ → ℕ} {N₀ : ℕ}
    (hup : ∀ n, 3 * f n ≤ n.choose 2)
    (hlow : ∀ n, N₀ ≤ n → (n - 3).choose 2 ≤ 3 * f n) :
    Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 6)) := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  -- upper comparison sequence `(1 - 1/n) / 6`
  have hU : Tendsto (fun n : ℕ => (1 - 1 / (n : ℝ)) / 6) atTop (𝓝 (1 / 6)) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).div_const 6
    simpa using this
  -- lower comparison sequence `(1 - 3/n) * (1 - 4/n) / 6`
  have hL : Tendsto (fun n : ℕ => (1 - 3 / (n : ℝ)) * (1 - 4 / (n : ℝ)) / 6) atTop
      (𝓝 (1 / 6)) := by
    have h3 : Tendsto (fun n : ℕ => (3 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 3
    have h4 : Tendsto (fun n : ℕ => (4 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 4
    have := (((tendsto_const_nhds (x := (1 : ℝ))).sub h3).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub h4)).div_const 6
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · filter_upwards [eventually_ge_atTop (max N₀ 4)] with n hn
    have hn4 : 4 ≤ n := le_of_max_le_right hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlow' := hlow n (le_of_max_le_left hn)
    have hcast : (((n - 3).choose 2 : ℕ) : ℝ) = ((n : ℝ) - 3) * ((n : ℝ) - 4) / 2 := by
      rw [Nat.cast_choose_two]
      have h1 : ((n - 3 : ℕ) : ℝ) = (n : ℝ) - 3 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [h1]
      ring
    have hle : ((n : ℝ) - 3) * ((n : ℝ) - 4) / 2 ≤ 3 * (f n : ℝ) := by
      rw [← hcast]
      exact_mod_cast hlow'
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have : (1 - 3 / (n : ℝ)) * (1 - 4 / (n : ℝ)) = ((n : ℝ) - 3) * ((n : ℝ) - 4) / (n : ℝ) ^ 2 := by
      field_simp
    rw [this]
    field_simp
    nlinarith [hle]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hup' := hup n
    have hcast : ((n.choose 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ n
    have hle : 3 * (f n : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 := by
      rw [← hcast]
      exact_mod_cast hup'
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 - 1 / (n : ℝ)) = ((n : ℝ) - 1) / (n : ℝ) := by
      field_simp
    rw [this]
    field_simp
    nlinarith [hle]

end Erdos1076Sparse
