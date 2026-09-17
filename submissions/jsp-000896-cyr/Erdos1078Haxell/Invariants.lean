import Erdos1078Haxell.Definitions

/-! Structural consequences of validity. -/

set_option linter.unusedSectionVars false

namespace Erdos1078

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → ι)

theorem leaves_subset (M : Finset V) (x : V) : leaves G M x ⊆ M :=
  Finset.filter_subset _ _

private lemma take_toFinset_subset (xs : List V) (j : ℕ) :
    (xs.take j).toFinset ⊆ xs.toFinset := by
  intro x hx
  rw [List.mem_toFinset] at hx ⊢
  exact List.mem_of_mem_take hx

theorem classes_take_subset (M : Finset V) (a : ι) (xs : List V) (j : ℕ) :
    classes G part M a (xs.take j) ⊆ classes G part M a xs := by
  rw [classes, classes]
  exact Finset.insert_subset_insert _ (Finset.image_subset_image
    (Finset.biUnion_subset_biUnion_of_subset_left _ (take_toFinset_subset xs j)))

theorem Tset_take_subset (M : Finset V) (xs : List V) (j : ℕ) :
    Tset G M (xs.take j) ⊆ Tset G M xs := by
  rw [Tset, Tset]
  exact Finset.union_subset_union (take_toFinset_subset xs j)
    (Finset.biUnion_subset_biUnion_of_subset_left _ (take_toFinset_subset xs j))

/-- The leaves of a centre lie in classes not reached before that centre. -/
theorem leaf_class_not_mem {a : ι} {M : Finset V} {xs : List V} (hV : Valid G part a M xs)
    (j : ℕ) (hj : j < xs.length) {y : V} (hy : y ∈ leaves G M xs[j]) :
    part y ∉ classes G part M a (xs.take j) := by
  rw [leaves, Finset.mem_filter] at hy
  obtain ⟨hyM, hadj⟩ := hy
  intro h
  rw [classes, Finset.mem_insert] at h
  rcases h with h | h
  · exact hV.miss y hyM h
  · obtain ⟨y', hy', hpy'⟩ := Finset.mem_image.mp h
    have hy'M : y' ∈ M := by
      obtain ⟨x, _, hx2⟩ := Finset.mem_biUnion.mp hy'
      exact leaves_subset G M x hx2
    have hyy : y' = y := hV.pit.2 (Finset.mem_coe.mpr hy'M) (Finset.mem_coe.mpr hyM) hpy'
    refine (hV.chain j hj).2 y ?_ hadj.symm
    rw [Tset]
    exact Finset.mem_union_right _ (hyy ▸ hy')

private lemma getElem_mem_take (xs : List V) {i j : ℕ} (hi : i < xs.length) (hij : i < j) :
    xs[i] ∈ xs.take j := by
  have hlen : i < (xs.take j).length := by
    rw [List.length_take]; omega
  have h := List.getElem_mem hlen
  rwa [List.getElem_take] at h

private lemma leaves_disjoint_lt {a : ι} {M : Finset V} {xs : List V} (hV : Valid G part a M xs)
    {i j : ℕ} (hi : i < xs.length) (hj : j < xs.length) (hij : i < j) :
    Disjoint (leaves G M xs[i]) (leaves G M xs[j]) := by
  rw [Finset.disjoint_left]
  intro y hyi hyj
  refine leaf_class_not_mem G part hV j hj hyj ?_
  rw [classes, Finset.mem_insert]
  exact Or.inr (Finset.mem_image_of_mem part
    (Finset.mem_biUnion.mpr ⟨xs[i], List.mem_toFinset.mpr (getElem_mem_take xs hi hij), hyi⟩))

/-- Leaves of different centres are disjoint. -/
theorem leaves_disjoint {a : ι} {M : Finset V} {xs : List V} (hV : Valid G part a M xs)
    {i j : ℕ} (hi : i < xs.length) (hj : j < xs.length) (hij : i ≠ j) :
    Disjoint (leaves G M xs[i]) (leaves G M xs[j]) := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact leaves_disjoint_lt G part hV hi hj h
  · exact (leaves_disjoint_lt G part hV hj hi h).symm

/-- Every constellation vertex lies in a reached class. -/
theorem Tset_subset_classes {a : ι} {M : Finset V} {xs : List V} (hV : Valid G part a M xs) :
    ∀ u ∈ Tset G M xs, part u ∈ classes G part M a xs := by
  intro u hu
  rw [Tset, Finset.mem_union] at hu
  rcases hu with hu | hu
  · rw [List.mem_toFinset, List.mem_iff_getElem] at hu
    obtain ⟨j, hj, rfl⟩ := hu
    exact classes_take_subset G part M a xs j (hV.chain j hj).1
  · rw [classes]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem part hu)

private lemma biUnion_eq_fin (M : Finset V) (xs : List V) :
    xs.toFinset.biUnion (leaves G M) =
      (Finset.univ : Finset (Fin xs.length)).biUnion (fun j => leaves G M xs[j]) := by
  ext y
  simp only [Finset.mem_biUnion, List.mem_toFinset, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    exact ⟨⟨j, hj⟩, hy⟩
  · rintro ⟨j, hy⟩
    exact ⟨xs[j], List.getElem_mem j.isLt, hy⟩

private lemma biUnion_subset_M (M : Finset V) (xs : List V) :
    xs.toFinset.biUnion (leaves G M) ⊆ M := by
  intro y hy
  obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp hy
  exact leaves_subset G M x hx

/-- The number of reached classes is one more than the total number of leaves. -/
theorem card_classes {a : ι} {M : Finset V} {xs : List V} (hV : Valid G part a M xs) :
    (classes G part M a xs).card = 1 + ∑ j : Fin xs.length, (leaves G M xs[j]).card := by
  have hsub := biUnion_subset_M G M xs
  have hanot : a ∉ (xs.toFinset.biUnion (leaves G M)).image part := by
    intro h
    obtain ⟨y, hy, hpy⟩ := Finset.mem_image.mp h
    exact hV.miss y (hsub hy) hpy
  have hinj : Set.InjOn part ↑(xs.toFinset.biUnion (leaves G M)) := by
    intro y hy z hz h
    exact hV.pit.2 (Finset.mem_coe.mpr (hsub (Finset.mem_coe.mp hy)))
      (Finset.mem_coe.mpr (hsub (Finset.mem_coe.mp hz))) h
  rw [classes, Finset.card_insert_of_notMem hanot, Finset.card_image_of_injOn hinj,
    biUnion_eq_fin, Finset.card_biUnion]
  · exact Nat.add_comm _ _
  · intro i _ j _ hij
    exact leaves_disjoint G part hV i.isLt j.isLt (fun h => hij (Fin.ext h))

theorem card_Tset_le (M : Finset V) (xs : List V) :
    (Tset G M xs).card ≤ xs.length + ∑ j : Fin xs.length, (leaves G M xs[j]).card := by
  have h1 : xs.toFinset.card ≤ xs.length := List.toFinset_card_le xs
  have h2 : (xs.toFinset.biUnion (leaves G M)).card
      ≤ ∑ j : Fin xs.length, (leaves G M xs[j]).card := by
    rw [biUnion_eq_fin]
    exact Finset.card_biUnion_le
  rw [Tset]
  exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add h1 h2)

/-- If every centre has a leaf, there are at most `|M|` centres. -/
theorem length_le_card {a : ι} {M : Finset V} {xs : List V} (hV : Valid G part a M xs)
    (hall : ∀ j (hj : j < xs.length), (leaves G M xs[j]).Nonempty) : xs.length ≤ M.card := by
  have key : ((Finset.univ : Finset (Fin xs.length)).biUnion (fun j => leaves G M xs[j])).card
      = ∑ j : Fin xs.length, (leaves G M xs[j]).card :=
    Finset.card_biUnion (fun i _ j _ hij =>
      leaves_disjoint G part hV i.isLt j.isLt (fun h => hij (Fin.ext h)))
  have hle : ((Finset.univ : Finset (Fin xs.length)).biUnion
      (fun j => leaves G M xs[j])).card ≤ M.card :=
    Finset.card_le_card (Finset.biUnion_subset.mpr (fun j _ => leaves_subset G M _))
  have h1 : xs.length ≤ ∑ j : Fin xs.length, (leaves G M xs[j]).card := by
    calc xs.length = ∑ _j : Fin xs.length, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => Finset.card_pos.mpr (hall j j.isLt))
  omega

/-- A partial independent transversal missing `a` has fewer than `|ι|` vertices. -/
theorem card_lt_of_valid {a : ι} {M : Finset V} {xs : List V} (hV : Valid G part a M xs) :
    M.card < Fintype.card ι := by
  have h1 : (M.image part).card = M.card := Finset.card_image_of_injOn hV.pit.2
  have h2 : M.image part ⊆ (Finset.univ : Finset ι).erase a := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_erase.mpr ⟨hV.miss v hv, Finset.mem_univ _⟩
  have h3 : ((Finset.univ : Finset ι).erase a).card = Fintype.card ι - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
  have h4 : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨a⟩
  have h5 := Finset.card_le_card h2
  omega

end Erdos1078
