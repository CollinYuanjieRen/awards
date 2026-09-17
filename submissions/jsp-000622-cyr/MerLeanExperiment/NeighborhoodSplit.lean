import MerLeanExperiment.NeighborhoodPattern
import MerLeanExperiment.GraphSplit

/-! Concrete normalization of a graph about a distinguished vertex. -/
namespace CochromaticTwenty

/-- The neighbor block occupies positions one through `d`. -/
def neighborIndex {n d : ℕ} (hd : d < n) (i : Fin d) : Fin n :=
  ⟨i.val + 1, by omega⟩

/-- The nonneighbor block excludes the center and follows the neighbors. -/
def nonneighborIndex {n d : ℕ} (hd : d < n) (j : Fin (n - d - 1)) : Fin n :=
  ⟨j.val + d + 1, by omega⟩

@[simp] theorem neighborIndex_inj {n d : ℕ} (hd : d < n) (i j : Fin d) :
    neighborIndex hd i = neighborIndex hd j ↔ i = j := by
  simp [neighborIndex, Fin.ext_iff]

@[simp] theorem nonneighborIndex_inj {n d : ℕ} (hd : d < n)
    (i j : Fin (n - d - 1)) :
    nonneighborIndex hd i = nonneighborIndex hd j ↔ i = j := by
  simp [nonneighborIndex, Fin.ext_iff]

/-- All cross-edge choices, extended outside the actual rectangular table. -/
def neighborhoodAssignment {d m : ℕ} (cross : Fin d → Fin m → Bool) : ℕ → Bool :=
  fun k => if hk : k < d * m then
    let ij := (finProdFinEquiv : Fin d × Fin m ≃ Fin (d * m)).symm ⟨k, hk⟩
    cross ij.1 ij.2
  else false

@[simp] theorem neighborhoodAssignment_apply {d m : ℕ}
    (cross : Fin d → Fin m → Bool) (i : Fin d) (j : Fin m) :
    neighborhoodAssignment cross (i.val * m + j.val) = cross i j := by
  have hk : i.val * m + j.val < d * m := by
    calc
      i.val * m + j.val < i.val * m + m := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * m := by simp [Nat.add_mul]
      _ ≤ d * m := Nat.mul_le_mul_right m (by omega)
  unfold neighborhoodAssignment
  rw [dite_eq_left hk]
  have heq : (⟨i.val * m + j.val, hk⟩ : Fin (d * m)) =
      (finProdFinEquiv : Fin d × Fin m ≃ Fin (d * m)) (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [heq, Equiv.symm_apply_apply]

theorem neighborhoodPattern_left {n d : ℕ} (hd : d < n) (left right : ℕ)
    (a : ℕ → Bool) (i j : Fin d) :
    ((neighborhoodPattern n d left right).graph a).Adj
      (neighborIndex hd i) (neighborIndex hd j) ↔ (codeGraph d left).Adj i j := by
  have he : edgeIndex (min i.val j.val) (max i.val j.val) = edgeIndex i.val j.val := by
    simp [edgeIndex]
  simp [GraphPattern.graph, neighborhoodPattern, neighborhoodEdge, neighborIndex,
    EdgeRule.eval, codeGraph, he, Fin.ext_iff]

theorem neighborhoodPattern_right {n d : ℕ} (hd : d < n) (left right : ℕ)
    (a : ℕ → Bool) (i j : Fin (n - d - 1)) :
    ((neighborhoodPattern n d left right).graph a).Adj
      (nonneighborIndex hd i) (nonneighborIndex hd j) ↔
      ((codeGraph (n - d - 1) right)ᶜ).Adj i j := by
  have he : edgeIndex (min i.val j.val) (max i.val j.val) = edgeIndex i.val j.val := by
    simp [edgeIndex]
  simp [GraphPattern.graph, neighborhoodPattern, neighborhoodEdge, nonneighborIndex,
    EdgeRule.eval, codeGraph, Fin.ext_iff,
    SimpleGraph.compl_adj]
  have hs (x : ℕ) : x + d + 1 - d - 1 = x := by omega
  intro hij
  simp [hs, he, hij]

theorem neighborhoodPattern_cross {n d : ℕ} (hd : d < n) (left right : ℕ)
    (a : ℕ → Bool) (i : Fin d) (j : Fin (n - d - 1)) :
    ((neighborhoodPattern n d left right).graph a).Adj
      (neighborIndex hd i) (nonneighborIndex hd j) ↔
      a (i.val * (n - d - 1) + j.val) = true := by
  have hlt : i.val + 1 < j.val + d + 1 := by omega
  have hn : neighborIndex hd i ≠ nonneighborIndex hd j := by
    intro h
    have := congrArg Fin.val h
    simp only [neighborIndex, nonneighborIndex] at this
    omega
  have hsub : j.val + d + 1 - d - 1 = j.val := by omega
  simp [GraphPattern.graph, neighborhoodPattern, neighborhoodEdge, EdgeRule.eval,
    neighborIndex, nonneighborIndex, min_eq_left (Nat.le_of_lt hlt),
    max_eq_right (Nat.le_of_lt hlt), hsub, Fin.ext_iff,
    show ¬ j.val + d + 1 ≤ d by omega, show ¬ d < i.val + 1 by omega]
  omega

theorem neighborhoodPattern_center_left {n d : ℕ} (hd : d < n) (left right : ℕ)
    (a : ℕ → Bool) (i : Fin d) :
    ((neighborhoodPattern n d left right).graph a).Adj
      ⟨0, by omega⟩ (neighborIndex hd i) := by
  simp [GraphPattern.graph, neighborhoodPattern, neighborhoodEdge, EdgeRule.eval,
    neighborIndex, Fin.ext_iff, show i.val + 1 ≤ d by omega]

theorem neighborhoodPattern_center_right {n d : ℕ} (hd : d < n) (left right : ℕ)
    (a : ℕ → Bool) (i : Fin (n - d - 1)) :
    ¬ ((neighborhoodPattern n d left right).graph a).Adj
      ⟨0, by omega⟩ (nonneighborIndex hd i) := by
  simp [GraphPattern.graph, neighborhoodPattern, neighborhoodEdge, EdgeRule.eval,
    nonneighborIndex, Fin.ext_iff, show ¬ i.val + d + 1 ≤ d by omega]


/-- Every vertex is the center, an actual neighbor, or an actual nonneighbor.
The complement-neighbor convention excludes the center automatically. -/
theorem neighborhood_vertex_cases {n : ℕ} (G : SimpleGraph (Fin n)) (v u : Fin n) :
    v = u ∨ (∃ w : G.neighborSet v, w.val = u) ∨
      (∃ w : (Gᶜ).neighborSet v, w.val = u) := by
  classical
  by_cases huv : u = v
  · exact Or.inl huv.symm
  · by_cases ha : G.Adj v u
    · exact Or.inr (Or.inl ⟨⟨u, ha⟩, rfl⟩)
    · right; right
      exact ⟨⟨u, by simp [SimpleGraph.mem_neighborSet, SimpleGraph.compl_adj,
        Ne.symm huv, ha]⟩, rfl⟩

noncomputable def neighborhoodRelabel {n d leftCode rightCode : ℕ}
    (G : SimpleGraph (Fin n)) (v : Fin n) (hd : d < n)
    (eLeft : G.induce (G.neighborSet v) ≃g codeGraph d leftCode)
    (eRight : (G.induce ((Gᶜ).neighborSet v))ᶜ ≃g codeGraph (n-d-1) rightCode)
    (u : Fin n) : Fin n := by
  classical
  exact if huv : u = v then ⟨0, by omega⟩ else
    if ha : G.Adj v u then neighborIndex hd (eLeft ⟨u, ha⟩) else
      nonneighborIndex hd (eRight ⟨u, by
        simp [SimpleGraph.mem_neighborSet, SimpleGraph.compl_adj, Ne.symm huv, ha]⟩)

@[simp] theorem neighborhoodRelabel_center {n d leftCode rightCode : ℕ}
    (G : SimpleGraph (Fin n)) (v : Fin n) (hd : d < n)
    (eLeft : G.induce (G.neighborSet v) ≃g codeGraph d leftCode)
    (eRight : (G.induce ((Gᶜ).neighborSet v))ᶜ ≃g codeGraph (n-d-1) rightCode) :
    neighborhoodRelabel G v hd eLeft eRight v = ⟨0, by omega⟩ := by
  classical
  simp [neighborhoodRelabel]

@[simp] theorem neighborhoodRelabel_left {n d leftCode rightCode : ℕ}
    (G : SimpleGraph (Fin n)) (v : Fin n) (hd : d < n)
    (eLeft : G.induce (G.neighborSet v) ≃g codeGraph d leftCode)
    (eRight : (G.induce ((Gᶜ).neighborSet v))ᶜ ≃g codeGraph (n-d-1) rightCode)
    (u : G.neighborSet v) :
    neighborhoodRelabel G v hd eLeft eRight u.val = neighborIndex hd (eLeft u) := by
  classical
  have ha : G.Adj v u.val := u.property
  have hn : u.val ≠ v := by intro h; rw [h] at ha; exact G.irrefl ha
  simp [neighborhoodRelabel, hn, ha]

@[simp] theorem neighborhoodRelabel_right {n d leftCode rightCode : ℕ}
    (G : SimpleGraph (Fin n)) (v : Fin n) (hd : d < n)
    (eLeft : G.induce (G.neighborSet v) ≃g codeGraph d leftCode)
    (eRight : (G.induce ((Gᶜ).neighborSet v))ᶜ ≃g codeGraph (n-d-1) rightCode)
    (u : (Gᶜ).neighborSet v) :
    neighborhoodRelabel G v hd eLeft eRight u.val = nonneighborIndex hd (eRight u) := by
  classical
  have ha : (Gᶜ).Adj v u.val := u.property
  have hh : v ≠ u.val ∧ ¬ G.Adj v u.val := by simpa using ha
  simp [neighborhoodRelabel, Ne.symm hh.1, hh.2]

theorem neighborhoodRelabel_injective {n d leftCode rightCode : ℕ}
    (G : SimpleGraph (Fin n)) (v : Fin n) (hd : d < n)
    (eLeft : G.induce (G.neighborSet v) ≃g codeGraph d leftCode)
    (eRight : (G.induce ((Gᶜ).neighborSet v))ᶜ ≃g codeGraph (n-d-1) rightCode) :
    Function.Injective (neighborhoodRelabel G v hd eLeft eRight) := by
  intro u w h
  rcases neighborhood_vertex_cases G v u with rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩
  · rcases neighborhood_vertex_cases G v w with rfl | ⟨w, rfl⟩ | ⟨w, rfl⟩
    · rfl
    · have he := congrArg Fin.val h
      simp [neighborIndex] at he
    · have he := congrArg Fin.val h
      simp [nonneighborIndex] at he
  · rcases neighborhood_vertex_cases G v w with rfl | ⟨w, rfl⟩ | ⟨w, rfl⟩
    · have he := congrArg Fin.val h
      simp [neighborIndex] at he
    · have he : eLeft u = eLeft w := by simpa using h
      exact congrArg Subtype.val (eLeft.injective he)
    · have he := congrArg Fin.val h
      simp only [neighborhoodRelabel_left, neighborhoodRelabel_right,
        neighborIndex, nonneighborIndex] at he
      have hu := (eLeft u).isLt
      omega
  · rcases neighborhood_vertex_cases G v w with rfl | ⟨w, rfl⟩ | ⟨w, rfl⟩
    · have he := congrArg Fin.val h
      simp [nonneighborIndex] at he
    · have he := congrArg Fin.val h
      simp only [neighborhoodRelabel_left, neighborhoodRelabel_right,
        neighborIndex, nonneighborIndex] at he
      have hw := (eLeft w).isLt
      omega
    · have he : eRight u = eRight w := by simpa using h
      exact congrArg Subtype.val (eRight.injective he)


theorem neighborhoodRight_adj_iff {n d rightCode : ℕ}
    (G : SimpleGraph (Fin n)) (v : Fin n)
    (eRight : (G.induce ((Gᶜ).neighborSet v))ᶜ ≃g codeGraph (n-d-1) rightCode)
    (u w : (Gᶜ).neighborSet v) :
    ((codeGraph (n-d-1) rightCode)ᶜ).Adj (eRight u) (eRight w) ↔ G.Adj u.val w.val := by
  classical
  have hne : eRight u ≠ eRight w ↔ u ≠ w := by
    constructor
    · intro h he; exact h (congrArg eRight he)
    · intro h he; exact h (eRight.injective he)
  have hr : (codeGraph (n-d-1) rightCode).Adj (eRight u) (eRight w) ↔
      u ≠ w ∧ ¬ G.Adj u.val w.val := by
    simpa using (eRight.map_rel_iff (a := u) (b := w))
  rw [SimpleGraph.compl_adj, hne, hr]
  by_cases h : u = w
  · subst w; simp
  · simp [h]

/-- Normalize an ordinary graph using its actual neighbor and nonneighbor
isomorphisms, retaining every cross-edge value. No normalization premise is used. -/
theorem exists_neighborhoodPattern_iso {n d leftCode rightCode : ℕ}
    (G : SimpleGraph (Fin n)) (v : Fin n) (hd : d < n)
    (eLeft : G.induce (G.neighborSet v) ≃g codeGraph d leftCode)
    (eRight : (G.induce ((Gᶜ).neighborSet v))ᶜ ≃g codeGraph (n-d-1) rightCode) :
    ∃ a : ℕ → Bool, Nonempty (G ≃g (neighborhoodPattern n d leftCode rightCode).graph a) := by
  classical
  let cross : Fin d → Fin (n-d-1) → Bool := fun i j =>
    decide (G.Adj (eLeft.symm i).val (eRight.symm j).val)
  let a := neighborhoodAssignment cross
  let f := neighborhoodRelabel G v hd eLeft eRight
  have hi : Function.Injective f := neighborhoodRelabel_injective G v hd eLeft eRight
  let e : Fin n ≃ Fin n := Equiv.ofBijective f ⟨hi, Finite.surjective_of_injective hi⟩
  refine ⟨a, ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩⟩
  intro u w
  change ((neighborhoodPattern n d leftCode rightCode).graph a).Adj (f u) (f w) ↔ G.Adj u w
  change ((neighborhoodPattern n d leftCode rightCode).graph a).Adj
    (neighborhoodRelabel G v hd eLeft eRight u)
    (neighborhoodRelabel G v hd eLeft eRight w) ↔ G.Adj u w
  rcases neighborhood_vertex_cases G v u with rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩
  · rcases neighborhood_vertex_cases G v w with rfl | ⟨w, rfl⟩ | ⟨w, rfl⟩
    · simp
    · rw [neighborhoodRelabel_center, neighborhoodRelabel_left]
      exact ⟨fun _ => w.property,
        fun _ => neighborhoodPattern_center_left hd leftCode rightCode a (eLeft w)⟩
    · rw [neighborhoodRelabel_center, neighborhoodRelabel_right]
      have hn : ¬ G.Adj v w.val := by
        have hh : (Gᶜ).Adj v w.val := w.property
        exact ((G.compl_adj _ _).mp hh).2
      exact iff_of_false
        (neighborhoodPattern_center_right hd leftCode rightCode a (eRight w)) hn
  · rcases neighborhood_vertex_cases G v w with rfl | ⟨w, rfl⟩ | ⟨w, rfl⟩
    · rw [neighborhoodRelabel_left, neighborhoodRelabel_center]
      constructor
      · intro _; exact (G.adj_comm _ _).mp u.property
      · intro _
        exact (((neighborhoodPattern n d leftCode rightCode).graph a).adj_comm _ _).mp
          (neighborhoodPattern_center_left hd leftCode rightCode a (eLeft u))
    · rw [neighborhoodRelabel_left, neighborhoodRelabel_left, neighborhoodPattern_left]
      exact eLeft.map_rel_iff
    · rw [neighborhoodRelabel_left, neighborhoodRelabel_right, neighborhoodPattern_cross]
      change neighborhoodAssignment cross
        ((eLeft u).val * (n-d-1) + (eRight w).val) = true ↔ G.Adj u.val w.val
      rw [neighborhoodAssignment_apply]
      simp [cross]
  · rcases neighborhood_vertex_cases G v w with rfl | ⟨w, rfl⟩ | ⟨w, rfl⟩
    · rw [neighborhoodRelabel_right, neighborhoodRelabel_center]
      have hn : ¬ G.Adj u.val v := by
        have hh : (Gᶜ).Adj v u.val := u.property
        intro ha
        exact ((G.compl_adj _ _).mp hh).2 ((G.adj_comm _ _).mp ha)
      apply iff_of_false _ hn
      intro ha
      exact (neighborhoodPattern_center_right hd leftCode rightCode a (eRight u))
        ((((neighborhoodPattern n d leftCode rightCode).graph a).adj_comm _ _).mp ha)
    · rw [neighborhoodRelabel_right, neighborhoodRelabel_left, SimpleGraph.adj_comm]
      rw [neighborhoodPattern_cross]
      change neighborhoodAssignment cross
        ((eLeft w).val * (n-d-1) + (eRight u).val) = true ↔ G.Adj u.val w.val
      rw [neighborhoodAssignment_apply]
      simp [cross, SimpleGraph.adj_comm]
    · rw [neighborhoodRelabel_right, neighborhoodRelabel_right, neighborhoodPattern_right]
      exact neighborhoodRight_adj_iff G v eRight u w

#print axioms exists_neighborhoodPattern_iso
end CochromaticTwenty
