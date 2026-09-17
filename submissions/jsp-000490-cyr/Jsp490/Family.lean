import Mathlib

/-!
# JSP-000490 / Erdős #603 — the family of clique edge sets

For a type `V` of vertices we work with the type `X := {e : Sym2 V // ¬ e.IsDiag}` of unordered
pairs of *distinct* vertices, i.e. the edges of the complete graph on `V`.  To a set `S` of
vertices we associate its clique `cliqueEdges S`, the set of edges with both endpoints in `S`.

This file collects the elementary combinatorial facts about this family that the main argument
needs: intersections of cliques are cliques, cliques of countable/infinite vertex sets are
countable/infinite, a clique edge set never has exactly two elements, every edge lies in a
countably infinite clique, and the transfer between colourings of `X` and symmetric colourings of
ordered pairs of vertices.
-/

universe u

namespace Erdos603

variable {V Y : Type u}

/-- The edge set of the clique on `S`: the pairs of distinct vertices both lying in `S`. -/
def cliqueEdges (S : Set V) : Set {e : Sym2 V // ¬ e.IsDiag} := {x | ∀ v ∈ x.1, v ∈ S}

/-! ### Elementary helpers -/

/-- Every non-diagonal unordered pair is `s(a, b)` for two distinct vertices `a`, `b`. -/
private theorem sym2_rep : ∀ e : Sym2 V, ¬ e.IsDiag → ∃ a b : V, a ≠ b ∧ e = s(a, b) := by
  intro e
  induction e using Sym2.ind with
  | _ a b => exact fun he => ⟨a, b, fun h => he (Sym2.mk_isDiag_iff.mpr h), rfl⟩

/-- Two unordered pairs are different as soon as the first vertex of the one differs from both
vertices of the other. -/
private theorem sym2_ne_of_left_ne {p q r t : V} (h₁ : p ≠ r) (h₂ : p ≠ t) :
    s(p, q) ≠ s(r, t) := by
  rw [Ne, Sym2.eq_iff]
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact h₁ h
  · exact h₂ h

/-- Two unordered pairs are different as soon as the second vertex of the one differs from both
vertices of the other. -/
private theorem sym2_ne_of_right_ne {p q r t : V} (h₁ : q ≠ r) (h₂ : q ≠ t) :
    s(p, q) ≠ s(r, t) := by
  rw [Ne, Sym2.eq_iff]
  rintro (⟨-, h⟩ | ⟨-, h⟩)
  · exact h₂ h
  · exact h₁ h

/-! ### Basic properties of `cliqueEdges` -/

theorem cliqueEdges_inter (S T : Set V) : cliqueEdges S ∩ cliqueEdges T = cliqueEdges (S ∩ T) := by
  ext x
  exact ⟨fun h v hv => ⟨h.1 v hv, h.2 v hv⟩,
    fun h => ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩⟩

theorem cliqueEdges_countable {S : Set V} (hS : S.Countable) : (cliqueEdges S).Countable := by
  have himg : ((fun p : V × V => s(p.1, p.2)) '' (S ×ˢ S)).Countable := (hS.prod hS).image _
  have hpre : ((Subtype.val : {e : Sym2 V // ¬ e.IsDiag} → Sym2 V) ⁻¹'
      ((fun p : V × V => s(p.1, p.2)) '' (S ×ˢ S))).Countable :=
    himg.preimage (fun _ _ h => Subtype.ext h)
  refine hpre.mono fun x hx => ?_
  obtain ⟨a, b, -, hrep⟩ := sym2_rep x.1 x.2
  have ha : a ∈ S := hx a (by rw [hrep]; exact Sym2.mem_mk_left a b)
  have hb : b ∈ S := hx b (by rw [hrep]; exact Sym2.mem_mk_right a b)
  exact ⟨(a, b), ⟨ha, hb⟩, hrep.symm⟩

theorem cliqueEdges_infinite {S : Set V} (hS : S.Infinite) : (cliqueEdges S).Infinite := by
  obtain ⟨s₀, hs₀⟩ := hS.nonempty
  have hd : (S \ {s₀}).Infinite := hS.sdiff (Set.finite_singleton _)
  have : Infinite ((S \ {s₀} : Set V)) := Set.infinite_coe_iff.mpr hd
  have hne : ∀ s : (S \ {s₀} : Set V), ¬ (s(s₀, (s : V)) : Sym2 V).IsDiag := fun s hdg =>
    s.2.2 (Sym2.mk_isDiag_iff.mp hdg).symm
  refine Set.infinite_of_injective_forall_mem
    (f := fun s : (S \ {s₀} : Set V) => (⟨s(s₀, (s : V)), hne s⟩ :
      {e : Sym2 V // ¬ e.IsDiag})) ?_ ?_
  · intro s t hst
    exact Subtype.ext (Sym2.congr_right.mp (congrArg Subtype.val hst))
  · intro s v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hs₀
    · exact s.2.1

/-! ### A clique edge set never has exactly two elements -/

theorem cliqueEdges_encard_ne_two (U : Set V) : (cliqueEdges U).encard ≠ 2 := by
  intro h2
  obtain ⟨e₁, e₂, hne, hset⟩ := Set.encard_eq_two.mp h2
  have h₁ : e₁ ∈ cliqueEdges U := by rw [hset]; exact Set.mem_insert _ _
  have h₂ : e₂ ∈ cliqueEdges U := by rw [hset]; exact Set.mem_insert_of_mem _ rfl
  obtain ⟨a, b, hab, hrep₁⟩ := sym2_rep e₁.1 e₁.2
  obtain ⟨c, d, hcd, hrep₂⟩ := sym2_rep e₂.1 e₂.2
  have haU : a ∈ U := h₁ a (by rw [hrep₁]; exact Sym2.mem_mk_left a b)
  have hbU : b ∈ U := h₁ b (by rw [hrep₁]; exact Sym2.mem_mk_right a b)
  have hcU : c ∈ U := h₂ c (by rw [hrep₂]; exact Sym2.mem_mk_left c d)
  have hdU : d ∈ U := h₂ d (by rw [hrep₂]; exact Sym2.mem_mk_right c d)
  have hval : s(a, b) ≠ s(c, d) := fun h =>
    hne (Subtype.ext (hrep₁.trans (h.trans hrep₂.symm)))
  -- Any edge of the clique on `U` is one of the two given ones.
  have key : ∀ p ∈ U, ∀ q ∈ U, p ≠ q → s(p, q) = s(a, b) ∨ s(p, q) = s(c, d) := by
    intro p hp q hq hpq
    have hmem : (⟨s(p, q), fun hdg => hpq (Sym2.mk_isDiag_iff.mp hdg)⟩ :
        {e : Sym2 V // ¬ e.IsDiag}) ∈ cliqueEdges U := by
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact hp
      · exact hq
    rw [hset] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact Or.inl (by rw [← hrep₁]; exact congrArg Subtype.val h)
    · exact Or.inr (by rw [← hrep₂]; exact congrArg Subtype.val h)
  by_cases hac : a = c
  · -- The two edges share the vertex `a = c`; then `s(b, d)` is a third edge.
    have hbd : b ≠ d := fun h => hval (by rw [hac, h])
    have had : a ≠ d := by rw [hac]; exact hcd
    have hbc : b ≠ c := by rw [← hac]; exact Ne.symm hab
    rcases key b hbU d hdU hbd with h | h
    · exact sym2_ne_of_right_ne (Ne.symm had) (Ne.symm hbd) h
    · exact sym2_ne_of_left_ne hbc hbd h
  · by_cases had : a = d
    · -- They share the vertex `a = d`; then `s(b, c)` is a third edge.
      have hbc : b ≠ c := fun h => hval (by rw [had, h]; exact Sym2.eq_swap)
      have hca : c ≠ a := by rw [had]; exact hcd
      have hbd : b ≠ d := by rw [← had]; exact Ne.symm hab
      rcases key b hbU c hcU hbc with h | h
      · exact sym2_ne_of_right_ne hca (Ne.symm hbc) h
      · exact sym2_ne_of_left_ne hbc hbd h
    · by_cases hbc : b = c
      · -- They share the vertex `b = c`; then `s(a, d)` is a third edge.
        have hadne : a ≠ d := had
        have hbd : b ≠ d := by rw [hbc]; exact hcd
        have hac' : a ≠ c := hac
        rcases key a haU d hdU hadne with h | h
        · exact sym2_ne_of_right_ne (Ne.symm hadne) (Ne.symm hbd) h
        · exact sym2_ne_of_left_ne hac' hadne h
      · -- `a` lies on neither `c` nor `d`, and `b ≠ c`; then `s(a, c)` is a third edge.
        rcases key a haU c hcU hac with h | h
        · exact sym2_ne_of_right_ne (Ne.symm hac) (Ne.symm hbc) h
        · exact sym2_ne_of_left_ne hac had h

/-! ### Covering the edges by countably infinite cliques -/

/-- Every edge lies in the edge set of some countably infinite clique (`V` infinite). -/
theorem exists_cliqueEdges_mem [Infinite V] (x : {e : Sym2 V // ¬ e.IsDiag}) :
    ∃ S : Set V, S.Countable ∧ S.Infinite ∧ x ∈ cliqueEdges S := by
  obtain ⟨a, b, -, hrep⟩ := sym2_rep x.1 x.2
  refine ⟨{a, b} ∪ Set.range (Infinite.natEmbedding V), ?_, ?_, ?_⟩
  · exact ((Set.countable_singleton b).insert a).union (Set.countable_range _)
  · exact Set.Infinite.mono Set.subset_union_right
      (Set.infinite_range_of_injective (Infinite.natEmbedding V).injective)
  · intro v hv
    rw [hrep] at hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact Set.mem_union_left _ (Set.mem_insert _ _)
    · exact Set.mem_union_left _ (Set.mem_insert_of_mem _ rfl)

/-- If `V` has two distinct elements then `X` is nonempty. -/
theorem nonempty_edges (h : ∃ a b : V, a ≠ b) : Nonempty {e : Sym2 V // ¬ e.IsDiag} := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨⟨s(a, b), fun hd => hab (Sym2.mk_isDiag_iff.mp hd)⟩⟩

/-! ### Transfer between edge colourings and symmetric colourings of ordered pairs -/

open Classical in
/-- Turn a colouring of the edges into a symmetric colouring of ordered pairs (`y₀` on the
diagonal). -/
noncomputable def pairColour (col : {e : Sym2 V // ¬ e.IsDiag} → Y) (y₀ : Y) (u v : V) : Y :=
  if h : u = v then y₀ else col ⟨s(u, v), by simpa [Sym2.mk_isDiag_iff] using h⟩

theorem pairColour_of_ne (col : {e : Sym2 V // ¬ e.IsDiag} → Y) (y₀ : Y) {u v : V} (h : u ≠ v) :
    pairColour col y₀ u v = col ⟨s(u, v), by simpa [Sym2.mk_isDiag_iff] using h⟩ := by
  unfold pairColour
  exact dite_eq_right h

theorem pairColour_symm (col : {e : Sym2 V // ¬ e.IsDiag} → Y) (y₀ : Y) (u v : V) :
    pairColour col y₀ u v = pairColour col y₀ v u := by
  by_cases h : u = v
  · rw [h]
  · rw [pairColour_of_ne col y₀ h, pairColour_of_ne col y₀ (Ne.symm h)]
    exact congrArg col (Subtype.ext Sym2.eq_swap)

/-- A clique whose distinct pairs all get colour `y₁` has a monochromatic edge set. -/
theorem cliqueEdges_monochromatic (col : {e : Sym2 V // ¬ e.IsDiag} → Y) (y₀ y₁ : Y) {S : Set V}
    (h : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → pairColour col y₀ u v = y₁) :
    ∀ x ∈ cliqueEdges S, col x = y₁ := by
  intro x hx
  obtain ⟨a, b, hab, hrep⟩ := sym2_rep x.1 x.2
  have haS : a ∈ S := hx a (by rw [hrep]; exact Sym2.mem_mk_left a b)
  have hbS : b ∈ S := hx b (by rw [hrep]; exact Sym2.mem_mk_right a b)
  have hxe : x = ⟨s(a, b), fun hd => hab (Sym2.mk_isDiag_iff.mp hd)⟩ := Subtype.ext hrep
  rw [hxe]
  exact (pairColour_of_ne col y₀ hab).symm.trans (h a haS b hbS hab)

end Erdos603

