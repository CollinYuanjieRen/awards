import MerLeanExperiment.Vendor.Erdos1018

open Function Set SimpleGraph
open scoped Sym2

namespace Erdos1018.CliqueSubdivision

variable {V : Type*} {G : SimpleGraph V} {r : ℕ}

/-- A common vertex of two distinct subdivision routes is an endpoint of each route. -/
theorem support_inter_eq_endpoints (s : CliqueSubdivision G r) {e f : CliqueEdge r}
    (hef : e ≠ f) {x : V} (hxe : x ∈ (s.path e).support)
    (hxf : x ∈ (s.path f).support) :
    (x = s.branch e.1.1 ∨ x = s.branch e.1.2) ∧
      (x = s.branch f.1.1 ∨ x = s.branch f.1.2) := by
  have endpoint_of_interior {g h : CliqueEdge r} (hgh : g ≠ h)
      (hxg : x ∈ walkInteriorSet (s.path g)) (hxh : x ∈ (s.path h).support) :
      x = s.branch h.1.1 ∨ x = s.branch h.1.2 := by
    by_contra hends
    push Not at hends
    have hxh' : x ∈ walkInteriorSet (s.path h) := ⟨hxh, hends.1, hends.2⟩
    exact Set.disjoint_left.mp (s.interior_pairwise hgh) hxg hxh'
  constructor
  · by_cases hx1 : x = s.branch e.1.1
    · exact Or.inl hx1
    by_cases hx2 : x = s.branch e.1.2
    · exact Or.inr hx2
    exfalso
    have hfend := endpoint_of_interior (g := e) (h := f) hef ⟨hxe, hx1, hx2⟩ hxf
    rcases hfend with hf1 | hf2
    · exact Set.disjoint_left.mp (s.interior_avoids_branch e)
        ⟨hxe, hx1, hx2⟩ ⟨f.1.1, hf1.symm⟩
    · exact Set.disjoint_left.mp (s.interior_avoids_branch e)
        ⟨hxe, hx1, hx2⟩ ⟨f.1.2, hf2.symm⟩
  · by_cases hx1 : x = s.branch f.1.1
    · exact Or.inl hx1
    by_cases hx2 : x = s.branch f.1.2
    · exact Or.inr hx2
    exfalso
    have heend := endpoint_of_interior (g := f) (h := e) hef.symm ⟨hxf, hx1, hx2⟩ hxe
    rcases heend with he1 | he2
    · exact Set.disjoint_left.mp (s.interior_avoids_branch f)
        ⟨hxf, hx1, hx2⟩ ⟨e.1.1, he1.symm⟩
    · exact Set.disjoint_left.mp (s.interior_avoids_branch f)
        ⟨hxf, hx1, hx2⟩ ⟨e.1.2, he2.symm⟩

/-- Distinct ordered clique edges have different unordered branch-endpoint pairs. -/
theorem branch_endpoint_pair_ne (s : CliqueSubdivision G r) {e f : CliqueEdge r}
    (hef : e ≠ f) :
    ({s.branch e.1.1, s.branch e.1.2} : Set V) ≠
      {s.branch f.1.1, s.branch f.1.2} := by
  intro hpair
  rw [Set.pair_eq_pair_iff] at hpair
  rcases hpair with hdir | hswap
  · apply hef
    apply Subtype.ext
    apply Prod.ext
    · exact s.branch.injective hdir.1
    · exact s.branch.injective hdir.2
  · have h₁ : e.1.1 = f.1.2 := s.branch.injective hswap.1
    have h₂ : e.1.2 = f.1.1 := s.branch.injective hswap.2
    have hrev : f.1.2 < f.1.1 := by simpa [h₁, h₂] using e.2
    exact lt_asymm f.2 hrev

private theorem pair_eq_of_two_common {a b c d x y : V} (hxy : x ≠ y)
    (hxab : x = a ∨ x = b) (hyab : y = a ∨ y = b)
    (hxcd : x = c ∨ x = d) (hycd : y = c ∨ y = d) :
    ({a, b} : Set V) = {c, d} := by
  rw [Set.pair_eq_pair_iff]
  rcases hxab with rfl | rfl <;> rcases hyab with rfl | rfl <;>
    rcases hxcd with hxc | hxd <;> rcases hycd with hyc | hyd <;>
    simp_all [eq_comm]

/-- Distinct subdivision routes have disjoint ambient-edge lists. -/
theorem path_edges_disjoint (s : CliqueSubdivision G r) {e f : CliqueEdge r}
    (hef : e ≠ f) : List.Disjoint (s.path e).edges (s.path f).edges := by
  rw [List.disjoint_left]
  intro g hge hgf
  let x := g.out.1
  let y := g.out.2
  have hg : s(x, y) = g := by rw [Sym2.mk, g.out_eq]
  have hxy : x ≠ y := (s.path e).adj_of_mem_edges (hg ▸ hge) |>.ne
  have support_mem (p : G.Walk (s.branch e.1.1) (s.branch e.1.2))
      (hgP : g ∈ p.edges) (z : V) (hz : z ∈ g) : z ∈ p.support :=
    Walk.mem_support_iff_exists_mem_edges.2 <| Or.inr ⟨g, hgP, hz⟩
  have hxe : x ∈ (s.path e).support := support_mem (s.path e) hge x (by
    rw [← hg]
    simp)
  have hye : y ∈ (s.path e).support := support_mem (s.path e) hge y (by
    rw [← hg]
    simp)
  have hxf : x ∈ (s.path f).support :=
    Walk.mem_support_iff_exists_mem_edges.2 <| Or.inr ⟨g, hgf, by rw [← hg]; simp⟩
  have hyf : y ∈ (s.path f).support :=
    Walk.mem_support_iff_exists_mem_edges.2 <| Or.inr ⟨g, hgf, by rw [← hg]; simp⟩
  have hxends := s.support_inter_eq_endpoints hef hxe hxf
  have hyends := s.support_inter_eq_endpoints hef hye hyf
  apply s.branch_endpoint_pair_ne hef
  exact pair_eq_of_two_common hxy hxends.1 hyends.1 hxends.2 hyends.2

/-- A branch vertex lying on a subdivision route is one of that route's endpoints. -/
theorem branch_mem_support_eq_endpoint (s : CliqueSubdivision G r) (i : Fin r)
    (e : CliqueEdge r) (hmem : s.branch i ∈ (s.path e).support) :
    i = e.1.1 ∨ i = e.1.2 := by
  by_contra hends
  push Not at hends
  have hinterior : s.branch i ∈ walkInteriorSet (s.path e) := by
    exact ⟨hmem, fun h ↦ hends.1 (s.branch.injective h),
      fun h ↦ hends.2 (s.branch.injective h)⟩
  exact Set.disjoint_left.mp (s.interior_avoids_branch e)
    hinterior ⟨i, rfl⟩

end Erdos1018.CliqueSubdivision
