import MerLeanExperiment.PlaneDrawing
import MerLeanExperiment.Vendor.Erdos1018
import MerLeanExperiment.Vendor.Schoenflies.Curve

open scoped unitInterval
open Set Schoenflies

namespace Erdos1018Topological

open PlanarListColoring

/-- Compatible arcs for all edges of a clique determine an ordinary plane drawing. -/
theorem planeDrawing_of_cliqueEdge_arcs
    (r : ℕ) (point : Fin r → Plane) (hpoint : Function.Injective point)
    (A : Erdos1018.CliqueEdge r → Set Plane)
    (harcs : ∀ e, IsArcBetween (A e) (point e.1.1) (point e.1.2))
    (hvert : ∀ e i, point i ∈ A e → i = e.1.1 ∨ i = e.1.2)
    (hinter : ∀ e f, e ≠ f → ∀ z, z ∈ A e → z ∈ A f → z ∈ Set.range point) :
    Nonempty (PlaneDrawing (⊤ : SimpleGraph (Fin r))) := by
  classical
  let canon : (⊤ : SimpleGraph (Fin r)).edgeSet → Erdos1018.CliqueEdge r := fun e =>
    if h : e.1.out.1 < e.1.out.2 then ⟨(e.1.out.1, e.1.out.2), h⟩
    else ⟨(e.1.out.2, e.1.out.1), by
      have hab : e.1.out.1 ≠ e.1.out.2 := by
        intro hab
        have hedge : ¬e.1.IsDiag := by simpa using e.2
        apply hedge
        rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
        exact hab
      exact lt_of_le_of_ne (le_of_not_gt h) hab.symm⟩
  have hcanon (e : (⊤ : SimpleGraph (Fin r)).edgeSet) :
      s((canon e).1.1, (canon e).1.2) = e.1 := by
    dsimp [canon]
    split
    · exact e.1.out_eq
    · rw [Sym2.eq_swap]
      exact e.1.out_eq
  have hcanon_injective : Function.Injective canon := by
    intro e f hef
    apply Subtype.ext
    rw [← hcanon e, ← hcanon f, hef]
  have hcanon_vertex (e : (⊤ : SimpleGraph (Fin r)).edgeSet) (i : Fin r)
      (hi : i = (canon e).1.1 ∨ i = (canon e).1.2) :
      i = e.1.out.1 ∨ i = e.1.out.2 := by
    dsimp [canon] at hi
    split at hi
    · exact hi
    · rcases hi with hi | hi
      · exact Or.inr hi
      · exact Or.inl hi
  have horiented (e : (⊤ : SimpleGraph (Fin r)).edgeSet) :
      IsArcBetween (A (canon e)) (point e.1.out.1) (point e.1.out.2) := by
    dsimp [canon]
    split
    · exact harcs _
    · exact (harcs _).reverse
  choose curve hcont hinj himage hzero hone using horiented
  let vertexPoint : Fin r → Fin 2 → ℝ := fun i => WithLp.ofLp (point i)
  let edgePoint : (⊤ : SimpleGraph (Fin r)).edgeSet → I → Fin 2 → ℝ :=
    fun e t => WithLp.ofLp (curve e t.1)
  have havoid (e : (⊤ : SimpleGraph (Fin r)).edgeSet) (v : Fin r) (t : I)
      (ht0 : t ≠ 0) (ht1 : t ≠ 1) : edgePoint e t ≠ vertexPoint v := by
    intro heq
    have hcurve : curve e t.1 = point v := (WithLp.ofLp_injective 2) heq
    have hmem : point v ∈ A (canon e) := by
      rw [← himage e]
      exact ⟨t.1, t.property, hcurve⟩
    rcases hcanon_vertex e v (hvert (canon e) v hmem) with hv | hv
    · subst v
      have ht : t.1 = 0 := hinj e t.property zero_mem_I <| hcurve.trans (hzero e).symm
      exact ht0 (Subtype.ext ht)
    · subst v
      have ht : t.1 = 1 := hinj e t.property one_mem_I <| hcurve.trans (hone e).symm
      exact ht1 (Subtype.ext ht)
  refine ⟨{
    vertexPoint := vertexPoint
    vertexPoint_injective := (WithLp.ofLp_injective 2).comp hpoint
    edgePoint := edgePoint
    edge_continuous := ?_
    edge_zero := ?_
    edge_one := ?_
    edge_interior_injective := ?_
    edge_interior_avoids_vertex := ?_
    edge_interiors_disjoint := ?_ }⟩
  · intro e
    exact (PiLp.continuous_ofLp 2 _).comp (hcont e).domRestrict
  · intro e
    exact congrArg WithLp.ofLp (hzero e)
  · intro e
    exact congrArg WithLp.ofLp (hone e)
  · intro e s t _ _ _ _ hst
    apply Subtype.ext
    apply hinj e s.property t.property
    exact (WithLp.ofLp_injective 2) hst
  · intro e v t ht0 ht1 heq
    exact havoid e v t ht0 ht1 heq
  · intro e f hef s t hs0 hs1 ht0 ht1 heq
    have hcurve : curve e s.1 = curve f t.1 := (WithLp.ofLp_injective 2) heq
    have hmem_e : curve e s.1 ∈ A (canon e) := by
      rw [← himage e]
      exact ⟨s.1, s.property, rfl⟩
    have hmem_f : curve e s.1 ∈ A (canon f) := by
      rw [← himage f]
      exact ⟨t.1, t.property, hcurve.symm⟩
    obtain ⟨v, hv⟩ := hinter (canon e) (canon f)
      (fun h => hef (hcanon_injective h)) _ hmem_e hmem_f
    exact havoid e v s hs0 hs1 (congrArg WithLp.ofLp hv.symm)

end Erdos1018Topological
