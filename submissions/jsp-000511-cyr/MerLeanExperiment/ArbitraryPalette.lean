import MerLeanExperiment.Goal

namespace PlanarListColoring

theorem planar_bipartite_three_list_colorable_palette
    {V : Type} {C : Type*} [Fintype V] (G : SimpleGraph V)
    (hplanar : Nonempty (PlaneDrawing G)) (hbipartite : G.IsBipartite)
    (L : V → Finset C) (hL : ∀ v, (L v).card = 3) :
    ∃ f : G.Coloring C, ∀ v, f v ∈ L v := by
  classical
  let S : Finset C := Finset.univ.biUnion L
  let encode : C → ℕ := fun c =>
    if hc : c ∈ S then (Fintype.equivFin S ⟨c, hc⟩).val else 0
  have hencode_inj : Set.InjOn encode (↑S : Set C) := by
    intro a ha b hb hab
    have ha' : a ∈ S := ha
    have hb' : b ∈ S := hb
    have hea : encode a = (Fintype.equivFin S ⟨a, ha⟩).val := by
      simp [encode, ha']
    have heb : encode b = (Fintype.equivFin S ⟨b, hb⟩).val := by
      simp [encode, hb']
    rw [hea, heb] at hab
    have hsub : (⟨a, ha⟩ : S) = ⟨b, hb⟩ := by
      apply (Fintype.equivFin S).injective
      apply Fin.ext
      exact hab
    exact congrArg Subtype.val hsub
  let LN : V → Finset ℕ := fun v => (L v).image encode
  have hLS (v : V) : ↑(L v) ⊆ (↑S : Set C) := by
    intro c hc
    exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, hc⟩
  have hLN (v : V) : (LN v).card = 3 := by
    rw [Finset.card_image_iff.mpr (hencode_inj.mono (hLS v)), hL v]
  obtain ⟨fN, hfN⟩ :=
    planar_bipartite_three_list_colorable G hplanar hbipartite LN hLN
  have hex (v : V) : ∃ c ∈ L v, encode c = fN v := by
    simpa only [LN, Finset.mem_image] using hfN v
  choose f hfL hfencode using hex
  refine ⟨SimpleGraph.Coloring.mk f ?_, hfL⟩
  intro u v huv huv_eq
  apply fN.valid huv
  rw [← hfencode u, ← hfencode v, huv_eq]

end PlanarListColoring
