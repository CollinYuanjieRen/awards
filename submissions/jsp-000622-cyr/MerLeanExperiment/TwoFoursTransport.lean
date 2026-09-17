import MerLeanExperiment.TriangleCycleSplit

namespace CochromaticTwenty
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem TwoHomogeneousFours.map_iso (e : G ≃g H) (h : TwoHomogeneousFours G) :
    TwoHomogeneousFours H := by
  classical
  obtain ⟨s, t, hs, ht, hdisj, hsh, hth⟩ := h
  refine ⟨s.map e.toEquiv.toEmbedding, t.map e.toEquiv.toEmbedding,
    by simpa using hs, by simpa using ht, ?_, ?_, ?_⟩
  · exact (Finset.disjoint_map _).mpr hdisj
  · simpa [Finset.coe_map] using homogeneous_image e hsh
  · simpa [Finset.coe_map] using homogeneous_image e hth

theorem twoHomogeneousFours_compl_iff : TwoHomogeneousFours Gᶜ ↔ TwoHomogeneousFours G := by
  constructor
  · rintro ⟨s, t, hs, ht, hd, hsh, hth⟩
    exact ⟨s, t, hs, ht, hd, homogeneous_compl_iff.mp hsh, homogeneous_compl_iff.mp hth⟩
  · rintro ⟨s, t, hs, ht, hd, hsh, hth⟩
    exact ⟨s, t, hs, ht, hd, homogeneous_compl_iff.mpr hsh, homogeneous_compl_iff.mpr hth⟩

/-- A homogeneous four-set in the complement of a first homogeneous four-set
is an actual disjoint second set in the ambient graph. -/
theorem twoHomogeneousFours_of_induce_compl (s : Finset V) (hs : s.card = 4)
    (hsh : Homogeneous G (s : Set V))
    (t : Finset ↥((s : Set V)ᶜ)) (ht : t.card = 4)
    (hth : Homogeneous (G.induce ((s : Set V)ᶜ)) (t : Set ↥((s : Set V)ᶜ))) :
    TwoHomogeneousFours G := by
  classical
  let emb : ↥((s : Set V)ᶜ) ↪ V := Function.Embedding.subtype _
  refine ⟨s, t.map emb, hs, by simpa using ht, ?_, hsh, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hvt
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hvt
    exact w.property hv
  · simpa [Finset.coe_map, emb] using homogeneous_image_subtype hth

end CochromaticTwenty
#print axioms CochromaticTwenty.TwoHomogeneousFours.map_iso
#print axioms CochromaticTwenty.twoHomogeneousFours_of_induce_compl
