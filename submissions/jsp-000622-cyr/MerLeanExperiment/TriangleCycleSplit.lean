import MerLeanExperiment.GraphSplit
import MerLeanExperiment.CocoloringAssembly
import MerLeanExperiment.SmallRamsey
import MerLeanExperiment.TriangleCycleMeaning

/-!
Normalization of an eight-vertex graph around a homogeneous triple.  The
exceptional five-vertex remainder is represented by the triangle-plus-cycle
pattern whose concrete three-cocoloring theorem is proved separately.
-/

namespace CochromaticTwenty

variable {V : Type*} {G : SimpleGraph V}

/-- Homogeneity is unchanged by graph complementation. -/
theorem homogeneous_compl_iff {s : Set V} :
    Homogeneous Gᶜ s ↔ Homogeneous G s := by
  constructor
  · rintro (h | h)
    · refine Or.inr ?_
      intro u hu v hv huv hadj
      exact (h hu hv huv).2 hadj
    · refine Or.inl ?_
      intro u hu v hv huv
      by_contra hadj
      exact h hu hv huv ⟨huv, hadj⟩
  · rintro (h | h)
    · refine Or.inr ?_
      intro u hu v hv huv hadj
      exact hadj.2 (h hu hv huv)
    · refine Or.inl ?_
      intro u hu v hv huv
      exact ⟨huv, h hu hv huv⟩

/-- A cocoloring is unchanged by graph complementation. -/
theorem hasCocoloring_compl_iff {k : ℕ} :
    HasCocoloring Gᶜ k ↔ HasCocoloring G k := by
  constructor
  · rintro ⟨color, hcolor⟩
    exact ⟨color, fun i ↦ homogeneous_compl_iff.mp (hcolor i)⟩
  · rintro ⟨color, hcolor⟩
    exact ⟨color, fun i ↦ homogeneous_compl_iff.mpr (hcolor i)⟩

/-- A three-vertex clique is isomorphic to the complete graph on `Fin 3`. -/
noncomputable def cliqueThreeIso {s : Finset V}
    (hcard : s.card = 3) (hclique : G.IsClique (s : Set V)) :
    G.induce (s : Set V) ≃g (⊤ : SimpleGraph (Fin 3)) where
  toEquiv := Fintype.equivFinOfCardEq (by simp [hcard])
  map_rel_iff' := by
    intro u v
    change
      Fintype.equivFinOfCardEq (by simp [hcard]) u ≠
          Fintype.equivFinOfCardEq (by simp [hcard]) v ↔
        G.Adj u v
    constructor
    · intro huv
      exact hclique u.property v.property
        (fun h ↦ huv (congrArg
          (Fintype.equivFinOfCardEq (by simp [hcard])) (Subtype.ext h)))
    · intro huv hEq
      have huvEq : u = v :=
        (Fintype.equivFinOfCardEq (by simp [hcard])).injective hEq
      subst v
      exact G.irrefl huv

/-- Encode the fifteen cross edges between `Fin 3` and `Fin 5`. -/
def triangleCycleAssignment (cross : Fin 3 → Fin 5 → Bool) : ℕ → Bool :=
  fun i ↦ if hi : i < 15 then
    let uv := (finProdFinEquiv : Fin 3 × Fin 5 ≃ Fin 15).symm ⟨i, hi⟩
    cross uv.1 uv.2
  else false

@[simp]
theorem triangleCycleAssignment_apply (cross : Fin 3 → Fin 5 → Bool)
    (u : Fin 3) (v : Fin 5) :
    triangleCycleAssignment cross (u.val * 5 + v.val) = cross u v := by
  have hlt : u.val * 5 + v.val < 15 := by omega
  unfold triangleCycleAssignment
  rw [dite_eq_left hlt]
  have heq : (⟨u.val * 5 + v.val, hlt⟩ : Fin 15) =
      (finProdFinEquiv : Fin 3 × Fin 5 ≃ Fin 15) (u, v) := by
    apply Fin.ext
    simp [finProdFinEquiv]
    omega
  rw [heq, Equiv.symm_apply_apply]

/-- The corresponding sum extension is the triangle-plus-five-cycle graph
pattern. -/
def sumExtensionTriangleCycleIso (cross : Fin 3 → Fin 5 → Bool) :
    sumExtensionGraph (⊤ : SimpleGraph (Fin 3)) cycleFive cross ≃g
      triangleCyclePattern.graph (triangleCycleAssignment cross) where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by
    intro u v
    cases u with
    | inl u =>
        cases v with
        | inl v =>
            rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left]
            have hu : Fin.castAdd 5 u = u.castLE (by decide) := Fin.ext rfl
            have hv : Fin.castAdd 5 v = v.castLE (by decide) := Fin.ext rfl
            rw [hu, hv]
            simpa using
              (triangleCyclePattern_left (triangleCycleAssignment cross) u v)
        | inr v =>
            rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
            have hu : Fin.castAdd 5 u = u.castLE (by decide) := Fin.ext rfl
            rw [hu]
            simpa using
              (triangleCyclePattern_cross (triangleCycleAssignment cross) u v)
    | inr u =>
        cases v with
        | inl v =>
            rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_left]
            have hv : Fin.castAdd 5 v = v.castLE (by decide) := Fin.ext rfl
            rw [hv, SimpleGraph.adj_comm]
            simpa using
              (triangleCyclePattern_cross (triangleCycleAssignment cross) v u)
        | inr v =>
            rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_right]
            simpa using
              (triangleCyclePattern_right (triangleCycleAssignment cross) u v)

/-- A graph split into an actual triangle and an actual five-cycle remainder
is one of the triangle-cycle pattern graphs. -/
theorem exists_triangleCyclePattern_iso (G : SimpleGraph (Fin 8))
    {s : Finset (Fin 8)} (hcard : s.card = 3)
    (hclique : G.IsClique (s : Set (Fin 8)))
    (eRight : G.induce ((s : Set (Fin 8))ᶜ) ≃g cycleFive) :
    ∃ a : ℕ → Bool, Nonempty (G ≃g triangleCyclePattern.graph a) := by
  let eLeft := cliqueThreeIso hcard hclique
  obtain ⟨cross, ⟨e⟩⟩ := exists_sumExtensionGraph_iso
    G (s : Set (Fin 8)) (⊤ : SimpleGraph (Fin 3)) cycleFive eLeft eRight
  exact ⟨triangleCycleAssignment cross,
    ⟨e.trans (sumExtensionTriangleCycleIso cross)⟩⟩

private theorem hasCocoloring_three_of_clique_three
    (G : SimpleGraph (Fin 8)) {s : Finset (Fin 8)}
    (hcard : s.card = 3) (hclique : G.IsClique (s : Set (Fin 8))) :
    HasCocoloring G 3 := by
  classical
  let S : Set (Fin 8) := (s : Set (Fin 8))
  have hSCard : Fintype.card S = 3 := by simp [S, hcard]
  have hcompCard : Fintype.card ↥(Sᶜ) = 5 := by
    rw [Fintype.card_compl_set, hSCard]
    simp
  let H : SimpleGraph ↥(Sᶜ) := G.induce (Sᶜ)
  let eFin : H ≃g H.overFin hcompCard := H.overFinIso hcompCard
  rcases fiveVertexClassification (H.overFin hcompCard) with hcolor | hcycle
  · have hleft : HasCocoloring (G.induce S) 1 :=
      hasCocoloring_one_of_homogeneous (Or.inl hclique)
    have hright : HasCocoloring (G.induce (Sᶜ)) 2 := by
      exact (hasCocoloring_iso_iff eFin).mpr hcolor
    simpa using hleft.induce_add hright
  · obtain ⟨eCycle⟩ := hcycle
    have eRight : G.induce (Sᶜ) ≃g cycleFive := eFin.trans eCycle
    obtain ⟨a, ⟨e⟩⟩ := exists_triangleCyclePattern_iso G hcard hclique eRight
    exact (hasCocoloring_iso_iff e).mpr
      (TriangleCycleMeaning.triangleCycle_hasCocoloring a)

/-- Every ordinary graph on eight vertices has a three-cocoloring. -/
theorem fin8_hasCocoloring_three (G : SimpleGraph (Fin 8)) :
    HasCocoloring G 3 := by
  rcases ramsey_three_three G (by simp) with ⟨s, hcard, hclique⟩ |
      ⟨s, hcard, hindependent⟩
  · exact hasCocoloring_three_of_clique_three G hcard hclique
  · have hclique : Gᶜ.IsClique (s : Set (Fin 8)) := by
      intro u hu v hv huv
      exact ⟨huv, hindependent hu hv huv⟩
    have hcolor := hasCocoloring_three_of_clique_three Gᶜ hcard hclique
    exact hasCocoloring_compl_iff.mp hcolor

end CochromaticTwenty

#print axioms CochromaticTwenty.exists_triangleCyclePattern_iso
#print axioms CochromaticTwenty.fin8_hasCocoloring_three
