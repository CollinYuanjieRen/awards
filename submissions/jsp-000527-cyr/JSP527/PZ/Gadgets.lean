/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (JSP-000527 submission, 2026-09-16).
-/
import JSP527.PZ.Assembly

/-!
# Proposition 3.1 on every ordered triple of a uniform separated cluster family

This file turns the single-triple statement `pohoata_zakharov_prop_three_one` into the
triple-indexed family consumed by the Ramsey step of Pohoata--Zakharov.  For a uniform
separated cluster family `U` on `Fin m` with `5 ≤ m` it produces, for every ordered triple
`j₁ < j₂ < j₃`, the two trihedral polyhedra containing the two alternating regions of (4.8),
and it packages the whole assignment as a `TripleGadgetFamily (Fin m)` indexed by three-element
subsets through the increasing enumeration `Finset.orderEmbOfFin`.
-/

namespace Erdos651

open Finset Set

noncomputable section

/-- Distinct clusters are disjoint and nonempty, so a family of `m` of them inside `X` forces
`m ≤ X.card`; four clusters already give the cardinality needed for general position to
constrain triples. -/
theorem UniformSeparatedClusters.four_le_card {k m : ℕ} {X : Finset (Point 3)}
    (U : UniformSeparatedClusters k m X) (hm : 4 ≤ m) : 4 ≤ X.card := by
  classical
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin m)), U.representative i ∈ X := fun i _ =>
    U.cluster_subset i (U.representative_mem i)
  have hinj : Set.InjOn U.representative (Finset.univ : Finset (Fin m)) := by
    intro i _ j _ hij
    by_contra hne
    exact Finset.disjoint_left.mp (U.strongConvex.pairwiseDisjoint hne)
      (U.representative_mem i) (hij ▸ U.representative_mem j)
  have hcard : m ≤ X.card := by
    simpa using Finset.card_le_card_of_injOn U.representative hmem hinj
  omega

/-- The three-point analogue of `affineIndependent_fin_four_of_generalPosition`: an explicitly
indexed injective triple of a general-position set with at least four points is affinely
independent. -/
theorem affineIndependent_fin_three_of_generalPosition {U : Finset (Point 3)}
    (hUcard : 4 ≤ U.card) (hgp : InGeneralPosition 3 U) (p : Fin 3 → Point 3)
    (hpU : ∀ i, p i ∈ U) (hpinj : Function.Injective p) :
    AffineIndependent ℝ p := by
  classical
  let A := Finset.univ.image p
  have hAU : A ⊆ U := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hpU i
  have hAcard : A.card ≤ 3 := by
    simpa [A] using
      Finset.card_image_le (s := (Finset.univ : Finset (Fin 3))) (f := p)
  have hAind : AffineIndependent ℝ (fun x : A ↦ (x : Point 3)) :=
    affineIndependent_of_card_le_three_of_generalPosition_three hgp hUcard hAU hAcard
  let e : Fin 3 ↪ A :=
    ⟨fun i ↦ ⟨p i, Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩⟩,
      fun i j hij ↦ hpinj (congrArg Subtype.val hij)⟩
  convert hAind.comp_embedding e using 1
  funext i
  rfl

/-- A subset of a three-dimensional general-position set with at least four points has no three
collinear points, in the linear-independence form required by Proposition 3.1. -/
theorem noThreeCollinear_of_generalPosition {X Y : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hXcard : 4 ≤ X.card) (hYX : Y ⊆ X) :
    NoThreeCollinear Y := by
  intro x hx y hy z hz hxy hyz hxz
  have hpU : ∀ i, ![x, y, z] i ∈ X := by
    intro i
    fin_cases i
    · exact hYX hx
    · exact hYX hy
    · exact hYX hz
  have hpinj : Function.Injective ![x, y, z] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have h : AffineIndependent ℝ ![x, y, z] :=
    affineIndependent_fin_three_of_generalPosition hXcard hgp _ hpU hpinj
  apply (linearIndependent_equiv' (finSuccAboveEquiv (0 : Fin 3)) ?_).mpr
    ((affineIndependent_iff_linearIndependent_vsub ℝ ![x, y, z] 0).mp h)
  funext i
  fin_cases i <;> rfl

/-- The two full-cluster separations required by Proposition 3.1, obtained from the
representative-level Corollary 2.4 through Proposition 2.7. -/
theorem UniformSeparatedClusters.trihedral_cluster_hulls_disjoint {k m : ℕ}
    {X : Finset (Point 3)} (U : UniformSeparatedClusters k m X) (hm : 5 ≤ m)
    (j₁ j₂ j₃ : Fin m) (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃) :
    Disjoint
      (convexHull ℝ
        (↑(clusterUnion U.cluster (firstTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)))
      (convexHull ℝ
        (↑(clusterUnion U.cluster (secondTrihedralIndices j₁ j₂ j₃ ∪ {j₂})) :
          Set (Point 3))) ∧
    Disjoint
      (convexHull ℝ
        (↑(clusterUnion U.cluster (firstTrihedralIndices j₁ j₂ j₃ ∪ {j₂})) :
          Set (Point 3)))
      (convexHull ℝ
        (↑(clusterUnion U.cluster (secondTrihedralIndices j₁ j₂ j₃)) : Set (Point 3))) := by
  classical
  obtain ⟨hrep₁, hrep₂⟩ :=
    trihedral_representative_hulls_disjoint U.representative hm U.projectedChain
      U.uniformAboveBelow j₁ j₂ j₃ h₁₂ h₂₃
  have hunion := trihedralIndices_union_middle h₁₂ h₂₃
  have hunion' : (firstTrihedralIndices j₁ j₂ j₃ ∪ {j₂}) ∪
      secondTrihedralIndices j₁ j₂ j₃ = Finset.univ := by
    rw [Finset.union_assoc, Finset.union_comm ({j₂} : Finset (Fin m))]
    exact hunion
  have hj₃ : j₃ ∈ firstTrihedralIndices j₁ j₂ j₃ := by simp [h₂₃]
  have hj₁ : j₁ ∈ secondTrihedralIndices j₁ j₂ j₃ := by simp [h₁₂]
  exact ⟨U.fullCluster_hulls_disjoint _ _ hunion ⟨j₃, hj₃⟩ ⟨j₂, by simp⟩ hrep₁,
    U.fullCluster_hulls_disjoint _ _ hunion' ⟨j₂, by simp⟩ ⟨j₁, hj₁⟩ hrep₂⟩

/-- Proposition 3.1 applied to one ordered triple of a uniform separated cluster family. -/
theorem exists_trihedralClusterGadget {k m : ℕ} {X : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hm : 5 ≤ m)
    (U : UniformSeparatedClusters k m X) (j₁ j₂ j₃ : Fin m)
    (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃) :
    Nonempty (TrihedralClusterGadget U.cluster j₁ j₂ j₃) := by
  obtain ⟨hfirst, hsecond⟩ :=
    U.trihedral_cluster_hulls_disjoint hm j₁ j₂ j₃ h₁₂ h₂₃
  exact pohoata_zakharov_prop_three_one U.cluster j₁ j₂ j₃ h₁₂ h₂₃ U.nonempty
    (noThreeCollinear_of_generalPosition hgp (U.four_le_card (by omega))
      (U.cluster_subset j₂))
    U.strongConvex hfirst hsecond

/-- A choice of Proposition 3.1 gadget for each ordered triple. -/
def clusterGadget {k m : ℕ} {X : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hm : 5 ≤ m) (U : UniformSeparatedClusters k m X)
    (j₁ j₂ j₃ : Fin m) (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃) :
    TrihedralClusterGadget U.cluster j₁ j₂ j₃ :=
  Classical.choice (exists_trihedralClusterGadget hgp hm U j₁ j₂ j₃ h₁₂ h₂₃)

/-- The triple gadget family attached to a uniform separated cluster family: a three-element
index set is enumerated increasingly and receives the gadget of its sorted triple. -/
def gadgetFamily {k m : ℕ} {X : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hm : 5 ≤ m) (U : UniformSeparatedClusters k m X) :
    TripleGadgetFamily (Fin m) := fun J hJ =>
  (clusterGadget hgp hm U (J.orderEmbOfFin hJ 0) (J.orderEmbOfFin hJ 1)
      (J.orderEmbOfFin hJ 2) ((J.orderEmbOfFin hJ).strictMono (by decide))
      ((J.orderEmbOfFin hJ).strictMono (by decide))).toMiddleTripleGadget

/-- The middle cluster and the two containments (4.8) for the gadget attached to a
three-element index set with a named increasing enumeration. -/
theorem gadgetFamily_spec {k m : ℕ} {X : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hm : 5 ≤ m) (U : UniformSeparatedClusters k m X)
    (J : Finset (Fin m)) (hJ : J.card = 3) (j₁ j₂ j₃ : Fin m)
    (h0 : J.orderEmbOfFin hJ 0 = j₁) (h1 : J.orderEmbOfFin hJ 1 = j₂)
    (h2 : J.orderEmbOfFin hJ 2 = j₃) :
    (gadgetFamily hgp hm U J hJ).middle = U.cluster j₂ ∧
    (↑(clusterUnion U.cluster (firstTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
      (gadgetFamily hgp hm U J hJ).firstPolytope ∧
    (↑(clusterUnion U.cluster (secondTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
      (gadgetFamily hgp hm U J hJ).secondPolytope := by
  subst h0
  subst h1
  subst h2
  exact ⟨rfl, (clusterGadget hgp hm U _ _ _ _ _).first_region_subset,
    (clusterGadget hgp hm U _ _ _ _ _).second_region_subset⟩

/-- The middle cluster and the two containments (4.8) for every ordered triple. -/
theorem gadgetFamily_spec_triple {k m : ℕ} {X : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hm : 5 ≤ m) (U : UniformSeparatedClusters k m X)
    (j₁ j₂ j₃ : Fin m) (h₁₂ : j₁ < j₂) (h₂₃ : j₂ < j₃)
    (hJ : ({j₁, j₂, j₃} : Finset (Fin m)).card = 3) :
    (gadgetFamily hgp hm U {j₁, j₂, j₃} hJ).middle = U.cluster j₂ ∧
    (↑(clusterUnion U.cluster (firstTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
      (gadgetFamily hgp hm U {j₁, j₂, j₃} hJ).firstPolytope ∧
    (↑(clusterUnion U.cluster (secondTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
      (gadgetFamily hgp hm U {j₁, j₂, j₃} hJ).secondPolytope := by
  classical
  have h₁₃ : j₁ < j₃ := h₁₂.trans h₂₃
  have hmono : StrictMono ![j₁, j₂, j₃] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hmem : ∀ i, ![j₁, j₂, j₃] i ∈ ({j₁, j₂, j₃} : Finset (Fin m)) := by
    intro i
    fin_cases i <;> simp
  have hsorted := Finset.orderEmbOfFin_unique hJ hmem hmono
  exact gadgetFamily_spec hgp hm U _ hJ j₁ j₂ j₃ (congrFun hsorted 0).symm
    (congrFun hsorted 1).symm (congrFun hsorted 2).symm

/-- The projection-order certificates on every subset of the middle cluster, for the gadget
attached to a three-element index set with a named increasing enumeration. -/
theorem gadgetFamily_certificates {k m : ℕ} {X : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hm : 5 ≤ m) (U : UniformSeparatedClusters k m X)
    (J : Finset (Fin m)) (hJ : J.card = 3) (j₂ : Fin m)
    (h1 : J.orderEmbOfFin hJ 1 = j₂) :
    (∀ Y : Finset (Point 3), Y ⊆ U.cluster j₂ →
      Nonempty (ProjectionOrderCertificate (gadgetFamily hgp hm U J hJ).firstPolytope Y
        (Fin 3))) ∧
    (∀ Y : Finset (Point 3), Y ⊆ U.cluster j₂ →
      Nonempty (ProjectionOrderCertificate (gadgetFamily hgp hm U J hJ).secondPolytope Y
        (Fin 3))) := by
  subst h1
  exact ⟨fun Y hY =>
      ⟨((clusterGadget hgp hm U _ _ _ _ _).first_generic Y hY).toProjectionOrderCertificate⟩,
    fun Y hY =>
      ⟨((clusterGadget hgp hm U _ _ _ _ _).second_generic Y hY).toProjectionOrderCertificate⟩⟩

/-- The triple gadget family of a uniform separated cluster family, together with the middle
cluster, the two containments (4.8), and the projection-order certificates of Proposition 2.1
on every subset of the middle cluster, for every ordered triple. -/
theorem exists_tripleGadgetFamily {k m : ℕ} {X : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hm : 5 ≤ m)
    (U : UniformSeparatedClusters k m X) :
    ∃ G : TripleGadgetFamily (Fin m),
      ∀ (j₁ j₂ j₃ : Fin m), j₁ < j₂ → j₂ < j₃ →
        ∀ hJ : ({j₁, j₂, j₃} : Finset (Fin m)).card = 3,
          (G {j₁, j₂, j₃} hJ).middle = U.cluster j₂ ∧
          (↑(clusterUnion U.cluster (firstTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
            (G {j₁, j₂, j₃} hJ).firstPolytope ∧
          (↑(clusterUnion U.cluster (secondTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
            (G {j₁, j₂, j₃} hJ).secondPolytope ∧
          (∀ Y : Finset (Point 3), Y ⊆ U.cluster j₂ →
            Nonempty (ProjectionOrderCertificate (G {j₁, j₂, j₃} hJ).firstPolytope Y
              (Fin 3))) ∧
          (∀ Y : Finset (Point 3), Y ⊆ U.cluster j₂ →
            Nonempty (ProjectionOrderCertificate (G {j₁, j₂, j₃} hJ).secondPolytope Y
              (Fin 3))) := by
  classical
  refine ⟨gadgetFamily hgp hm U, ?_⟩
  intro j₁ j₂ j₃ h₁₂ h₂₃ hJ
  obtain ⟨hmid, hfirst, hsecond⟩ :=
    gadgetFamily_spec_triple hgp hm U j₁ j₂ j₃ h₁₂ h₂₃ hJ
  have hmono : StrictMono ![j₁, j₂, j₃] := by
    intro a b hab
    have h₁₃ : j₁ < j₃ := h₁₂.trans h₂₃
    fin_cases a <;> fin_cases b <;> simp_all
  have hmem : ∀ i, ![j₁, j₂, j₃] i ∈ ({j₁, j₂, j₃} : Finset (Fin m)) := by
    intro i
    fin_cases i <;> simp
  have hsorted := Finset.orderEmbOfFin_unique hJ hmem hmono
  obtain ⟨hcert₁, hcert₂⟩ :=
    gadgetFamily_certificates hgp hm U _ hJ j₂ (congrFun hsorted 1).symm
  exact ⟨hmid, hfirst, hsecond, hcert₁, hcert₂⟩

end

end Erdos651
