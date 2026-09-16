/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (JSP-000527 submission, 2026-09-16).
-/
import JSP527.PZ.Assembly

/-!
# Sections 2--3 of Pohoata--Zakharov, up to the uniform above/below selection

This file runs the geometric pipeline of the Pohoata--Zakharov argument on a large
general-position set `X ⊆ ℝ³` whose vertical projection is injective and planar-generic:
a Pór--Valtr positive-fraction configuration is lifted through the vertical projection,
Proposition 2.5 makes the cells two-separated while keeping strong convex position, the
resulting representatives form a projected convex chain, and a four-uniform Ramsey
selection makes the above/below pattern uniform.

It also records the transport lemma which produces the three projection hypotheses from an
arbitrary general-position set, together with the transfer of convex subsets back.
-/

namespace Erdos651

open Filter Finset Set

noncomputable section

/-- Proposition 2.5 with the underlying lifted configuration retained, so that later steps
can see which planar projection the cells came from. -/
theorem exists_separatedPositiveFractionClusters_source
    {k : ℕ} {X : Finset (Point 3)}
    (C : LiftedPositiveFractionConfiguration k X)
    (hgp : InGeneralPosition 3 X)
    (hlarge : 2 ^ (40 * k + k ^ 3) ≤ X.card) :
    ∃ D : SeparatedPositiveFractionClusters k X, D.source = C := by
  classical
  have hcell : ∀ i, 2 ^ (k ^ 3) ≤ (C.cell i).card := by
    intro i
    have hmul : 2 ^ (40 * k) * 2 ^ (k ^ 3) ≤ 2 ^ (40 * k) * (C.cell i).card := by
      calc
        2 ^ (40 * k) * 2 ^ (k ^ 3) = 2 ^ (40 * k + k ^ 3) := (pow_add 2 _ _).symm
        _ ≤ X.card := hlarge
        _ ≤ 2 ^ (40 * k) * (C.cell i).card := C.cell_density i
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  have hallgp : InGeneralPosition 3 (allClusters C.cell) := hgp.mono C.allCells_subset
  obtain ⟨Y, hYC, hYtwo, hYloss⟩ :=
    exists_twoSeparated_subclusters C.cell C.cell_disjoint hcell hallgp
  have hYdensity : ∀ i, X.card ≤ 2 ^ (40 * k + k ^ 3) * (Y i).card := by
    intro i
    calc
      X.card ≤ 2 ^ (40 * k) * (C.cell i).card := C.cell_density i
      _ ≤ 2 ^ (40 * k) * (2 ^ (k ^ 3) * (Y i).card) := Nat.mul_le_mul_left _ (hYloss i)
      _ = 2 ^ (40 * k + k ^ 3) * (Y i).card := by
        rw [pow_add]
        ring
  have hYne : ∀ i, (Y i).Nonempty := by
    intro i
    rw [Finset.nonempty_iff_ne_empty]
    intro hi
    have hd := hYdensity i
    rw [hi] at hd
    simp only [Finset.card_empty, mul_zero, Nat.le_zero] at hd
    have hpos : 0 < X.card := lt_of_lt_of_le (by positivity) hlarge
    omega
  exact ⟨{
    source := C
    cluster := Y
    cluster_subset_source := hYC
    twoSeparated := hYtwo
    strongConvex := C.strong_convex.mono hYC
    density := hYdensity
    nonempty := hYne }, rfl⟩

/-- The two-separated positive-fraction clusters coming from the vertical projection,
together with the projected-convex-chain property of their representatives. -/
theorem exists_separatedPositiveFractionClusters_projectedChain
    {k : ℕ} (hk : 4 ≤ k)
    {X : Finset (Point 3)} (hgp : InGeneralPosition 3 X)
    (hproj : Set.InjOn verticalProjection X)
    (hgp2 : InGeneralPosition 2 (X.image verticalProjection))
    (hcard : 2 ^ (40 * k + k ^ 3) ≤ X.card) :
    ∃ C : SeparatedPositiveFractionClusters k X,
      IsProjectedConvexChain C.representative Finset.univ := by
  classical
  have hexp : 2 ≤ 40 * k + k ^ 3 := le_trans (by omega) (Nat.le_add_right _ _)
  have hXcard : 4 ≤ X.card := by
    refine le_trans ?_ hcard
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (40 * k + k ^ 3) := Nat.pow_le_pow_right (by norm_num) hexp
  have hcard40 : 2 ^ (40 * k) ≤ X.card :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)) hcard
  obtain ⟨P⟩ := exists_orderedStrongPositiveFractionConfiguration k hk
    (X.image verticalProjection)
    (by rw [Finset.card_image_of_injOn hproj]; exact hcard40) hgp2
  obtain ⟨C, hCvert⟩ : ∃ C : LiftedPositiveFractionConfiguration k X,
      ⇑C.projection = verticalProjection := by
    refine ⟨⟨verticalProjectionAffine, ?_, ?_⟩, coe_verticalProjectionAffine⟩
    · simpa only [coe_verticalProjectionAffine] using hproj
    · simpa only [coe_verticalProjectionAffine] using P
  obtain ⟨D, hD⟩ := exists_separatedPositiveFractionClusters_source C hgp hcard
  subst hD
  refine ⟨D, ?_⟩
  apply D.source.planar.isProjectedConvexChain
  · intro i
    rw [← hCvert]
    exact D.representative_projection_mem i
  · intro i₀ i₁ i₂ i₃ h₀₁ h₁₂ h₂₃
    exact D.representative_four_independent hXcard hgp i₀ i₁ i₂ i₃ h₀₁ h₁₂ h₂₃

/-- Sections 2–3 of Pohoata–Zakharov up to the uniform above/below selection: a large
general-position set in `ℝ³` with injective, planar-general-position vertical projection
carries `m` two-separated, strongly convex clusters whose representatives form a projected
convex chain with uniform above/below pattern. -/
theorem exists_uniformSeparatedClusters {k m : ℕ} (hk : 4 ≤ k)
    (hkm : uniformRamseySequence 4 m ≤ k)
    {X : Finset (Point 3)} (hgp : InGeneralPosition 3 X)
    (hproj : Set.InjOn verticalProjection X)
    (hgp2 : InGeneralPosition 2 (X.image verticalProjection))
    (hcard : 2 ^ (40 * k + k ^ 3) ≤ X.card) :
    Nonempty (UniformSeparatedClusters k m X) := by
  classical
  obtain ⟨C, hchain⟩ :=
    exists_separatedPositiveFractionClusters_projectedChain hk hgp hproj hgp2 hcard
  obtain ⟨H, -, hHcard, huniform⟩ :=
    exists_uniformAboveBelow_subchain_of_ramseySequence C.representative Finset.univ
      (by simpa using hkm) hchain
  exact ⟨C.selectUniform H hHcard hchain huniform⟩

/-- Every general-position set with at least four points has an affine image which is
generic for the vertical projection, and convex subsets of that image transport back. -/
theorem exists_generic_image {X : Finset (Point 3)} (hgp : InGeneralPosition 3 X)
    (hXcard : 4 ≤ X.card) :
    ∃ e : Point 3 ≃ᵃ[ℝ] Point 3,
      InGeneralPosition 3 (X.image e) ∧
      Set.InjOn verticalProjection (X.image e) ∧
      InGeneralPosition 2 ((X.image e).image verticalProjection) ∧
      (X.image e).card = X.card ∧
      (∀ n, ContainsConvexSubset 3 n (X.image e) → ContainsConvexSubset 3 n X) := by
  classical
  obtain ⟨e, hgpe, hinj, hgp2⟩ := exists_vertical_generic_affineEquiv hgp hXcard
  refine ⟨e, hgpe, hinj, hgp2, Finset.card_image_of_injective X e.injective, ?_⟩
  rintro n ⟨Y, hYsub, hYcard, hYconv⟩
  refine ⟨Y.image e.symm, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hYsub hy)
    simpa using hx
  · rw [Finset.card_image_of_injective _ e.symm.injective, hYcard]
  · exact (AffineEquiv.inConvexPosition_image_iff e.symm Y).mpr hYconv

end

end Erdos651
