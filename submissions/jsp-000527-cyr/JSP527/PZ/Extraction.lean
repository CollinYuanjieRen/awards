/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (JSP-000527 submission, 2026-09-16).
-/
import JSP527.External.Erdos651
import JSP527.PZ.Clusters
import JSP527.PZ.Gadgets

/-!
# The unconditional extraction step of Pohoata--Zakharov

This file closes the end of Section 3 of Pohoata--Zakharov.  A large general-position set in
`ℝ³` is first moved by an affine equivalence into a position generic for the vertical
projection, then carries `m = pzAboveBelowScale n` two-separated, strongly convex clusters with
a uniform above/below pattern.  Proposition 3.1 attaches two trihedral polyhedra to every
ordered triple of clusters; the triple Ramsey step of the assembly makes the resulting
Dilworth colour constant on a clique of `t + 1 = 2q + 1` indices.

The alternating triples of that clique (`alternatingTriple`) then give `q` middle clusters,
each carrying a free set for the *same* polyhedron.  For the red colour the clique is read
left to right, for the blue colour right to left; in both cases the middle index of every
other alternating triple lies in the region of (4.8) covered by the selected polyhedron, so
the free sets are mutually contained in each other's backgrounds.  This is exactly an
`AlternatingFreeFamily`, and `containsConvexSubset_of_sourceEnvelope` converts it into a
convex subset of size `n`.
-/

namespace Erdos651

open Filter Finset Set

noncomputable section

/-- The alternating free family extracted from a monochromatic triple clique.  The data is
presented abstractly: `a₁ r < a₂ r < a₃ r` is the sorted `r`-th alternating triple, `b` is the
Ramsey colour, and `hother` records that every other middle index lies in the region of (4.8)
belonging to the selected polyhedron. -/
theorem exists_alternatingFreeFamily {k m q : ℕ} {X : Finset (Point 3)}
    (U : UniformSeparatedClusters k m X) (G : TripleGadgetFamily (Fin m))
    (hspec : ∀ j₁ j₂ j₃ : Fin m, j₁ < j₂ → j₂ < j₃ →
      ∀ hJ : ({j₁, j₂, j₃} : Finset (Fin m)).card = 3,
        (G {j₁, j₂, j₃} hJ).middle = U.cluster j₂ ∧
        (↑(clusterUnion U.cluster (firstTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
          (G {j₁, j₂, j₃} hJ).firstPolytope ∧
        (↑(clusterUnion U.cluster (secondTrihedralIndices j₁ j₂ j₃)) : Set (Point 3)) ⊆
          (G {j₁, j₂, j₃} hJ).secondPolytope ∧
        (∀ Y : Finset (Point 3), Y ⊆ U.cluster j₂ →
          Nonempty (ProjectionOrderCertificate (G {j₁, j₂, j₃} hJ).firstPolytope Y (Fin 3))) ∧
        (∀ Y : Finset (Point 3), Y ⊆ U.cluster j₂ →
          Nonempty (ProjectionOrderCertificate (G {j₁, j₂, j₃} hJ).secondPolytope Y (Fin 3))))
    (b : Bool) (jb : Fin (2 * q + 1) ↪ Fin m) (a₁ a₂ a₃ : Fin q → Fin m)
    (h₁₂ : ∀ r : Fin q, a₁ r < a₂ r) (h₂₃ : ∀ r : Fin q, a₂ r < a₃ r)
    (htriple : ∀ r : Fin q, alternatingTriple jb r = {a₁ r, a₂ r, a₃ r})
    (h₂inj : Function.Injective a₂)
    (hother : ∀ r r' : Fin q, r ≠ r' →
      a₂ r' ∈ (if b then firstTrihedralIndices (a₁ r) (a₂ r) (a₃ r)
        else secondTrihedralIndices (a₁ r) (a₂ r) (a₃ r)))
    (hfree : ∀ r : Fin q, ∃ Z : Finset (Point 3),
      Z ⊆ (alternatingGadget G jb r).middle ∧
      (alternatingGadget G jb r).middle.card ≤ Z.card * Z.card ∧
      PFree (if b then (alternatingGadget G jb r).firstPolytope
        else (alternatingGadget G jb r).secondPolytope) Z) :
    ∃ F : AlternatingFreeFamily q X,
      ∀ r : Fin q, X.card ≤ 2 ^ (40 * k + k ^ 3) * (F.middle r).card := by
  classical
  have hGcongr : ∀ (S S' : Finset (Fin m)) (hS : S.card = 3) (hS' : S'.card = 3),
      S = S' → G S hS = G S' hS' := by
    rintro S S' hS hS' rfl
    rfl
  have hcard3 : ∀ r : Fin q, ({a₁ r, a₂ r, a₃ r} : Finset (Fin m)).card = 3 := by
    intro r
    rw [← htriple r]
    exact alternatingTriple_card jb r
  have hgad : ∀ r : Fin q, alternatingGadget G jb r = G {a₁ r, a₂ r, a₃ r} (hcard3 r) :=
    fun r => hGcongr _ _ _ _ (htriple r)
  have hmid : ∀ r : Fin q, (alternatingGadget G jb r).middle = U.cluster (a₂ r) := by
    intro r
    rw [hgad r]
    exact (hspec _ _ _ (h₁₂ r) (h₂₃ r) (hcard3 r)).1
  obtain ⟨bg, hbg⟩ : ∃ bg : Fin q → Set (Point 3), ∀ r : Fin q,
      bg r = if b then (alternatingGadget G jb r).firstPolytope
        else (alternatingGadget G jb r).secondPolytope := ⟨_, fun _ => rfl⟩
  obtain ⟨idx, hidx⟩ : ∃ idx : Fin q → Finset (Fin m), ∀ r : Fin q,
      idx r = if b then firstTrihedralIndices (a₁ r) (a₂ r) (a₃ r)
        else secondTrihedralIndices (a₁ r) (a₂ r) (a₃ r) := ⟨_, fun _ => rfl⟩
  have hsub : ∀ r : Fin q,
      (↑(clusterUnion U.cluster (idx r)) : Set (Point 3)) ⊆ bg r := by
    intro r
    obtain ⟨-, hfirst, hsecond, -, -⟩ := hspec _ _ _ (h₁₂ r) (h₂₃ r) (hcard3 r)
    rw [hidx r, hbg r]
    cases b
    · simpa [hgad r] using hsecond
    · simpa [hgad r] using hfirst
  have hcert : ∀ (r : Fin q) (Y : Finset (Point 3)), Y ⊆ U.cluster (a₂ r) →
      Nonempty (ProjectionOrderCertificate (bg r) Y (Fin 3)) := by
    intro r Y hY
    obtain ⟨-, -, -, hc₁, hc₂⟩ := hspec _ _ _ (h₁₂ r) (h₂₃ r) (hcard3 r)
    rw [hbg r]
    cases b
    · simpa [hgad r] using hc₂ Y hY
    · simpa [hgad r] using hc₁ Y hY
  choose Z hZmid hZcard hZfree using hfree
  have hZcluster : ∀ r : Fin q, Z r ⊆ U.cluster (a₂ r) := by
    intro r
    rw [← hmid r]
    exact hZmid r
  refine ⟨{ middle := fun r => U.cluster (a₂ r)
            background := bg
            freeSet := Z
            middle_subset := fun r => U.cluster_subset (a₂ r)
            free_subset_middle := hZcluster
            middle_card_le_free_square := fun r => by rw [← hmid r]; exact hZcard r
            free_disjoint := ?_
            free := fun r => by rw [hbg r]; exact hZfree r
            certificate := fun r => Classical.choice (hcert r (Z r) (hZcluster r))
            other_free_subset := ?_ }, fun r => U.density (a₂ r)⟩
  · intro r _ r' _ hne
    exact (U.strongConvex.pairwiseDisjoint fun h => hne (h₂inj h)).mono
      (hZcluster r) (hZcluster r')
  · intro r r' hne
    refine subset_trans ?_ (hsub r)
    intro x hx
    have hxc : x ∈ U.cluster (a₂ r') := hZcluster r' hx
    have hmem : a₂ r' ∈ idx r := by
      rw [hidx r]
      exact hother r r' hne
    simp only [clusterUnion, Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨a₂ r', by simpa using hmem, hxc⟩

/-- The extraction theorem: for every large `n`, a general-position set in `ℝ³` beyond the
source envelope `t ^ (77 n / t)` at scale `t = pzSourceScale n` contains `n` points in convex
position. -/
theorem pohoataZakharov_forces_eventually : ∀ᶠ n : ℕ in atTop,
    ∀ X : Finset (Point 3), InGeneralPosition 3 X →
      (pzSourceScale n : ℝ) ^ ((77 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ)) < (X.card : ℝ) →
      ContainsConvexSubset 3 n X := by
  classical
  filter_upwards [pzQuarterRoot_tendsto_atTop.eventually_ge_atTop 4,
    pzAboveBelowScale_tendsto_atTop.eventually_ge_atTop 5,
    pzSourceScale_tendsto_atTop.eventually_ge_atTop 3,
    eventually_uniformRamseySequence_aboveBelowScale_le_quarterRoot,
    eventually_ge_atTop 2] with n hk4 hm5 ht3 hkm hn2
  intro X hgp hlarge
  set q := (pzSourceScale n + 1) / 2 with hqdef
  have hq2 : pzSourceScale n = 2 * q := by
    obtain ⟨s, hs⟩ := pzSourceScale_even n
    omega
  -- numerical preliminaries
  have htk := pzSourceScale_le_quarterRoot n
  have hk4' := pzQuarterRoot_pow_four_le n
  have hkle : pzQuarterRoot n ≤ pzQuarterRoot n ^ 4 := by
    simpa using Nat.pow_le_pow_right (show 1 ≤ pzQuarterRoot n by omega) (show 1 ≤ 4 by omega)
  have htn : pzSourceScale n ≤ n := htk.trans (hkle.trans hk4')
  have ht1 : (1 : ℝ) ≤ (pzSourceScale n : ℝ) := by
    have h : (1 : ℕ) ≤ pzSourceScale n := by omega
    exact_mod_cast h
  have hexp : (41 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ) ≤
      (77 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have htpos : (0 : ℝ) < (pzSourceScale n : ℝ) := by linarith
    gcongr
    norm_num
  have henv : ((2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) : ℕ) : ℝ) ≤
      (pzSourceScale n : ℝ) ^ ((77 : ℝ) * (n : ℝ) / (pzSourceScale n : ℝ)) :=
    (positiveFractionLoss_le_sourceEnvelope n (by omega)).trans
      (Real.rpow_le_rpow_of_exponent_le ht1 hexp)
  have hcardX : 2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) ≤ X.card := by
    have h := henv.trans_lt hlarge
    exact_mod_cast h.le
  have hX4 : 4 ≤ X.card := by
    refine le_trans ?_ hcardX
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) :=
          Nat.pow_le_pow_right (by norm_num) (le_trans (by omega) (Nat.le_add_right _ _))
  -- the geometric pipeline
  obtain ⟨e, hgpe, hinj, hgp2, hcarde, htrans⟩ := exists_generic_image hgp hX4
  have hcardX' : 2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) ≤ (X.image e).card := by
    rw [hcarde]; exact hcardX
  obtain ⟨U⟩ := exists_uniformSeparatedClusters (k := pzQuarterRoot n)
    (by omega) hkm hgpe hinj hgp2 hcardX'
  obtain ⟨G, hG⟩ := exists_tripleGadgetFamily hgpe hm5 U
  -- the triple Ramsey step
  obtain ⟨H, -, hHcard, hHmono⟩ := pzSourceScale_tripleRamsey n
    (Finset.univ : Finset (Fin (pzAboveBelowScale n))) (by omega) (by simp)
    (fun J => if hJ : J.card = 3 then (G J hJ).color else false)
  obtain ⟨bcol, hb⟩ := hHmono
  have hHcard2 : H.card = 2 * q + 1 := by omega
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : Fin (2 * q + 1) ↪o Fin (pzAboveBelowScale n), ∀ p, e₀ p ∈ H :=
    ⟨H.orderEmbOfFin hHcard2, H.orderEmbOfFin_mem hHcard2⟩
  have hmono : ∀ J : Finset (Fin (pzAboveBelowScale n)), J ⊆ H → ∀ hJ : J.card = 3,
      (G J hJ).color = bcol := by
    intro J hJH hJ
    have h : (if hJ' : J.card = 3 then (G J hJ').color else false) = bcol := hb J hJH hJ
    rw [dite_eq_left_of_eq_true (eq_true hJ)] at h
    exact h
  have hlt : ∀ p p' : Fin (2 * q + 1), p.1 < p'.1 → e₀ p < e₀ p' :=
    fun p p' h => e₀.lt_iff_lt.mpr h
  have hle : ∀ p p' : Fin (2 * q + 1), p.1 ≤ p'.1 → e₀ p ≤ e₀ p' :=
    fun p p' h => e₀.le_iff_le.mpr h
  have hinj₀ : ∀ p p' : Fin (2 * q + 1), e₀ p = e₀ p' → p.1 = p'.1 :=
    fun p p' h => congrArg Fin.val (e₀.injective h)
  -- the alternating free family, red clique read forwards and blue clique read backwards
  obtain ⟨F, hFdens⟩ : ∃ F : AlternatingFreeFamily q (X.image e),
      ∀ r : Fin q, (X.image e).card ≤
        2 ^ (40 * pzQuarterRoot n + pzQuarterRoot n ^ 3) * (F.middle r).card := by
    cases bcol
    · refine exists_alternatingFreeFamily U G hG false
        ((⟨Fin.rev, Fin.rev_injective⟩ : Fin (2 * q + 1) ↪ Fin (2 * q + 1)).trans
          e₀.toEmbedding)
        (fun _ => e₀ (Fin.rev (alternatingLastPosition q)))
        (fun r => e₀ (Fin.rev (alternatingMiddlePosition r)))
        (fun r => e₀ (Fin.rev (alternatingLeftPosition r))) ?_ ?_ ?_ ?_ ?_ ?_
      · intro r
        have hr := r.isLt
        refine hlt _ _ ?_
        simp only [Fin.val_rev, alternatingLastPosition, alternatingMiddlePosition]
        omega
      · intro r
        have hr := r.isLt
        refine hlt _ _ ?_
        simp only [Fin.val_rev, alternatingMiddlePosition, alternatingLeftPosition]
        omega
      · intro r
        simp only [alternatingTriple]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · intro r r' h
        have hr := r.isLt
        have hr' := r'.isLt
        have h' := hinj₀ _ _ h
        simp only [Fin.val_rev, alternatingMiddlePosition] at h'
        exact Fin.ext (by omega)
      · intro r r' hne
        have hr := r.isLt
        have hr' := r'.isLt
        have hne' : r.1 ≠ r'.1 := fun h => hne (Fin.ext h)
        simp only [Bool.false_eq_true, ite_false, mem_secondTrihedralIndices]
        rcases lt_or_gt_of_ne hne' with h | h
        · left
          constructor
          · refine hle _ _ ?_
            simp only [Fin.val_rev, alternatingMiddlePosition, alternatingLastPosition]
            omega
          · refine hlt _ _ ?_
            simp only [Fin.val_rev, alternatingMiddlePosition]
            omega
        · right
          refine hlt _ _ ?_
          simp only [Fin.val_rev, alternatingMiddlePosition, alternatingLeftPosition]
          omega
      · exact exists_alternating_free_subsets_of_monochromatic_clique G H
          ((⟨Fin.rev, Fin.rev_injective⟩ : Fin (2 * q + 1) ↪ Fin (2 * q + 1)).trans
            e₀.toEmbedding) (fun p => he₀ _) false hmono
    · refine exists_alternatingFreeFamily U G hG true e₀.toEmbedding
        (fun r => e₀ (alternatingLeftPosition r))
        (fun r => e₀ (alternatingMiddlePosition r))
        (fun _ => e₀ (alternatingLastPosition q)) ?_ ?_ ?_ ?_ ?_ ?_
      · intro r
        have hr := r.isLt
        refine hlt _ _ ?_
        simp only [alternatingLeftPosition, alternatingMiddlePosition]
        omega
      · intro r
        have hr := r.isLt
        refine hlt _ _ ?_
        simp only [alternatingMiddlePosition, alternatingLastPosition]
        omega
      · intro r
        rfl
      · intro r r' h
        have hr := r.isLt
        have hr' := r'.isLt
        have h' := hinj₀ _ _ h
        simp only [alternatingMiddlePosition] at h'
        exact Fin.ext (by omega)
      · intro r r' hne
        have hr := r.isLt
        have hr' := r'.isLt
        have hne' : r.1 ≠ r'.1 := fun h => hne (Fin.ext h)
        simp only [reduceIte, mem_firstTrihedralIndices]
        rcases lt_or_gt_of_ne hne' with h | h
        · right
          constructor
          · refine hlt _ _ ?_
            simp only [alternatingMiddlePosition]
            omega
          · refine hle _ _ ?_
            simp only [alternatingMiddlePosition, alternatingLastPosition]
            omega
        · left
          refine hlt _ _ ?_
          simp only [alternatingMiddlePosition, alternatingLeftPosition]
          omega
      · exact exists_alternating_free_subsets_of_monochromatic_clique G H _
          (fun p => he₀ p) true hmono
  -- conclude
  refine htrans n (F.containsConvexSubset_of_sourceEnvelope hn2 ht3 htn hFdens ?_)
  rw [hcarde]
  exact hlarge

end

end Erdos651
