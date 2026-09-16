/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
import JSP527.PZ.Main

/-!
# Erdős Problem 651 in every dimension `d ≥ 3`

A generic linear projection `Point (d + 2) → Point (d + 1)` is injective on a fixed finite
general-position set and carries it to a general-position set: the direction of the projection
is chosen outside the finitely many proper subspaces spanned by the differences of the small
subsets, which is possible because a real vector space is not a finite union of proper
subspaces.  Convex position pulls back along any affine map that is injective on the set, so a
convex-position certificate found in dimension `d + 1` lifts to dimension `d + 2`.

This makes the Erdős–Szekeres numbers decrease with the dimension, up to the additive constant
forced by sets that are too small for the projection argument: `f_{d+1}(n) ≤ max (f_d(n)) (d+3)`
for `d ≥ 1`.  The constant is harmless asymptotically, so the Pohoata–Zakharov subexponential
bound and the refutation of Erdős's conjectured exponential lower bound hold in every
dimension `d ≥ 3`.
-/

open Erdos651 Filter

namespace PohoataZakharov

section GenericProjection

variable {d : ℕ}

/-- The fibre-selection finset of a subset of an image maps exactly onto that subset. -/
theorem image_filter_mem {e : ℕ} {X : Finset (Point d)} {T : Finset (Point e)}
    (π : Point d → Point e) (hT : T ⊆ X.image π) :
    (X.filter fun x ↦ π x ∈ T).image π = T := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hx).2
  · intro y hy
    obtain ⟨x, hxX, hxy⟩ := Finset.mem_image.mp (hT hy)
    subst hxy
    exact Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hxX, hy⟩, rfl⟩

/-- In a `(d + 2)`-dimensional general-position set with at least `d + 3` points, every subset
of at most `d + 2` points is affinely independent.  The cardinality hypothesis is necessary
because `InGeneralPosition (d + 2)` only directly constrains `(d + 3)`-point subsets. -/
theorem affineIndependent_of_card_le_of_inGeneralPosition {X S : Finset (Point (d + 2))}
    (hgp : InGeneralPosition (d + 2) X) (hXcard : d + 3 ≤ X.card) (hSX : S ⊆ X)
    (hScard : S.card ≤ d + 2) :
    AffineIndependent ℝ (fun p : S ↦ (p : Point (d + 2))) := by
  obtain ⟨T, hST, hTX, hTcard⟩ :=
    Finset.exists_subsuperset_card_eq hSX (by omega : S.card ≤ d + 3) hXcard
  have hT : AffineIndependent ℝ (fun p : T ↦ (p : Point (d + 2))) := hgp T hTX (by omega)
  exact hT.mono (by
    intro p hp
    exact hST hp)

/-- A finite general-position set of at least `d + 3` points in `Point (d + 2)` admits a
generic affine projection to `Point (d + 1)` which is injective on the set and whose image is
again in general position. -/
theorem exists_generic_projection {X : Finset (Point (d + 2))}
    (hgp : InGeneralPosition (d + 2) X) (hXcard : d + 3 ≤ X.card) :
    ∃ π : Point (d + 2) →ᵃ[ℝ] Point (d + 1),
      Set.InjOn π X ∧ InGeneralPosition (d + 1) (X.image π) := by
  classical
  have hdim : Module.finrank ℝ (Point (d + 2)) = d + 2 := by simp [Point]
  let I := X.powerset.filter fun S ↦ S.card ≤ d + 2
  let bad : I → Submodule ℝ (Point (d + 2)) :=
    fun S ↦ vectorSpan ℝ (S.1 : Set (Point (d + 2)))
  have hbad : ∀ S : I, bad S ≠ ⊤ := by
    intro S htop
    have hSX : S.1 ⊆ X := Finset.mem_powerset.mp (Finset.mem_filter.mp S.2).1
    have hScard : S.1.card ≤ d + 2 := (Finset.mem_filter.mp S.2).2
    have hAI := affineIndependent_of_card_le_of_inGeneralPosition hgp hXcard hSX hScard
    by_cases hSne : S.1.Nonempty
    · let _ : Nonempty S.1 := Finset.nonempty_coe_sort.mpr hSne
      have hfin := hAI.finrank_vectorSpan_add_one
      have hrange :
          Set.range (fun p : S.1 ↦ (p : Point (d + 2))) = (S.1 : Set (Point (d + 2))) := by
        ext x
        simp
      rw [hrange] at hfin
      change vectorSpan ℝ (S.1 : Set (Point (d + 2))) = ⊤ at htop
      rw [htop, finrank_top, hdim, Fintype.card_coe] at hfin
      omega
    · have hSempty : S.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
      simp [bad, hSempty] at htop
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  have hv0 : v ≠ 0 := by
    intro hvzero
    subst v
    let E : I := ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset X, by simp⟩⟩
    exact hv E (by simp [bad])
  let K : Submodule ℝ (Point (d + 2)) := ℝ ∙ v
  have hKfin : Module.finrank ℝ K = 1 := finrank_span_singleton hv0
  have hQfin : Module.finrank ℝ (Point (d + 2) ⧸ K) = d + 1 := by
    have hsum := K.finrank_quotient_add_finrank
    rw [hKfin] at hsum
    omega
  let e : (Point (d + 2) ⧸ K) ≃ₗ[ℝ] Point (d + 1) := LinearEquiv.ofFinrankEq _ _ (by
    rw [hQfin]
    simp [Point])
  let L : Point (d + 2) →ₗ[ℝ] Point (d + 1) := e.toLinearMap.comp K.mkQ
  let π : Point (d + 2) →ᵃ[ℝ] Point (d + 1) := L.toAffineMap
  have hker : LinearMap.ker L = K := by
    ext z
    simp [L, K]
  have hpreserve (S : Finset (Point (d + 2))) (hSX : S ⊆ X) (hScard : S.card ≤ d + 2) :
      AffineIndependent ℝ (fun z : S ↦ π (z : Point (d + 2))) := by
    have hAI := affineIndependent_of_card_le_of_inGeneralPosition hgp hXcard hSX hScard
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst S
      exact affineIndependent_of_subsingleton ℝ _
    let _ : Nonempty S := Finset.nonempty_coe_sort.mpr hS
    let a : S := ⟨hS.choose, hS.choose_spec⟩
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ a] at hAI ⊢
    simp_rw [← π.linearMap_vsub]
    apply hAI.map
    rw [show LinearMap.ker π.linear = K by simpa [π] using hker]
    have hspan_le :
        Submodule.span ℝ
            (Set.range fun z : {z : S // z ≠ a} ↦
              (z.1 : Point (d + 2)) -ᵥ (a : Point (d + 2))) ≤
          vectorSpan ℝ (S : Set (Point (d + 2))) := by
      rw [Submodule.span_le]
      rintro w ⟨z, rfl⟩
      exact vsub_mem_vectorSpan ℝ z.1.2 a.2
    let SS : I := ⟨S, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hSX, hScard⟩⟩
    have hvS : v ∉ vectorSpan ℝ (S : Set (Point (d + 2))) := by simpa [bad] using hv SS
    exact Disjoint.mono_left hspan_le (Submodule.disjoint_span_singleton_of_notMem hvS)
  have hπinj : Set.InjOn π X := by
    intro x hx y hy hxy
    by_contra hne
    let S : Finset (Point (d + 2)) := {x, y}
    have hSX : S ⊆ X := by
      intro z hz
      have hz' : z = x ∨ z = y := by simpa [S] using hz
      rcases hz' with rfl | rfl
      · simpa using hx
      · simpa using hy
    have hScard : S.card ≤ d + 2 := by
      have hle : S.card ≤ ({y} : Finset (Point (d + 2))).card + 1 := by
        simpa [S] using Finset.card_insert_le x ({y} : Finset (Point (d + 2)))
      simp only [Finset.card_singleton] at hle
      omega
    have hAI := hpreserve S hSX hScard
    have hxyS : x ∈ S := by simp [S]
    have hyyS : y ∈ S := by simp [S]
    exact hne (congrArg Subtype.val
      (hAI.injective (show π (⟨x, hxyS⟩ : S) = π (⟨y, hyyS⟩ : S) from hxy)))
  refine ⟨π, hπinj, ?_⟩
  intro T hTsub hTcard
  let S : Finset (Point (d + 2)) := X.filter fun x ↦ π x ∈ T
  have hSX : S ⊆ X := fun x hx ↦ (Finset.mem_filter.mp hx).1
  have hImage : S.image π = T := image_filter_mem _ hTsub
  have hπinjS : Set.InjOn π S := hπinj.mono hSX
  have hScard : S.card = d + 2 := by
    have h1 : S.card = T.card := by
      rw [← Finset.card_image_of_injOn hπinjS, hImage]
    omega
  have hAIS := hpreserve S hSX (by omega)
  have hpreExists (y : T) : ∃ x ∈ S, π x = (y : Point (d + 1)) := by
    have hy : (y : Point (d + 1)) ∈ S.image π := by
      rw [hImage]
      exact y.2
    exact Finset.mem_image.mp hy
  choose pre hpreS hpre using hpreExists
  let emb : T ↪ S :=
    ⟨fun y ↦ ⟨pre y, hpreS y⟩, fun y z hyz ↦ Subtype.ext (by
      calc
        (y : Point (d + 1)) = π (pre y) := (hpre y).symm
        _ = π (pre z) := congrArg π (congrArg Subtype.val hyz)
        _ = (z : Point (d + 1)) := hpre z)⟩
  have hemb : (fun z : S ↦ π (z : Point (d + 2))) ∘ emb =
      fun z : T ↦ (z : Point (d + 1)) := by
    funext y
    exact hpre y
  rw [← hemb]
  exact hAIS.comp_embedding emb

end GenericProjection

section Transport

/-- A convex-position subset of the image of an affine map that is injective on `X` pulls back
to a convex-position subset of `X` of the same cardinality. -/
theorem containsConvexSubset_of_image {d e n : ℕ} {X : Finset (Point d)}
    (π : Point d →ᵃ[ℝ] Point e) (hπ : Set.InjOn π X)
    (h : ContainsConvexSubset e n (X.image π)) : ContainsConvexSubset d n X := by
  classical
  obtain ⟨Y, hYsub, hYcard, hYconv⟩ := h
  refine ⟨X.filter fun x ↦ π x ∈ Y, Finset.filter_subset _ _, ?_, ?_⟩
  · calc (X.filter fun x ↦ π x ∈ Y).card
        = ((X.filter fun x ↦ π x ∈ Y).image π).card :=
          (Finset.card_image_of_injOn (hπ.mono (Finset.filter_subset _ _))).symm
      _ = Y.card := congrArg Finset.card (image_filter_mem _ hYsub)
      _ = n := hYcard
  · refine InConvexPosition.of_image_affineMap π (hπ.mono (Finset.filter_subset _ _)) ?_
    rw [image_filter_mem (π := (π : Point d → Point e)) hYsub]
    exact hYconv

/-- The forcing property transfers from dimension `d + 1` to dimension `d + 2`, provided the
threshold is large enough for the generic projection to exist. -/
theorem forcesConvexSubset_succ {d n N : ℕ} (hN : d + 3 ≤ N)
    (h : ForcesConvexSubset (d + 1) n N) : ForcesConvexSubset (d + 2) n N := by
  intro X hNX hgp
  obtain ⟨π, hinj, himg⟩ := exists_generic_projection hgp (by omega)
  refine containsConvexSubset_of_image π hinj (h _ ?_ himg)
  rw [Finset.card_image_of_injOn hinj]
  exact hNX

/-- Existence of the Erdős–Szekeres number transfers from dimension `d + 1` to `d + 2`. -/
theorem hasErdosSzekeresNumber_succ {d n : ℕ} (h : HasErdosSzekeresNumber (d + 1) n) :
    HasErdosSzekeresNumber (d + 2) n := by
  obtain ⟨N, hN⟩ := h
  exact ⟨max N (d + 3), forcesConvexSubset_succ (le_max_right _ _) (hN.mono (le_max_left _ _))⟩

/-- The Erdős–Szekeres number does not increase with the dimension, up to the additive
constant forced by point sets too small to project generically. -/
theorem erdosSzekeresNumber_succ_le {d n : ℕ} (h : HasErdosSzekeresNumber (d + 1) n) :
    erdosSzekeresNumber (d + 2) n ≤ max (erdosSzekeresNumber (d + 1) n) (d + 3) :=
  erdosSzekeresNumber_le
    (forcesConvexSubset_succ (le_max_right _ _) ((erdosSzekeresNumber_forces h).mono
      (le_max_left _ _)))

/-- The Erdős–Szekeres number exists in every dimension `d ≥ 3`. -/
theorem hasErdosSzekeresNumber_add_three (d n : ℕ) : HasErdosSzekeresNumber (d + 3) n := by
  induction d with
  | zero => exact hasErdosSzekeresNumber_three n
  | succ d ih => exact hasErdosSzekeresNumber_succ (d := d + 2) ih

/-- The Erdős–Szekeres number in dimension `d + 3` is bounded by the three-dimensional one, up
to an additive constant depending only on the dimension. -/
theorem erdosSzekeresNumber_add_three_le (d n : ℕ) :
    erdosSzekeresNumber (d + 3) n ≤ max (erdosSzekeresNumber 3 n) (d + 4) := by
  induction d with
  | zero => exact le_max_left _ _
  | succ d ih =>
    have h : erdosSzekeresNumber (d + 4) n ≤ max (erdosSzekeresNumber (d + 3) n) (d + 5) :=
      erdosSzekeresNumber_succ_le (d := d + 2) (hasErdosSzekeresNumber_add_three d n)
    have hg : erdosSzekeresNumber (d + 1 + 3) n = erdosSzekeresNumber (d + 4) n := rfl
    rw [hg]
    omega

end Transport

section Asymptotics

/-- Pohoata–Zakharov in every dimension `d ≥ 3`: `f_d(n) ≤ 2 ^ (o(n))`. -/
theorem erdos_651_subexponential_all_dimensions (d : ℕ) :
    Erdos651.HasSubexponentialUpperBound (Erdos651.erdosSzekeresNumber (d + 3)) := by
  intro ε hε
  have htend : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ (ε * (n : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
      (Tendsto.const_mul_atTop hε tendsto_natCast_atTop_atTop)
  filter_upwards [erdos_651_subexponential ε hε, htend.eventually_ge_atTop ((d : ℝ) + 4)]
    with n h3 hc
  have hle : (erdosSzekeresNumber (d + 3) n : ℝ) ≤
      max ((erdosSzekeresNumber 3 n : ℕ) : ℝ) ((d : ℝ) + 4) := by
    exact_mod_cast erdosSzekeresNumber_add_three_le d n
  exact hle.trans (max_le h3 hc)

/-- Premise-free `k`-indexed form of the subexponential bound in dimension `d + 3`. -/
theorem erdos_651_subexponential_inv_all_dimensions (d k : ℕ) : ∀ᶠ n : ℕ in Filter.atTop,
    (Erdos651.erdosSzekeresNumber (d + 3) n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) := by
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  filter_upwards [erdos_651_subexponential_all_dimensions d (1 / ((k : ℝ) + 1)) hk] with n hn
  rwa [show 1 / ((k : ℝ) + 1) * (n : ℝ) = (n : ℝ) / ((k : ℝ) + 1) by ring] at hn

/-- Erdős's conjectured exponential lower bound fails in every dimension `d ≥ 3`. -/
theorem erdos_651_disproved_all_dimensions (d : ℕ) :
    ¬ Erdos651.HasExponentialLowerBound (Erdos651.erdosSzekeresNumber (d + 3)) :=
  Erdos651.subexponential_not_exponentialLowerBound (erdos_651_subexponential_all_dimensions d)

end Asymptotics

end PohoataZakharov
