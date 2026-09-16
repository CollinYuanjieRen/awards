import MerLeanExperiment.BinaryLimits

/-!
Finite clusters of binary power-sum configurations around distinct centers.
-/

namespace PlanarMinimax

open Filter Set
open scoped Topology

/-- The dependent index type of binary words grouped by cluster tag. -/
abbrev ClusterVertex (T : Type*) (k : T → ℕ) := Σ t : T, BinaryWord (k t)

/-- Transport a cluster word across an equality of tags. -/
def castClusterWord {T : Type*} {k : T → ℕ} {s t : T} (h : s = t)
    (b : BinaryWord (k t)) : BinaryWord (k s) :=
  h ▸ b

@[simp] theorem castClusterWord_self {T : Type*} {k : T → ℕ} {t : T}
    (h : t = t) (b : BinaryWord (k t)) : castClusterWord h b = b := by
  have hp : h = rfl := Subsingleton.elim _ _
  subst hp
  rfl

/-- Equal tags and equal transported words determine equal cluster vertices. -/
theorem clusterVertex_eq_of_tag_word {T : Type*} {k : T → ℕ}
    {x y : ClusterVertex T k} (htag : x.1 = y.1)
    (hword : x.2 = castClusterWord htag y.2) : x = y := by
  cases x with
  | mk tx bx =>
    cases y with
    | mk ty cy =>
      change tx = ty at htag
      cases htag
      change bx = cy at hword
      cases hword
      rfl

/-- A sign choice on an arbitrary vector. -/
def clusterSigned (sign : Bool) (v : Plane) : Plane :=
  if sign then v else -v

/-- A differing target bit selects the corresponding sign of an arbitrary vector. -/
theorem bitCoeff_smul_eq_clusterSigned {b c : Bool} (hbc : b ≠ c) (v : Plane) :
    (bitCoeff c - bitCoeff b) • v = clusterSigned c v := by
  cases b <;> cases c <;> simp_all [bitCoeff, clusterSigned]

/-- Signing preserves nonzeroness. -/
theorem clusterSigned_ne_zero (sign : Bool) {v : Plane} (hv : v ≠ 0) :
    clusterSigned sign v ≠ 0 := by
  cases sign <;> simp [clusterSigned, hv]

/-- The perturbed point belonging to a cluster vertex. -/
noncomputable def clusterPoint {T : Type*} {k : T → ℕ}
    (center : T → Plane) (u : ∀ t, Fin (k t) → Plane) (ε : ℝ)
    (x : ClusterVertex T k) : Plane :=
  center x.1 + ε • binaryPoint (u x.1) ε x.2

/-- Pairwise scale: inverse power within a cluster and one between clusters. -/
noncomputable def clusterScale {T : Type*} {k : T → ℕ}
    (x y : ClusterVertex T k) (ε : ℝ) : ℝ := by
  classical
  exact if htag : x.1 = y.1 then
      let cy := castClusterWord htag y.2
      if hword : x.2 = cy then 1
      else (ε ^ ((firstDiff x.2 cy hword).val + 1))⁻¹
    else 1

/-- Pairwise limit: signed internal direction or the displacement of two centers. -/
noncomputable def clusterDirection {T : Type*} {k : T → ℕ}
    (center : T → Plane) (u : ∀ t, Fin (k t) → Plane)
    (x y : ClusterVertex T k) : Plane := by
  classical
  exact if htag : x.1 = y.1 then
      let cy := castClusterWord htag y.2
      if hword : x.2 = cy then 0
      else
        let r := firstDiff x.2 cy hword
        clusterSigned (cy r) (u x.1 r)
    else center y.1 - center x.1

/-- Off-diagonal cluster scales are eventually positive. -/
theorem clusterScale_eventually_pos {T : Type*} {k : T → ℕ}
    (x y : ClusterVertex T k) (hxy : x ≠ y) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < clusterScale x y ε := by
  classical
  rcases x with ⟨tx, bx⟩
  rcases y with ⟨ty, cy⟩
  by_cases htag : tx = ty
  · subst ty
    have hword : bx ≠ cy := by
      intro hw
      apply hxy
      cases hw
      rfl
    simpa [clusterScale, hword] using
      eventually_invPow_pos ((firstDiff bx cy hword).val + 1)
  · simp [clusterScale, htag]

/-- Between distinct clusters, unscaled displacements converge to center displacements. -/
theorem clusterPoint_sub_tendsto_of_tag_ne {T : Type*} {k : T → ℕ}
    (center : T → Plane) (u : ∀ t, Fin (k t) → Plane)
    (x y : ClusterVertex T k) (_htag : x.1 ≠ y.1) :
    Tendsto (fun ε : ℝ ↦ clusterPoint center u ε y - clusterPoint center u ε x)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (center y.1 - center x.1)) := by
  apply (Continuous.tendsto' (by unfold clusterPoint binaryPoint; fun_prop)
    0 (center y.1 - center x.1) _).mono_left inf_le_left
  simp [clusterPoint]

/-- Within one cluster, the extra outer parameter shifts the extracted power by one. -/
theorem clusterPoint_sub_factor_words {T : Type*} {k : T → ℕ}
    (center : T → Plane) (u : ∀ t, Fin (k t) → Plane)
    (t : T) (b c : BinaryWord (k t)) (hbc : b ≠ c) (ε : ℝ) :
    clusterPoint center u ε ⟨t, c⟩ - clusterPoint center u ε ⟨t, b⟩ =
      (ε ^ ((firstDiff b c hbc).val + 1)) •
        binaryTail (u t) b c (firstDiff b c hbc) ε := by
  rw [show clusterPoint center u ε ⟨t, c⟩ - clusterPoint center u ε ⟨t, b⟩ =
      ε • (binaryPoint (u t) ε c - binaryPoint (u t) ε b) by
    simp [clusterPoint, smul_sub]]
  rw [binaryPoint_sub_factor (u t) b c _ (firstDiff_spec b c hbc) ε]
  simp [pow_succ, smul_smul, mul_comm]

/-- Same-cluster rescaled displacements converge to signed internal directions. -/
theorem clusterPoint_sub_tendsto_words {T : Type*} {k : T → ℕ}
    (center : T → Plane) (u : ∀ t, Fin (k t) → Plane)
    (t : T) (b c : BinaryWord (k t)) (hbc : b ≠ c) :
    Tendsto (fun ε : ℝ ↦ clusterScale ⟨t, b⟩ ⟨t, c⟩ ε •
        (clusterPoint center u ε ⟨t, c⟩ - clusterPoint center u ε ⟨t, b⟩))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (clusterDirection center u ⟨t, b⟩ ⟨t, c⟩)) := by
  let r := firstDiff b c hbc
  have htail : Tendsto (binaryTail (u t) b c r)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (binaryTail (u t) b c r 0)) :=
    (continuous_binaryTail (u t) b c r).continuousAt.mono_left inf_le_left
  rw [show clusterDirection center u ⟨t, b⟩ ⟨t, c⟩ =
      clusterSigned (c r) (u t r) by simp [clusterDirection, hbc, r]]
  rw [← bitCoeff_smul_eq_clusterSigned (firstDiff_ne b c hbc) (u t r)]
  rw [← binaryTail_zero (u t) b c r (firstDiff_spec b c hbc)]
  apply htail.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := by
    exact ne_of_gt (show (0 : ℝ) < ε from hε)
  rw [show clusterScale (⟨t, b⟩ : ClusterVertex T k) ⟨t, c⟩ ε =
      (ε ^ (r.val + 1))⁻¹ by simp [clusterScale, hbc, r]]
  rw [clusterPoint_sub_factor_words center u t b c hbc ε]
  simp [r, smul_smul, hε0]

/-- Off-diagonal cluster displacements converge to their declared directions. -/
theorem clusterDisplacement_tendsto {T : Type*} {k : T → ℕ}
    (center : T → Plane) (u : ∀ t, Fin (k t) → Plane)
    (x y : ClusterVertex T k) (hxy : x ≠ y) :
    Tendsto (fun ε : ℝ ↦ clusterScale x y ε •
        (clusterPoint center u ε y - clusterPoint center u ε x))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (clusterDirection center u x y)) := by
  classical
  rcases x with ⟨tx, bx⟩
  rcases y with ⟨ty, cy⟩
  by_cases htag : tx = ty
  · subst ty
    have hword : bx ≠ cy := by
      intro hw
      apply hxy
      cases hw
      rfl
    exact clusterPoint_sub_tendsto_words center u tx bx cy hword
  · simpa [clusterScale, clusterDirection, htag] using
      clusterPoint_sub_tendsto_of_tag_ne center u ⟨tx, bx⟩ ⟨ty, cy⟩ htag

/-- Off-diagonal cluster limiting directions are nonzero. -/
theorem clusterDirection_ne_zero {T : Type*} {k : T → ℕ}
    (center : T → Plane) (hcenter : Function.Injective center)
    (u : ∀ t, Fin (k t) → Plane) (hu : ∀ t r, u t r ≠ 0)
    (x y : ClusterVertex T k) (hxy : x ≠ y) : clusterDirection center u x y ≠ 0 := by
  classical
  rcases x with ⟨tx, bx⟩
  rcases y with ⟨ty, cy⟩
  by_cases htag : tx = ty
  · subst ty
    have hword : bx ≠ cy := by
      intro hw
      apply hxy
      cases hw
      rfl
    simp [clusterDirection, hword, clusterSigned_ne_zero _ (hu _ _)]
  · simp [clusterDirection, htag, sub_ne_zero.mpr (hcenter.ne (Ne.symm htag))]

/-- The closed form of an internal off-diagonal limiting direction. -/
theorem clusterDirection_same_words {T : Type*} {k : T → ℕ}
    (center : T → Plane) (u : ∀ t, Fin (k t) → Plane)
    (t : T) (b c : BinaryWord (k t)) (hbc : b ≠ c) :
    clusterDirection center u ⟨t, b⟩ ⟨t, c⟩ =
      clusterSigned (c (firstDiff b c hbc)) (u t (firstDiff b c hbc)) := by
  simp [clusterDirection, hbc]

/-- The closed form of a limiting direction between different clusters. -/
theorem clusterDirection_of_tag_ne {T : Type*} {k : T → ℕ}
    (center : T → Plane) (u : ∀ t, Fin (k t) → Plane)
    {s t : T} (hst : s ≠ t) (b : BinaryWord (k s)) (c : BinaryWord (k t)) :
    clusterDirection center u ⟨s, b⟩ ⟨t, c⟩ = center t - center s := by
  simp [clusterDirection, hst]

/-- The three geometric cluster hypotheses control every limiting triple angle. -/
theorem clusterDirection_angle_le {T : Type*} {k : T → ℕ} {B : ℝ}
    (center : T → Plane) (hcenter : Function.Injective center)
    (u : ∀ t, Fin (k t) → Plane) (hu : ∀ t r, u t r ≠ 0)
    (hB : 0 ≤ B)
    (hInternal : ∀ t (r s : Fin (k t)), r ≠ s → ∀ σ τ,
      InnerProductGeometry.angle (clusterSigned σ (u t r))
        (clusterSigned τ (u t s)) ≤ B)
    (hMixed : ∀ t (r : Fin (k t)) s, t ≠ s → ∀ σ,
      InnerProductGeometry.angle (clusterSigned σ (u t r))
        (center s - center t) ≤ B)
    (hCenters : ∀ a b c, a ≠ b → b ≠ c → a ≠ c →
      InnerProductGeometry.angle (center a - center b) (center c - center b) ≤ B)
    (x y z : ClusterVertex T k) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    InnerProductGeometry.angle (clusterDirection center u y x)
      (clusterDirection center u y z) ≤ B := by
  classical
  rcases x with ⟨tx, bx⟩
  rcases y with ⟨ty, bw⟩
  rcases z with ⟨tz, bz⟩
  by_cases hxt : tx = ty
  · subst tx
    have hbyx : bw ≠ bx := by
      intro h
      apply hxy
      cases h
      rfl
    by_cases hzt : tz = ty
    · subst tz
      have hbyz : bw ≠ bz := by
        intro h
        apply hyz
        cases h
        rfl
      rw [clusterDirection_same_words center u ty bw bx hbyx,
        clusterDirection_same_words center u ty bw bz hbyz]
      let r := firstDiff bw bx hbyx
      let s := firstDiff bw bz hbyz
      by_cases hrs : r = s
      · have heq : clusterSigned (bx r) (u ty r) = clusterSigned (bz s) (u ty s) := by
          rw [← bitCoeff_smul_eq_clusterSigned (firstDiff_ne bw bx hbyx) (u ty r),
            ← bitCoeff_smul_eq_clusterSigned (firstDiff_ne bw bz hbyz) (u ty s)]
          exact same_signedLeading_firstDiff (u ty) bw bx bz hbyx hbyz hrs
        change InnerProductGeometry.angle (clusterSigned (bx r) (u ty r))
          (clusterSigned (bz s) (u ty s)) ≤ B
        rw [heq, InnerProductGeometry.angle_self
          (clusterSigned_ne_zero (bz s) (hu ty s))]
        exact hB
      · exact hInternal ty r s hrs (bx r) (bz s)
    · rw [clusterDirection_same_words center u ty bw bx hbyx,
        clusterDirection_of_tag_ne center u (Ne.symm hzt) bw bz]
      exact hMixed ty (firstDiff bw bx hbyx) tz (Ne.symm hzt)
        (bx (firstDiff bw bx hbyx))
  · by_cases hzt : tz = ty
    · subst tz
      have hbyz : bw ≠ bz := by
        intro h
        apply hyz
        cases h
        rfl
      rw [clusterDirection_of_tag_ne center u (Ne.symm hxt) bw bx,
        clusterDirection_same_words center u ty bw bz hbyz,
        InnerProductGeometry.angle_comm]
      exact hMixed ty (firstDiff bw bz hbyz) tx (Ne.symm hxt)
        (bz (firstDiff bw bz hbyz))
    · rw [clusterDirection_of_tag_ne center u (Ne.symm hxt) bw bx,
        clusterDirection_of_tag_ne center u (Ne.symm hzt) bw bz]
      by_cases hxzTag : tx = tz
      · subst tz
        rw [InnerProductGeometry.angle_self
          (sub_ne_zero.mpr (hcenter.ne hxt))]
        exact hB
      · exact hCenters tx ty tz hxt (Ne.symm hzt) hxzTag

/-- The dependent family of cluster words has the expected sum-of-powers cardinality. -/
theorem card_clusterVertex {T : Type*} [Fintype T] (k : T → ℕ) :
    Fintype.card (ClusterVertex T k) = ∑ t, 2 ^ k t := by
  classical
  simp [ClusterVertex, Fintype.card_sigma]

/-- A chosen injection of ordinary indices into a sufficiently large cluster family. -/
noncomputable def indexClusterVertex {T : Type*} [Fintype T] {k : T → ℕ} {N : ℕ}
    (hN : N ≤ ∑ t, 2 ^ k t) : Fin N → ClusterVertex T k :=
  (Fintype.equivFinOfCardEq (card_clusterVertex k)).symm ∘ Fin.castLE hN

/-- The chosen indexed cluster vertices are distinct. -/
theorem indexClusterVertex_injective {T : Type*} [Fintype T] {k : T → ℕ} {N : ℕ}
    (hN : N ≤ ∑ t, 2 ^ k t) : Function.Injective (indexClusterVertex hN) := by
  exact (Fintype.equivFinOfCardEq (card_clusterVertex k)).symm.injective.comp
    (Fin.castLEEmb hN).injective

/-- Finite binary clusters satisfying the three explicit geometric bounds give a minimax bound. -/
theorem minimaxAngle_le_cluster {T : Type*} [Fintype T] {k : T → ℕ}
    {N : ℕ} {B : ℝ} (hN : 3 ≤ N) (hcard : N ≤ ∑ t, 2 ^ k t)
    (center : T → Plane) (hcenter : Function.Injective center)
    (u : ∀ t, Fin (k t) → Plane) (hu : ∀ t r, u t r ≠ 0)
    (hB : 0 ≤ B)
    (hInternal : ∀ t (r s : Fin (k t)), r ≠ s → ∀ σ τ,
      InnerProductGeometry.angle (clusterSigned σ (u t r))
        (clusterSigned τ (u t s)) ≤ B)
    (hMixed : ∀ t (r : Fin (k t)) s, t ≠ s → ∀ σ,
      InnerProductGeometry.angle (clusterSigned σ (u t r))
        (center s - center t) ≤ B)
    (hCenters : ∀ a b c, a ≠ b → b ≠ c → a ≠ c →
      InnerProductGeometry.angle (center a - center b) (center c - center b) ≤ B) :
    minimaxAngle N ≤ B := by
  let vertex : Fin N → ClusterVertex T k := indexClusterVertex hcard
  have hvertex : Function.Injective vertex := indexClusterVertex_injective hcard
  let P : ℝ → Fin N → Plane := fun ε i ↦ clusterPoint center u ε (vertex i)
  let scale : Fin N → Fin N → ℝ → ℝ := fun i j ε ↦ clusterScale (vertex i) (vertex j) ε
  let direction : Fin N → Fin N → Plane :=
    fun i j ↦ clusterDirection center u (vertex i) (vertex j)
  apply minimaxAngle_le_of_angleLimit hN P scale direction
  · intro i j hij
    exact clusterScale_eventually_pos (vertex i) (vertex j) (hvertex.ne hij)
  · intro i j hij
    change Tendsto (fun ε : ℝ ↦ clusterScale (vertex i) (vertex j) ε •
        (clusterPoint center u ε (vertex j) - clusterPoint center u ε (vertex i)))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (clusterDirection center u (vertex i) (vertex j)))
    exact clusterDisplacement_tendsto center u (vertex i) (vertex j) (hvertex.ne hij)
  · intro i j hij
    exact clusterDirection_ne_zero center hcenter u hu (vertex i) (vertex j) (hvertex.ne hij)
  · intro i j l hij hjl hil
    exact clusterDirection_angle_le center hcenter u hu hB hInternal hMixed hCenters
      (vertex i) (vertex j) (vertex l) (hvertex.ne hij) (hvertex.ne hjl) (hvertex.ne hil)

#print axioms minimaxAngle_le_cluster

end PlanarMinimax
