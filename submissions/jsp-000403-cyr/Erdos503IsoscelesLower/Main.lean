import Mathlib

/-!
# Erdős Problem #503: isosceles sets of size `C(d+1, 2) + 1` in `ℝ^d` (Alweiss, Weisenberg)

Erdős asked for the largest `A ⊆ ℝ^d` such that every three points of `A` form an isosceles
triangle (OPEN in general; `6` for `d = 2`, `8` for `d = 3`; Blokhuis: `|A| ≤ C(d+2, 2)`).  The
problem page records Alweiss's lower bound `C(d+1, 2)`, from the vectors `eᵢ + eⱼ` (`i < j`) in
`ℝ^{d+1}`, which lie in a hyperplane and so in some `ℝ^d`, and Weisenberg's observation that one
more point can be added, giving `C(d+1, 2) + 1`.  This file proves that construction: for every
`d` there is an isosceles set of `C(d+1, 2) + 1` points in `EuclideanSpace ℝ (Fin d)`.

The predicates `IsIsosceles`, `Set.Triplewise`, `Set.IsIsosceles` are copied verbatim from the
formal-conjectures repository.  The formal-conjectures statement `erdos_503.variants.lower_bound`
is phrased with `sSup {A.ncard | A.IsIsosceles}`, which in `ℕ` is only meaningful given an upper
bound (Blokhuis's theorem); the theorem here is the explicit existence statement behind it and
does not use `sSup`.  Kelly's, Croft's and Blokhuis's bounds and the general question are not
addressed.

Proof.  In `ℝ^{d+1}` the points `eᵢ + eⱼ` (`i < j`) have squared distance `2` when the pairs share
an index and `4` otherwise, and the point `(2/(d+1))·(1, …, 1)` is equidistant from all of them;
a triangle with side lengths from a two-element set is isosceles.  All points lie in the affine
hyperplane `∑ xᵢ = 2`, which is isometric to `ℝ^d`.  (For `d = 1` the extra point coincides with
`e₀ + e₁`, so the cases `d ≤ 1` — one point in `ℝ⁰`, two points in `ℝ¹` — are treated directly.)
-/

/-- Three points form an isosceles triangle (formal-conjectures definition). -/
def IsIsosceles {α : Type*} [Dist α] (p q r : α) : Prop :=
  dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q

/-- The ternary relation `r` holds triplewise on the set `s` (formal-conjectures definition). -/
protected def Set.Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

/-- Every three points of `A` form an isosceles triangle (formal-conjectures definition). -/
nonrec def Set.IsIsosceles {α : Type} [Dist α] (A : Set α) :=
  Nonempty A ∧ A.Triplewise (IsIsosceles · · ·)

/-- The Alweiss points `eᵢ + eⱼ` (`i < j`) in `ℝ^{d+1}`. -/
noncomputable def alweissPoint (d : ℕ) (p : Fin (d + 1) × Fin (d + 1)) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  EuclideanSpace.single p.1 1 + EuclideanSpace.single p.2 1

/-- Weisenberg's extra point `(2/(d+1)) · (1, …, 1)`. -/
noncomputable def weisenbergPoint (d : ℕ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  (WithLp.toLp 2 fun _ => (2 : ℝ) / (d + 1))

/-- The Alweiss–Weisenberg configuration in `ℝ^{d+1}`. -/
noncomputable def awConfig (d : ℕ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  insert (weisenbergPoint d)
    (alweissPoint d '' {p : Fin (d + 1) × Fin (d + 1) | p.1 < p.2})

/-! ### Helper lemmas for the Alweiss–Weisenberg configuration -/

/-- Three reals taken from a two-element set contain two equal ones. -/
private lemma three_of_pair_eq {u v a b c : ℝ} (ha : a = u ∨ a = v) (hb : b = u ∨ b = v)
    (hc : c = u ∨ c = v) : a = b ∨ b = c ∨ c = a := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> simp

/-- Coordinates of an Alweiss point. -/
private lemma alweissPoint_apply (d : ℕ) (p : Fin (d + 1) × Fin (d + 1)) (j : Fin (d + 1)) :
    (alweissPoint d p).ofLp j = (if j = p.1 then (1 : ℝ) else 0) + (if j = p.2 then 1 else 0) := by
  simp [alweissPoint, PiLp.single_apply]

/-- Coordinates of the Weisenberg point. -/
private lemma weisenbergPoint_apply (d : ℕ) (j : Fin (d + 1)) :
    (weisenbergPoint d).ofLp j = (2 : ℝ) / (d + 1) := by
  simp [weisenbergPoint]

/-- The coordinates of an Alweiss point sum to `2`. -/
private lemma sum_alweissPoint (d : ℕ) (p : Fin (d + 1) × Fin (d + 1)) :
    ∑ j, (alweissPoint d p).ofLp j = 2 := by
  simp [alweissPoint_apply, Finset.sum_add_distrib]
  norm_num

/-- The coordinates of the Weisenberg point sum to `2`. -/
private lemma sum_weisenbergPoint (d : ℕ) : ∑ j, (weisenbergPoint d).ofLp j = 2 := by
  have h : ((d : ℝ) + 1) ≠ 0 := by positivity
  simp only [weisenbergPoint_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp

/-- The inner product of two Alweiss points counts the shared indices. -/
private lemma inner_alweissPoint (d : ℕ) (p q : Fin (d + 1) × Fin (d + 1)) :
    inner ℝ (alweissPoint d p) (alweissPoint d q) =
      (if p.1 = q.1 then (1 : ℝ) else 0) + (if p.1 = q.2 then 1 else 0)
        + (if p.2 = q.1 then 1 else 0) + (if p.2 = q.2 then 1 else 0) := by
  simp [alweissPoint, inner_add_left, inner_add_right, EuclideanSpace.inner_single_left,
    PiLp.single_apply]
  ring

/-- The inner product of an Alweiss point with the Weisenberg point does not depend on the point. -/
private lemma inner_alweissPoint_weisenbergPoint (d : ℕ) (p : Fin (d + 1) × Fin (d + 1)) :
    inner ℝ (alweissPoint d p) (weisenbergPoint d) = 2 * ((2 : ℝ) / (d + 1)) := by
  simp [alweissPoint, weisenbergPoint, inner_add_left, EuclideanSpace.inner_single_left]
  ring

/-- The squared norm of the Weisenberg point. -/
private lemma norm_weisenbergPoint_sq (d : ℕ) :
    ‖weisenbergPoint d‖ ^ 2 = (d + 1) * ((2 : ℝ) / (d + 1)) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have h : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
  simp [weisenbergPoint, Real.norm_eq_abs, abs_of_nonneg h]

/-- The squared norm of an Alweiss point is `2`. -/
private lemma norm_alweissPoint_sq (d : ℕ) (p : Fin (d + 1) × Fin (d + 1)) (h : p.1 ≠ p.2) :
    ‖alweissPoint d p‖ ^ 2 = 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_alweissPoint]
  rw [ite_eq_left rfl, ite_eq_right h, ite_eq_right (Ne.symm h), ite_eq_left rfl]
  norm_num

/-- Two distinct Alweiss points are at squared distance `2` or `4`. -/
private lemma dist_alweissPoint_sq (d : ℕ) {p q : Fin (d + 1) × Fin (d + 1)} (hp : p.1 < p.2)
    (hq : q.1 < q.2) (hpq : p ≠ q) :
    dist (alweissPoint d p) (alweissPoint d q) ^ 2 = 2 ∨
      dist (alweissPoint d p) (alweissPoint d q) ^ 2 = 4 := by
  have hp' : p.1 ≠ p.2 := Fin.ne_of_lt hp
  have hq' : q.1 ≠ q.2 := Fin.ne_of_lt hq
  have hpv : (p.1 : ℕ) < (p.2 : ℕ) := hp
  have hqv : (q.1 : ℕ) < (q.2 : ℕ) := hq
  have key : dist (alweissPoint d p) (alweissPoint d q) ^ 2
      = 4 - 2 * ((if p.1 = q.1 then (1 : ℝ) else 0) + (if p.1 = q.2 then 1 else 0)
        + (if p.2 = q.1 then 1 else 0) + (if p.2 = q.2 then 1 else 0)) := by
    rw [dist_eq_norm, norm_sub_sq_real, norm_alweissPoint_sq d p hp', norm_alweissPoint_sq d q hq',
      inner_alweissPoint]
    ring
  rw [key]
  rcases eq_or_ne p.1 q.1 with c1 | c1
  · have e1 : (p.1 : ℕ) = (q.1 : ℕ) := congrArg Fin.val c1
    have c2 : p.1 ≠ q.2 := by intro h; have := congrArg Fin.val h; omega
    have c3 : p.2 ≠ q.1 := by intro h; have := congrArg Fin.val h; omega
    have c4 : p.2 ≠ q.2 := fun h => hpq (Prod.ext_iff.mpr ⟨c1, h⟩)
    left; rw [ite_eq_left c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4]; norm_num
  · rcases eq_or_ne p.1 q.2 with c2 | c2
    · have e2 : (p.1 : ℕ) = (q.2 : ℕ) := congrArg Fin.val c2
      have c3 : p.2 ≠ q.1 := by intro h; have := congrArg Fin.val h; omega
      have c4 : p.2 ≠ q.2 := by intro h; have := congrArg Fin.val h; omega
      left; rw [ite_eq_right c1, ite_eq_left c2, ite_eq_right c3, ite_eq_right c4]; norm_num
    · rcases eq_or_ne p.2 q.1 with c3 | c3
      · have e3 : (p.2 : ℕ) = (q.1 : ℕ) := congrArg Fin.val c3
        have c4 : p.2 ≠ q.2 := by intro h; have := congrArg Fin.val h; omega
        left; rw [ite_eq_right c1, ite_eq_right c2, ite_eq_left c3, ite_eq_right c4]; norm_num
      · rcases eq_or_ne p.2 q.2 with c4 | c4
        · left; rw [ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_left c4]; norm_num
        · right; rw [ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4]; norm_num

/-- The distance between two distinct Alweiss points is `√2` or `2`. -/
private lemma dist_alweissPoint_mem (d : ℕ) {p q : Fin (d + 1) × Fin (d + 1)} (hp : p.1 < p.2)
    (hq : q.1 < q.2) (hpq : p ≠ q) :
    dist (alweissPoint d p) (alweissPoint d q) = Real.sqrt 2 ∨
      dist (alweissPoint d p) (alweissPoint d q) = 2 := by
  have hs : dist (alweissPoint d p) (alweissPoint d q)
      = Real.sqrt (dist (alweissPoint d p) (alweissPoint d q) ^ 2) :=
    (Real.sqrt_sq dist_nonneg).symm
  rcases dist_alweissPoint_sq d hp hq hpq with h | h
  · exact Or.inl (by rw [hs, h])
  · refine Or.inr ?_
    rw [hs, h, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The Weisenberg point is equidistant from all Alweiss points. -/
private lemma dist_alweissPoint_weisenbergPoint (d : ℕ) {p q : Fin (d + 1) × Fin (d + 1)}
    (hp : p.1 ≠ p.2) (hq : q.1 ≠ q.2) :
    dist (alweissPoint d p) (weisenbergPoint d) = dist (alweissPoint d q) (weisenbergPoint d) := by
  have key : ∀ r : Fin (d + 1) × Fin (d + 1), r.1 ≠ r.2 →
      dist (alweissPoint d r) (weisenbergPoint d) ^ 2
        = 2 - 2 * (2 * ((2 : ℝ) / (d + 1))) + (d + 1) * ((2 : ℝ) / (d + 1)) ^ 2 := by
    intro r hr
    rw [dist_eq_norm, norm_sub_sq_real, norm_alweissPoint_sq d r hr,
      inner_alweissPoint_weisenbergPoint, norm_weisenbergPoint_sq]
  have e1 : dist (alweissPoint d p) (weisenbergPoint d)
      = Real.sqrt (dist (alweissPoint d p) (weisenbergPoint d) ^ 2) :=
    (Real.sqrt_sq dist_nonneg).symm
  have e2 : dist (alweissPoint d q) (weisenbergPoint d)
      = Real.sqrt (dist (alweissPoint d q) (weisenbergPoint d) ^ 2) :=
    (Real.sqrt_sq dist_nonneg).symm
  rw [e1, e2, key p hp, key q hq]

theorem awConfig_isIsosceles (d : ℕ) : (awConfig d).IsIsosceles := by
  classical
  refine ⟨⟨⟨weisenbergPoint d, Set.mem_insert _ _⟩⟩, ?_⟩
  intro x hx y hy z hz hxy hyz hxz
  simp only [awConfig, Set.mem_insert_iff, Set.mem_image, Set.mem_ofPred_eq] at hx hy hz
  simp only [IsIsosceles]
  rcases hx with rfl | ⟨p, hp, rfl⟩
  · rcases hy with rfl | ⟨q, hq, rfl⟩
    · exact absurd rfl hxy
    · rcases hz with rfl | ⟨r, hr, rfl⟩
      · exact absurd rfl hxz
      · refine Or.inr (Or.inr ?_)
        rw [dist_comm (weisenbergPoint d) (alweissPoint d q)]
        exact dist_alweissPoint_weisenbergPoint d (Fin.ne_of_lt hr) (Fin.ne_of_lt hq)
  · rcases hy with rfl | ⟨q, hq, rfl⟩
    · rcases hz with rfl | ⟨r, hr, rfl⟩
      · exact absurd rfl hyz
      · refine Or.inl ?_
        rw [dist_comm (weisenbergPoint d) (alweissPoint d r)]
        exact dist_alweissPoint_weisenbergPoint d (Fin.ne_of_lt hp) (Fin.ne_of_lt hr)
    · rcases hz with rfl | ⟨r, hr, rfl⟩
      · refine Or.inr (Or.inl ?_)
        rw [dist_comm (weisenbergPoint d) (alweissPoint d p)]
        exact dist_alweissPoint_weisenbergPoint d (Fin.ne_of_lt hq) (Fin.ne_of_lt hp)
      · have hpq : p ≠ q := fun h => hxy (by rw [h])
        have hqr : q ≠ r := fun h => hyz (by rw [h])
        have hrp : r ≠ p := fun h => hxz (by rw [h])
        exact three_of_pair_eq (dist_alweissPoint_mem d hp hq hpq)
          (dist_alweissPoint_mem d hq hr hqr) (dist_alweissPoint_mem d hr hp hrp)

/-- For `d ≥ 2` the configuration has `C(d+1, 2) + 1` points (for `d = 1` the extra point coincides
with `e₀ + e₁`; the cases `d ≤ 1` are handled directly in the main theorem). -/
theorem awConfig_ncard (d : ℕ) (hd : 2 ≤ d) : (awConfig d).ncard = (d + 1).choose 2 + 1 := by
  classical
  have hQ : weisenbergPoint d ∉ alweissPoint d '' {p : Fin (d + 1) × Fin (d + 1) | p.1 < p.2} := by
    rintro ⟨p, hp, hpq⟩
    have hp' : p.1 ≠ p.2 := Fin.ne_of_lt hp
    have h1 : (alweissPoint d p).ofLp p.1 = 1 := by
      rw [alweissPoint_apply, ite_eq_left rfl, ite_eq_right hp']; norm_num
    rw [hpq, weisenbergPoint_apply] at h1
    have hne : ((d : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (d : ℝ) = 1 := by field_simp at h1; linarith
    have h3 : d = 1 := by exact_mod_cast h2
    omega
  have hinj : Set.InjOn (alweissPoint d) {p : Fin (d + 1) × Fin (d + 1) | p.1 < p.2} := by
    intro p hp q hq h
    by_contra hne
    rcases dist_alweissPoint_sq d hp hq hne with h2 | h2 <;>
      · rw [h, dist_self] at h2; norm_num at h2
  have hcount : {p : Fin (d + 1) × Fin (d + 1) | p.1 < p.2}.ncard = (d + 1).choose 2 := by
    have h1 : {p : Fin (d + 1) × Fin (d + 1) | p.1 < p.2}
        = (({x ∈ (Finset.univ : Finset (Fin (d + 1))) ×ˢ (Finset.univ : Finset (Fin (d + 1))) |
            x.1 < x.2} : Finset (Fin (d + 1) × Fin (d + 1))) : Set (Fin (d + 1) × Fin (d + 1))) := by
      ext p; simp
    rw [h1, Set.ncard_coe_finset, Finset.card_product_filter_lt, Finset.card_univ,
      Fintype.card_fin]
  rw [awConfig, Set.ncard_insert_of_notMem hQ (Set.Finite.image _ (Set.toFinite _)),
    Set.InjOn.ncard_image hinj, hcount]

/-- The configuration lies in an affine hyperplane isometric to `ℝ^d`: there is an isometry from
`EuclideanSpace ℝ (Fin d)` onto that hyperplane whose image contains the configuration. -/
theorem exists_isometry_awConfig (d : ℕ) :
    ∃ f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (d + 1)),
      Isometry f ∧ awConfig d ⊆ Set.range f := by
  classical
  obtain ⟨L, hL⟩ : ∃ L : EuclideanSpace ℝ (Fin (d + 1)) →ₗ[ℝ] ℝ,
      ∀ x, L x = ∑ j, x.ofLp j :=
    ⟨{ toFun := fun x => ∑ j, x.ofLp j
       map_add' := fun x y => by simp [Finset.sum_add_distrib]
       map_smul' := fun c x => by simp [Finset.mul_sum] }, fun _ => rfl⟩
  have hsurj : Function.Surjective L := by
    intro t
    refine ⟨EuclideanSpace.single (0 : Fin (d + 1)) t, ?_⟩
    rw [hL]
    simp [PiLp.single_apply]
  have hrange : Module.finrank ℝ (LinearMap.range L) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  have hdim : Module.finrank ℝ (LinearMap.ker L) = d := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [hrange, finrank_euclideanSpace_fin] at h
    omega
  set b : OrthonormalBasis (Fin d) ℝ (LinearMap.ker L) :=
    (stdOrthonormalBasis ℝ (LinearMap.ker L)).reindex (finCongr hdim) with hbdef
  refine ⟨fun v => ((b.repr.symm v : LinearMap.ker L) : EuclideanSpace ℝ (Fin (d + 1)))
      + weisenbergPoint d, ?_, ?_⟩
  · refine Isometry.of_dist_eq fun u v => ?_
    rw [dist_add_right, ← Subtype.dist_eq, LinearIsometryEquiv.dist_map]
  · rintro x hx
    have hLx : L x = 2 := by
      rcases hx with rfl | ⟨p, _, rfl⟩
      · rw [hL]; exact sum_weisenbergPoint d
      · rw [hL]; exact sum_alweissPoint d p
    have hmem : x - weisenbergPoint d ∈ LinearMap.ker L := by
      simp only [LinearMap.mem_ker, map_sub, hLx, hL (weisenbergPoint d), sum_weisenbergPoint]
      ring
    exact ⟨b.repr ⟨x - weisenbergPoint d, hmem⟩, by simp⟩

/-- **Alweiss–Weisenberg lower bound for Erdős #503.**  For every `d` there is a set of
`C(d+1, 2) + 1` points in `ℝ^d` every three of which form an isosceles triangle.  Kelly's,
Croft's and Blokhuis's bounds and the general question are not claimed. -/
theorem erdos_503_lower_bound_explicit (d : ℕ) :
    ∃ A : Set (EuclideanSpace ℝ (Fin d)), A.IsIsosceles ∧ A.ncard = (d + 1).choose 2 + 1 := by
  classical
  match d, (by omega : d = 0 ∨ d = 1 ∨ 2 ≤ d) with
  | 0, _ =>
    refine ⟨{0}, ⟨⟨⟨0, rfl⟩⟩, ?_⟩, by simp⟩
    intro x hx y hy z hz hxy _ _
    rw [Set.mem_singleton_iff] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  | 1, _ =>
    have hne : (0 : EuclideanSpace ℝ (Fin 1)) ≠ EuclideanSpace.single 0 1 := by
      intro h
      have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v.ofLp 0) h
      simp at h2
    refine ⟨{0, EuclideanSpace.single 0 1}, ⟨⟨⟨0, Set.mem_insert _ _⟩⟩, ?_⟩, ?_⟩
    · intro x hx y hy z hz hxy hyz hxz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
        simp_all
    · rw [Set.ncard_pair hne]
      norm_num
  | (n + 2), _ =>
    obtain ⟨f, hf, hsub⟩ := exists_isometry_awConfig (n + 2)
    refine ⟨f ⁻¹' awConfig (n + 2), ⟨?_, ?_⟩, ?_⟩
    · obtain ⟨y, hy⟩ := hsub (Set.mem_insert (weisenbergPoint (n + 2)) _)
      exact ⟨⟨y, by simp only [Set.mem_preimage, hy]; exact Set.mem_insert _ _⟩⟩
    · intro x hx y hy z hz hxy hyz hxz
      have h := (awConfig_isIsosceles (n + 2)).2 hx hy hz
        (fun h => hxy (hf.injective h)) (fun h => hyz (hf.injective h))
        (fun h => hxz (hf.injective h))
      simpa only [IsIsosceles, hf.dist_eq] using h
    · rw [Set.ncard_preimage_of_injective_subset_range hf.injective hsub,
        awConfig_ncard (n + 2) (by omega)]
