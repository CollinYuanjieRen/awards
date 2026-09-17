import Jsp202.DiameterGraph

/-!
# General lower bound for the planar diameter problem (Hopf–Pannwitz / Erdős #223)

For every `n ≥ 3` we exhibit an explicit planar configuration of `n` points with all pairwise
distances `≤ 1` whose diameter graph (adjacency `dist = 1`) has *exactly* `n` edges, witnessing the
"easy" direction `f₂(n) ≥ n`.

## The construction

Put one point `v₀` at the origin and the remaining `n - 1` points on the unit circle at angles
`k · c` (`k = 1, …, n-1`), where `c = π / (3 (n-2))`, so the largest angular gap `(n-2) · c` equals
`π/3`.  Then:

* every off-origin point is at distance exactly `1` from `v₀`  (`n - 1` diameter pairs);
* two off-origin points at indices `p, q` are at distance `2 |sin ((p-q) c / 2)|`, which equals `1`
  **iff** `|p - q| = n-2`, i.e. iff `{p, q} = {1, n-1}`  (exactly one further diameter pair);
* all other pairwise distances are `< 1`.

Total: `(n-1) + 1 = n` diameter pairs.  For `n = 3` this is the equilateral triangle.
-/

open scoped Classical
open Finset

namespace HopfPannwitz

/-- Distance between two explicit points of `EuclideanSpace ℝ (Fin 2)`. -/
theorem dist_pt2 (a b c d : ℝ) :
    dist (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) (!₂[c, d])
      = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs]

/-- Common angular unit `c = π / (3 (n-2))`. -/
noncomputable def cc (n : ℕ) : ℝ := Real.pi / (3 * ((n : ℝ) - 2))

/-- The construction: `v₀` at the origin, the other points on the unit circle at angle `i · c`. -/
noncomputable def genP (n : ℕ) : Fin n → EuclideanSpace ℝ (Fin 2) := fun i =>
  if i.val = 0 then !₂[0, 0]
  else !₂[Real.cos ((i.val : ℝ) * cc n), Real.sin ((i.val : ℝ) * cc n)]

variable {n : ℕ}

theorem nsub_pos (hn : 3 ≤ n) : (0 : ℝ) < (n : ℝ) - 2 := by
  have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

theorem cc_pos (hn : 3 ≤ n) : 0 < cc n := by
  unfold cc
  have := nsub_pos hn
  have : (0 : ℝ) < 3 * ((n : ℝ) - 2) := by linarith
  positivity

/-- The largest angular gap is `π/3`. -/
theorem nsub_mul_cc (hn : 3 ≤ n) : ((n : ℝ) - 2) * cc n = Real.pi / 3 := by
  unfold cc
  have h : (n : ℝ) - 2 ≠ 0 := ne_of_gt (nsub_pos hn)
  field_simp

/-- Distance from the origin vertex to any off-origin vertex is `1`. -/
theorem dist_origin (o i : Fin n) (ho : o.val = 0) (hi : i.val ≠ 0) :
    dist (genP n o) (genP n i) = 1 := by
  unfold genP
  simp only [ho, hi, ite_true, ite_false]
  rw [dist_pt2]
  rw [show ((0 : ℝ) - Real.cos ((i.val : ℝ) * cc n)) ^ 2
        + (0 - Real.sin ((i.val : ℝ) * cc n)) ^ 2
        = Real.sin ((i.val : ℝ) * cc n) ^ 2 + Real.cos ((i.val : ℝ) * cc n) ^ 2 by ring,
      Real.sin_sq_add_cos_sq, Real.sqrt_one]

/-- Chord formula for two off-origin vertices. -/
theorem circle_dist (i j : Fin n) (hi : i.val ≠ 0) (hj : j.val ≠ 0) :
    dist (genP n i) (genP n j)
      = Real.sqrt (2 - 2 * Real.cos (((i.val : ℝ) - (j.val : ℝ)) * cc n)) := by
  unfold genP
  simp only [hi, hj, ite_false]
  rw [dist_pt2]
  congr 1
  have hcs := Real.cos_sub ((i.val : ℝ) * cc n) ((j.val : ℝ) * cc n)
  have s1 := Real.sin_sq_add_cos_sq ((i.val : ℝ) * cc n)
  have s2 := Real.sin_sq_add_cos_sq ((j.val : ℝ) * cc n)
  rw [show ((i.val : ℝ) - (j.val : ℝ)) * cc n
        = (i.val : ℝ) * cc n - (j.val : ℝ) * cc n by ring, hcs]
  linear_combination s1 + s2

/-- The absolute index gap of two off-origin vertices is at most `n-2`. -/
theorem val_diff_le (_hn : 3 ≤ n) (i j : Fin n) (hi : i.val ≠ 0) (hj : j.val ≠ 0) :
    |(i.val : ℝ) - (j.val : ℝ)| ≤ (n : ℝ) - 2 := by
  have hib : (i.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : i.val + 1 ≤ n)
  have hjb : (j.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : j.val + 1 ≤ n)
  have hil : (1 : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast (by omega : 1 ≤ i.val)
  have hjl : (1 : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast (by omega : 1 ≤ j.val)
  rw [abs_le]; constructor <;> linarith

/-- Elementary trig bound: `cos x ≥ 1/2` on `[0, π/3]`. -/
theorem cos_ge_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 3) : (1 : ℝ) / 2 ≤ Real.cos x := by
  have hpi := Real.pi_pos
  have hmem3 : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have hmemx : x ∈ Set.Icc (0 : ℝ) Real.pi := ⟨h0, by linarith⟩
  rw [← Real.cos_pi_div_three]
  rcases eq_or_lt_of_le h1 with h | h
  · rw [h]
  · exact le_of_lt (Real.strictAntiOn_cos hmemx hmem3 h)

/-- Elementary trig bound: `cos x > 1/2` on `[0, π/3)`. -/
theorem cos_gt_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x < Real.pi / 3) : (1 : ℝ) / 2 < Real.cos x := by
  have hpi := Real.pi_pos
  have hmem3 : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have hmemx : x ∈ Set.Icc (0 : ℝ) Real.pi := ⟨h0, by linarith⟩
  rw [← Real.cos_pi_div_three]
  exact Real.strictAntiOn_cos hmemx hmem3 h1

/-- All pairwise distances in the configuration are `≤ 1`. -/
theorem dist_le_one (hn : 3 ≤ n) (i j : Fin n) : dist (genP n i) (genP n j) ≤ 1 := by
  rcases eq_or_ne i.val 0 with hi | hi
  · rcases eq_or_ne j.val 0 with hj | hj
    · -- both origin ⇒ same point
      have : i = j := Fin.ext (hi.trans hj.symm)
      simp [this]
    · exact le_of_eq (dist_origin i j hi hj)
  · rcases eq_or_ne j.val 0 with hj | hj
    · rw [dist_comm]; exact le_of_eq (dist_origin j i hj hi)
    · -- both off-origin
      rw [circle_dist i j hi hj]
      have hccpos := cc_pos hn
      have hxabs : |((i.val : ℝ) - (j.val : ℝ)) * cc n| ≤ Real.pi / 3 := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hccpos)]
        rw [← nsub_mul_cc hn]
        exact mul_le_mul_of_nonneg_right (val_diff_le hn i j hi hj) (le_of_lt hccpos)
      have hcos : (1 : ℝ) / 2 ≤ Real.cos (((i.val : ℝ) - (j.val : ℝ)) * cc n) := by
        rw [← Real.cos_abs]
        exact cos_ge_half (abs_nonneg _) hxabs
      have harg : 2 - 2 * Real.cos (((i.val : ℝ) - (j.val : ℝ)) * cc n) ≤ 1 := by linarith
      calc Real.sqrt (2 - 2 * Real.cos (((i.val : ℝ) - (j.val : ℝ)) * cc n))
          ≤ Real.sqrt 1 := Real.sqrt_le_sqrt harg
        _ = 1 := Real.sqrt_one

/-- If two off-origin vertices realise the extreme gap `|p-q| = n-2`, their distance is `1`. -/
theorem circle_dist_eq (hn : 3 ≤ n) (i j : Fin n) (hi : i.val ≠ 0) (hj : j.val ≠ 0)
    (hend : |(i.val : ℝ) - (j.val : ℝ)| = (n : ℝ) - 2) :
    dist (genP n i) (genP n j) = 1 := by
  rw [circle_dist i j hi hj]
  have hccpos := cc_pos hn
  have : Real.cos (((i.val : ℝ) - (j.val : ℝ)) * cc n) = 1 / 2 := by
    rw [← Real.cos_abs, abs_mul, abs_of_nonneg (le_of_lt hccpos), hend, nsub_mul_cc hn,
      Real.cos_pi_div_three]
  rw [this]; norm_num

/-- If two off-origin vertices are below the extreme gap `|p-q| < n-2`, their distance is `< 1`. -/
theorem circle_dist_lt (hn : 3 ≤ n) (i j : Fin n) (hi : i.val ≠ 0) (hj : j.val ≠ 0)
    (hmid : |(i.val : ℝ) - (j.val : ℝ)| < (n : ℝ) - 2) :
    dist (genP n i) (genP n j) < 1 := by
  rw [circle_dist i j hi hj]
  have hccpos := cc_pos hn
  have hxabs : |((i.val : ℝ) - (j.val : ℝ)) * cc n| < Real.pi / 3 := by
    rw [abs_mul, abs_of_nonneg (le_of_lt hccpos), ← nsub_mul_cc hn]
    exact mul_lt_mul_of_pos_right hmid hccpos
  have hcos : (1 : ℝ) / 2 < Real.cos (((i.val : ℝ) - (j.val : ℝ)) * cc n) := by
    rw [← Real.cos_abs]
    exact cos_gt_half (abs_nonneg _) hxabs
  have harg : 2 - 2 * Real.cos (((i.val : ℝ) - (j.val : ℝ)) * cc n) < 1 := by linarith
  rw [Real.sqrt_lt' (by norm_num)]; simpa using harg

/-- The extreme gap `|p-q| = n-2` forces the endpoints `{1, n-1}`. -/
theorem abs_eq_endpoints (hn : 3 ≤ n) (i j : Fin n) (hi : i.val ≠ 0) (hj : j.val ≠ 0)
    (h : |(i.val : ℝ) - (j.val : ℝ)| = (n : ℝ) - 2) :
    (i.val = 1 ∧ j.val = n - 1) ∨ (i.val = n - 1 ∧ j.val = 1) := by
  have hib := i.isLt
  have hjb := j.isLt
  rcases abs_choice ((i.val : ℝ) - (j.val : ℝ)) with hc | hc
  · rw [hc] at h
    have : i.val + 2 = n + j.val := by exact_mod_cast (by linarith : (i.val : ℝ) + 2 = (n : ℝ) + (j.val : ℝ))
    omega
  · rw [hc] at h
    have : j.val + 2 = n + i.val := by exact_mod_cast (by linarith : (j.val : ℝ) + 2 = (n : ℝ) + (i.val : ℝ))
    omega

/-- **Adjacency characterisation.** In the diameter graph with `D = 1`, `i ~ j` iff exactly one of
`i, j` is the origin, or `{i, j}` are the extreme circle points `{1, n-1}`. -/
theorem adj_iff (hn : 3 ≤ n) (i j : Fin n) :
    (diameterGraph (genP n) 1).Adj i j ↔
      (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0) ∨
      (i.val = 1 ∧ j.val = n - 1) ∨ (i.val = n - 1 ∧ j.val = 1) := by
  constructor
  · rintro ⟨hne, hdist⟩
    rcases eq_or_ne i.val 0 with hi | hi
    · exact Or.inl ⟨hi, fun hj => hne (Fin.ext (hi.trans hj.symm))⟩
    · rcases eq_or_ne j.val 0 with hj | hj
      · exact Or.inr (Or.inl ⟨hj, hi⟩)
      · -- both off-origin: dist = 1 forces the extreme gap
        refine Or.inr (Or.inr ?_)
        by_contra hcon
        have hne2 : |(i.val : ℝ) - (j.val : ℝ)| ≠ (n : ℝ) - 2 := by
          intro he; exact hcon (abs_eq_endpoints hn i j hi hj he)
        have hlt : |(i.val : ℝ) - (j.val : ℝ)| < (n : ℝ) - 2 :=
          lt_of_le_of_ne (val_diff_le hn i j hi hj) hne2
        have := circle_dist_lt hn i j hi hj hlt
        rw [hdist] at this
        exact lt_irrefl 1 this
  · intro h
    refine ⟨?_, ?_⟩
    · -- i ≠ j
      rcases h with ⟨hi, hj⟩ | ⟨hj, hi⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
      · intro he; rw [he] at hi; exact hj hi
      · intro he; rw [he] at hi; exact hi hj
      · intro he; rw [he] at hi; omega
      · intro he; rw [he] at hi; omega
    · -- dist = 1
      have hnr : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rcases h with ⟨hi, hj⟩ | ⟨hj, hi⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
      · exact dist_origin i j hi hj
      · rw [dist_comm]; exact dist_origin j i hj hi
      · refine circle_dist_eq hn i j (by omega) (by omega) ?_
        rw [hi, hj, hcast, Nat.cast_one, abs_of_nonpos (by linarith)]
        ring
      · refine circle_dist_eq hn i j (by omega) (by omega) ?_
        rw [hi, hj, hcast, Nat.cast_one, abs_of_nonneg (by linarith)]
        ring

/-- Two distinct indices have distinct off-origin/origin points: distances are strictly positive. -/
theorem one_le_abs_diff (i j : Fin n) (hij : i.val ≠ j.val) :
    (1 : ℝ) ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
  rcases Nat.lt_or_ge i.val j.val with h | h
  · rw [abs_of_nonpos]
    · have : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast h
      linarith
    · have : (i.val : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast le_of_lt h
      linarith
  · have h' : j.val < i.val := lt_of_le_of_ne h (Ne.symm hij)
    rw [abs_of_nonneg]
    · have : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast h'
      linarith
    · have : (j.val : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast le_of_lt h'
      linarith

/-- Distinct indices give points at positive distance. -/
theorem genP_dist_pos (hn : 3 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    0 < dist (genP n i) (genP n j) := by
  rcases eq_or_ne i.val 0 with hi | hi
  · rcases eq_or_ne j.val 0 with hj | hj
    · exact absurd (Fin.ext (hi.trans hj.symm)) hij
    · rw [dist_origin i j hi hj]; norm_num
  · rcases eq_or_ne j.val 0 with hj | hj
    · rw [dist_comm, dist_origin j i hj hi]; norm_num
    · rw [circle_dist i j hi hj]
      have hnenat : i.val ≠ j.val := fun he => hij (Fin.ext he)
      have hccpos := cc_pos hn
      have h1 := one_le_abs_diff i j hnenat
      have hup := val_diff_le hn i j hi hj
      have hpi := Real.pi_pos
      have hxpos : 0 < |((i.val : ℝ) - (j.val : ℝ)) * cc n| := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hccpos)]
        exact mul_pos (lt_of_lt_of_le one_pos h1) hccpos
      have hxle : |((i.val : ℝ) - (j.val : ℝ)) * cc n| ≤ Real.pi / 3 := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hccpos), ← nsub_mul_cc hn]
        exact mul_le_mul_of_nonneg_right hup (le_of_lt hccpos)
      have hcoslt : Real.cos (((i.val : ℝ) - (j.val : ℝ)) * cc n) < 1 := by
        rw [← Real.cos_abs]
        have hmem : |((i.val : ℝ) - (j.val : ℝ)) * cc n| ∈ Set.Icc (0 : ℝ) Real.pi :=
          ⟨abs_nonneg _, by linarith⟩
        have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_refl _, le_of_lt hpi⟩
        have := Real.strictAntiOn_cos hmem0 hmem hxpos
        rwa [Real.cos_zero] at this
      have hpos : 0 < 2 - 2 * Real.cos (((i.val : ℝ) - (j.val : ℝ)) * cc n) := by linarith
      exact Real.sqrt_pos.mpr hpos

/-- **`f₂(n) ≥ n`.**  For every `n ≥ 3` there is a planar configuration of `n` points with all
pairwise distances `≤ D` whose diameter graph has exactly `n` edges. -/
theorem exists_n_diameter_pairs (n : ℕ) (hn : 3 ≤ n) :
    ∃ (P : Fin n → EuclideanSpace ℝ (Fin 2)) (D : ℝ),
      Function.Injective P ∧ (∀ i j, dist (P i) (P j) ≤ D) ∧
      (diameterGraph P D).edgeFinset.card = n := by
  refine ⟨genP n, 1, ?_, dist_le_one hn, ?_⟩
  · -- injectivity: distinct points are at positive distance
    intro i j hPij
    by_contra hne
    have hpos := genP_dist_pos hn i j hne
    rw [hPij, dist_self] at hpos
    exact lt_irrefl 0 hpos
  · -- the diameter graph has exactly `n` edges
    have h0 : (0 : ℕ) < n := by omega
    have h1 : (1 : ℕ) < n := by omega
    have h2 : n - 1 < n := by omega
    set v0 : Fin n := ⟨0, h0⟩ with hv0def
    set v1 : Fin n := ⟨1, h1⟩ with hv1def
    set vL : Fin n := ⟨n - 1, h2⟩ with hvLdef
    have hv0 : v0.val = 0 := rfl
    have hv1 : v1.val = 1 := rfl
    have hvL : vL.val = n - 1 := rfl
    -- the explicit edge set: a star centred at `v0`, plus the extra edge `{v1, vL}`
    set S : Finset (Sym2 (Fin n)) := (univ.erase v0).image (fun i => s(v0, i)) with hSdef
    set E : Finset (Sym2 (Fin n)) := insert s(v1, vL) S with hEdef
    -- membership description of `E`
    have memE : ∀ i j : Fin n, s(i, j) ∈ E ↔
        (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0) ∨
        (i.val = 1 ∧ j.val = n - 1) ∨ (i.val = n - 1 ∧ j.val = 1) := by
      intro i j
      simp only [hEdef, hSdef, Finset.mem_insert, Finset.mem_image, Finset.mem_erase,
        Finset.mem_univ, and_true, Sym2.eq_iff]
      constructor
      · rintro (h | ⟨a, ha, hae⟩)
        · rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
          · exact Or.inr (Or.inr (Or.inl ⟨by rw [hi], by rw [hj]⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨by rw [hi], by rw [hj]⟩))
        · rcases hae with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
          · refine Or.inl ⟨by rw [← h1'], ?_⟩
            intro hj0; exact ha (h2'.trans (Fin.ext (hj0.trans hv0.symm)))
          · refine Or.inr (Or.inl ⟨by rw [← h1'], ?_⟩)
            intro hi0; exact ha (h2'.trans (Fin.ext (hi0.trans hv0.symm)))
      · rintro (⟨hi, hj⟩ | ⟨hj, hi⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩)
        · exact Or.inr ⟨j, fun hc => hj (by rw [hc]), Or.inl ⟨Fin.ext hi.symm, rfl⟩⟩
        · exact Or.inr ⟨i, fun hc => hi (by rw [hc]), Or.inr ⟨Fin.ext hj.symm, rfl⟩⟩
        · exact Or.inl (Or.inl ⟨Fin.ext (hi.trans hv1.symm), Fin.ext (hj.trans hvL.symm)⟩)
        · exact Or.inl (Or.inr ⟨Fin.ext (hi.trans hvL.symm), Fin.ext (hj.trans hv1.symm)⟩)
    -- the diameter graph's edge finset equals `E`
    have hEF : (diameterGraph (genP n) 1).edgeFinset = E := by
      ext e
      induction e using Sym2.ind with
      | _ i j =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, adj_iff hn, memE]
    rw [hEF]
    -- `s(v1, vL) ∉ S`
    have hnotmem : s(v1, vL) ∉ S := by
      simp only [hSdef, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
        Sym2.eq_iff, not_exists]
      rintro a ⟨ha, hcase⟩
      rcases hcase with ⟨he, _⟩ | ⟨he, _⟩
      · have : v0.val = v1.val := by rw [he]
        rw [hv0, hv1] at this; exact absurd this (by norm_num)
      · have : v0.val = vL.val := by rw [he]
        rw [hv0, hvL] at this; omega
    -- injectivity of the star map, hence `card S = n - 1`
    have hcardS : S.card = n - 1 := by
      rw [hSdef, Finset.card_image_of_injOn]
      · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      · intro a ha b hb hab
        simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Finset.mem_univ,
          Set.mem_singleton_iff, true_and] at ha hb
        rw [Sym2.eq_iff] at hab
        rcases hab with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h.symm hb
    rw [hEdef, Finset.card_insert_of_notMem hnotmem, hcardS]
    omega

#print axioms exists_n_diameter_pairs
