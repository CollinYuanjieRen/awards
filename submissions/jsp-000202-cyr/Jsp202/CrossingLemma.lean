import Mathlib

open scoped Classical
open Finset Module

namespace HopfPannwitz

/-!
# The crossing lemma for diameter segments

`crossing_lemma`: four distinct points of a planar configuration of diameter `D`, with
`dist a b = D = dist c d` (two "diameter" chords), have their closed segments `[a,b]` and `[c,d]`
sharing a point.

The proof is via **Radon's theorem** (`Convex.radon_partition`): four points in the plane are
affinely dependent, so they admit a Radon partition into two subsets whose convex hulls meet at a
point `O`. Enumerating the partition:

* pair vs. pair `{a,b} | {c,d}` — `O ∈ [a,b] ∩ [c,d]`, done immediately;
* diagonal `{a,c} | {b,d}` (or `{a,d} | {b,c}`) — `O ∈ [a,c] ∩ [b,d]`; then `diag_cross` uses the
  triangle inequality together with `dist_add_dist_eq_iff` (valid since `EuclideanSpace ℝ (Fin 2)`
  is strictly convex) to upgrade this to `O ∈ [a,b] ∩ [c,d]`;
* singleton `{p} | {other three}` — the lone point `p` lies in the convex hull of the other three;
  `lone_in_hull` shows the diameter equality forces `p` onto the segment between the two non-partner
  points, again giving the crossing.

The whole proof is complete, with no admitted goals.  The statement is over
`EuclideanSpace ℝ (Fin 2)`: it is genuinely
two-dimensional (a regular tetrahedron is a counterexample in dimension `≥ 3`), and this is the
faithful specialisation used by the application (`DiameterGraph`).
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- If the diagonals `[a,c]` and `[b,d]` of the "quadrilateral" `a,b,c,d` cross at `O`, and
`dist a b = dist c d = D` with `dist a c ≤ D`, `dist b d ≤ D`, then in fact `O` lies on both
`[a,b]` and `[c,d]`.  (The crossing forces `dist a c + dist b d = 2D`, hence both triangle
inequalities `dist a b ≤ dist a O + dist O b` and `dist c d ≤ dist c O + dist O d` are equalities;
`dist_add_dist_eq_iff` then yields the betweenness.) -/
private theorem diag_cross (a b c d O : V) (D : ℝ)
    (hab : dist a b = D) (hcd : dist c d = D) (hac : dist a c ≤ D) (hbd : dist b d ≤ D)
    (h1 : Wbtw ℝ a O c) (h2 : Wbtw ℝ b O d) :
    Wbtw ℝ a O b ∧ Wbtw ℝ c O d := by
  have e1 : dist a O + dist O c = dist a c := h1.dist_add_dist
  have e2 : dist b O + dist O d = dist b d := h2.dist_add_dist
  have t1 : dist a b ≤ dist a O + dist O b := dist_triangle a O b
  have t2 : dist c d ≤ dist c O + dist O d := dist_triangle c O d
  have rearr : dist a O + dist O b + (dist c O + dist O d) = dist a c + dist b d := by
    rw [← e1, ← e2, dist_comm O b, dist_comm c O]; ring
  refine ⟨?_, ?_⟩
  · rw [← dist_add_dist_eq_iff]; linarith [t1, t2, rearr, hac, hbd, hab, hcd]
  · rw [← dist_add_dist_eq_iff]; linarith [t1, t2, rearr, hac, hbd, hab, hcd]

/-- If `c ∈ [d, y]` and `y ∈ [a,b]` with `dist c d = D` maximal (`dist d a ≤ D`, `dist d b ≤ D`),
then `c` lies on `[a,b]`.  (`dist d y ≤ D` by convexity, and `c` between `d` and `y` at distance
`D = dist d c` from `d` forces `c = y`.) -/
private theorem onSeg_of_apex (a b c d : V) (D : ℝ)
    (hcd : dist c d = D) (hda : dist d a ≤ D) (hdb : dist d b ≤ D)
    (y : V) (hy : y ∈ segment ℝ a b) (hc : c ∈ segment ℝ d y) :
    c ∈ segment ℝ a b := by
  have hwy : Wbtw ℝ a y b := mem_segment_iff_wbtw.1 hy
  have hwc : Wbtw ℝ d c y := mem_segment_iff_wbtw.1 hc
  have hdy : dist d y ≤ D := by
    have h := hwy.dist_le_max_dist d
    rw [dist_comm y d, dist_comm a d, dist_comm b d] at h
    exact le_trans h (max_le hda hdb)
  have e : dist d c + dist c y = dist d y := hwc.dist_add_dist
  have hdc : dist d c = D := by rw [dist_comm]; exact hcd
  have hcy0 : dist c y = 0 := le_antisymm (by nlinarith [dist_nonneg (x := c) (y := y)]) dist_nonneg
  rw [dist_eq_zero.1 hcy0]; exact hy

/-- The lone point `p` (whose diameter partner is `q`) inside the convex hull of the other three
points `{x, y, q}` must actually lie on the segment `[x, y]` between the two non-partner points. -/
private theorem lone_in_hull (x y q p : V) (D : ℝ)
    (hpq : dist p q = D) (hqx : dist q x ≤ D) (hqy : dist q y ≤ D)
    (hmem : p ∈ convexHull ℝ ({x, y, q} : Set V)) : p ∈ segment ℝ x y := by
  have hset : ({x, y, q} : Set V) = insert q {x, y} := by ext z; simp; tauto
  rw [hset, convexHull_insert (Set.insert_nonempty x {y}), convexHull_pair, mem_convexJoin] at hmem
  obtain ⟨s, hs, w, hw, hpsw⟩ := hmem
  rw [Set.mem_singleton_iff] at hs
  rw [hs] at hpsw
  exact onSeg_of_apex x y p q D hpq hqx hqy w hw hpsw

set_option maxHeartbeats 1600000 in
/-- Two "diameter" segments meet: four distinct points, all pairwise distances `≤ D`, with
`dist a b = D = dist c d`, have their closed segments `[a,b]` and `[c,d]` sharing a point. -/
theorem crossing_lemma (a b c d : EuclideanSpace ℝ (Fin 2)) (D : ℝ)
    (hab : dist a b = D) (hcd : dist c d = D)
    (hca : dist c a ≤ D) (hcb : dist c b ≤ D) (hda : dist d a ≤ D) (hdb : dist d b ≤ D)
    (hac : dist a c ≤ D) (had : dist a d ≤ D) (hbc : dist b c ≤ D) (hbd : dist b d ≤ D)
    (_habne : a ≠ b) (_hcdne : c ≠ d)
    (_hac' : a ≠ c) (_had' : a ≠ d) (_hbc' : b ≠ c) (_hbd' : b ≠ d) :
    ∃ O, Wbtw ℝ a O b ∧ Wbtw ℝ c O d := by
  -- Four points in the plane are affinely dependent.
  have hdep : ¬ AffineIndependent ℝ ![a, b, c, d] := by
    rw [← finrank_vectorSpan_le_iff_not_affineIndependent ℝ ![a, b, c, d] (n := 2) (by simp)]
    calc finrank ℝ (vectorSpan ℝ (Set.range ![a, b, c, d]))
        ≤ finrank ℝ (EuclideanSpace ℝ (Fin 2)) := Submodule.finrank_le _
      _ = 2 := by simp
  obtain ⟨I, O, hO1, hO2⟩ := Convex.radon_partition (𝕜 := ℝ) hdep
  -- The `simp` set that computes `![a,b,c,d] '' ↑{literal}` and reduces `convexHull` of an
  -- explicit 1- or 2-element set.
  by_cases h0 : (0 : Fin 4) ∈ I
  · by_cases h1 : (1 : Fin 4) ∈ I
    · by_cases h2 : (2 : Fin 4) ∈ I
      · by_cases h3 : (3 : Fin 4) ∈ I
        · -- I = univ, Iᶜ = ∅
          have hIc : Iᶜ = ∅ := by ext i; fin_cases i <;> simp_all
          rw [hIc] at hO2
          simp only [Set.image_empty, convexHull_empty,
            Set.mem_empty_iff_false] at hO2
        · -- I = {0,1,2}, Iᶜ = {3} : lone d
          have hI : I = {0, 1, 2} := by ext i; fin_cases i <;> simp_all
          have hIc : Iᶜ = {3} := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1; rw [hIc] at hO2
          simp only [Set.image_insert_eq,
            Set.image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, convexHull_singleton,
            Set.mem_singleton_iff] at hO1 hO2
          rw [hO2] at hO1
          have h : d ∈ segment ℝ a b :=
            lone_in_hull a b c d D (by rw [dist_comm]; exact hcd) hca hcb hO1
          exact ⟨d, mem_segment_iff_wbtw.1 h, wbtw_self_right ℝ c d⟩
      · by_cases h3 : (3 : Fin 4) ∈ I
        · -- I = {0,1,3}, Iᶜ = {2} : lone c
          have hI : I = {0, 1, 3} := by ext i; fin_cases i <;> simp_all
          have hIc : Iᶜ = {2} := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1; rw [hIc] at hO2
          simp only [Set.image_insert_eq,
            Set.image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, convexHull_singleton,
            Set.mem_singleton_iff] at hO1 hO2
          rw [hO2] at hO1
          have h : c ∈ segment ℝ a b := lone_in_hull a b d c D hcd hda hdb hO1
          exact ⟨c, mem_segment_iff_wbtw.1 h, wbtw_self_left ℝ c d⟩
        · -- I = {0,1}, Iᶜ = {2,3} : pair ab | cd
          have hI : I = {0, 1} := by ext i; fin_cases i <;> simp_all
          have hIc : Iᶜ = {2, 3} := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1; rw [hIc] at hO2
          simp only [Set.image_insert_eq,
            Set.image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, convexHull_pair]
            at hO1 hO2
          exact ⟨O, mem_segment_iff_wbtw.1 hO1, mem_segment_iff_wbtw.1 hO2⟩
    · by_cases h2 : (2 : Fin 4) ∈ I
      · by_cases h3 : (3 : Fin 4) ∈ I
        · -- I = {0,2,3}, Iᶜ = {1} : lone b
          have hI : I = {0, 2, 3} := by ext i; fin_cases i <;> simp_all
          have hIc : Iᶜ = {1} := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1; rw [hIc] at hO2
          simp only [Set.image_insert_eq,
            Set.image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, convexHull_singleton,
            Set.mem_singleton_iff] at hO1 hO2
          rw [hO2] at hO1
          have hmem : b ∈ convexHull ℝ ({c, d, a} : Set (EuclideanSpace ℝ (Fin 2))) := by
            rw [show ({a, c, d} : Set (EuclideanSpace ℝ (Fin 2))) = {c, d, a} from by
              ext z; simp; tauto] at hO1
            exact hO1
          have h : b ∈ segment ℝ c d :=
            lone_in_hull c d a b D (by rw [dist_comm]; exact hab) hac had hmem
          exact ⟨b, wbtw_self_right ℝ a b, mem_segment_iff_wbtw.1 h⟩
        · -- I = {0,2}, Iᶜ = {1,3} : diagonal ac | bd
          have hI : I = {0, 2} := by ext i; fin_cases i <;> simp_all
          have hIc : Iᶜ = {1, 3} := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1; rw [hIc] at hO2
          simp only [Set.image_insert_eq,
            Set.image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, convexHull_pair]
            at hO1 hO2
          obtain ⟨w1, w2⟩ := diag_cross a b c d O D hab hcd hac hbd
            (mem_segment_iff_wbtw.1 hO1) (mem_segment_iff_wbtw.1 hO2)
          exact ⟨O, w1, w2⟩
      · by_cases h3 : (3 : Fin 4) ∈ I
        · -- I = {0,3}, Iᶜ = {1,2} : diagonal ad | bc
          have hI : I = {0, 3} := by ext i; fin_cases i <;> simp_all
          have hIc : Iᶜ = {1, 2} := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1; rw [hIc] at hO2
          simp only [Set.image_insert_eq,
            Set.image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, convexHull_pair]
            at hO1 hO2
          obtain ⟨w1, w2⟩ := diag_cross a b d c O D hab (by rw [dist_comm]; exact hcd) had hbc
            (mem_segment_iff_wbtw.1 hO1) (mem_segment_iff_wbtw.1 hO2)
          exact ⟨O, w1, w2.symm⟩
        · -- I = {0}, Iᶜ = {1,2,3} : lone a
          have hI : I = {0} := by ext i; fin_cases i <;> simp_all
          have hIc : Iᶜ = {1, 2, 3} := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1; rw [hIc] at hO2
          simp only [Set.image_insert_eq,
            Set.image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, convexHull_singleton,
            Set.mem_singleton_iff] at hO1 hO2
          rw [hO1] at hO2
          have hmem : a ∈ convexHull ℝ ({c, d, b} : Set (EuclideanSpace ℝ (Fin 2))) := by
            rw [show ({b, c, d} : Set (EuclideanSpace ℝ (Fin 2))) = {c, d, b} from by
              ext z; simp; tauto] at hO2
            exact hO2
          have h : a ∈ segment ℝ c d := lone_in_hull c d b a D hab hbc hbd hmem
          exact ⟨a, wbtw_self_left ℝ a b, mem_segment_iff_wbtw.1 h⟩
  · by_cases h1 : (1 : Fin 4) ∈ I
    · by_cases h2 : (2 : Fin 4) ∈ I
      · by_cases h3 : (3 : Fin 4) ∈ I
        · -- I = {1,2,3}, Iᶜ = {0} : lone a
          have hI : I = {1, 2, 3} := by ext i; fin_cases i <;> simp_all
          have hIc : Iᶜ = {0} := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1; rw [hIc] at hO2
          simp only [Set.image_insert_eq,
            Set.image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, convexHull_singleton,
            Set.mem_singleton_iff] at hO1 hO2
          rw [hO2] at hO1
          have hmem : a ∈ convexHull ℝ ({c, d, b} : Set (EuclideanSpace ℝ (Fin 2))) := by
            rw [show ({b, c, d} : Set (EuclideanSpace ℝ (Fin 2))) = {c, d, b} from by
              ext z; simp; tauto] at hO1
            exact hO1
          have h : a ∈ segment ℝ c d := lone_in_hull c d b a D hab hbc hbd hmem
          exact ⟨a, wbtw_self_left ℝ a b, mem_segment_iff_wbtw.1 h⟩
        · -- I = {1,2}, Iᶜ = {0,3} : diagonal bc | ad
          have hI : I = {1, 2} := by ext i; fin_cases i <;> simp_all
          have hIc : Iᶜ = {0, 3} := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1; rw [hIc] at hO2
          simp only [Set.image_insert_eq,
            Set.image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, convexHull_pair]
            at hO1 hO2
          obtain ⟨w1, w2⟩ := diag_cross a b d c O D hab (by rw [dist_comm]; exact hcd) had hbc
            (mem_segment_iff_wbtw.1 hO2) (mem_segment_iff_wbtw.1 hO1)
          exact ⟨O, w1, w2.symm⟩
      · by_cases h3 : (3 : Fin 4) ∈ I
        · -- I = {1,3}, Iᶜ = {0,2} : diagonal bd | ac
          have hI : I = {1, 3} := by ext i; fin_cases i <;> simp_all
          have hIc : Iᶜ = {0, 2} := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1; rw [hIc] at hO2
          simp only [Set.image_insert_eq,
            Set.image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, convexHull_pair]
            at hO1 hO2
          obtain ⟨w1, w2⟩ := diag_cross a b c d O D hab hcd hac hbd
            (mem_segment_iff_wbtw.1 hO2) (mem_segment_iff_wbtw.1 hO1)
          exact ⟨O, w1, w2⟩
        · -- I = {1}, Iᶜ = {0,2,3} : lone b
          have hI : I = {1} := by ext i; fin_cases i <;> simp_all
          have hIc : Iᶜ = {0, 2, 3} := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1; rw [hIc] at hO2
          simp only [Set.image_insert_eq,
            Set.image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, convexHull_singleton,
            Set.mem_singleton_iff] at hO1 hO2
          rw [hO1] at hO2
          have hmem : b ∈ convexHull ℝ ({c, d, a} : Set (EuclideanSpace ℝ (Fin 2))) := by
            rw [show ({a, c, d} : Set (EuclideanSpace ℝ (Fin 2))) = {c, d, a} from by
              ext z; simp; tauto] at hO2
            exact hO2
          have h : b ∈ segment ℝ c d :=
            lone_in_hull c d a b D (by rw [dist_comm]; exact hab) hac had hmem
          exact ⟨b, wbtw_self_right ℝ a b, mem_segment_iff_wbtw.1 h⟩
    · by_cases h2 : (2 : Fin 4) ∈ I
      · by_cases h3 : (3 : Fin 4) ∈ I
        · -- I = {2,3}, Iᶜ = {0,1} : pair cd | ab
          have hI : I = {2, 3} := by ext i; fin_cases i <;> simp_all
          have hIc : Iᶜ = {0, 1} := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1; rw [hIc] at hO2
          simp only [Set.image_insert_eq,
            Set.image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, convexHull_pair]
            at hO1 hO2
          exact ⟨O, mem_segment_iff_wbtw.1 hO2, mem_segment_iff_wbtw.1 hO1⟩
        · -- I = {2}, Iᶜ = {0,1,3} : lone c
          have hI : I = {2} := by ext i; fin_cases i <;> simp_all
          have hIc : Iᶜ = {0, 1, 3} := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1; rw [hIc] at hO2
          simp only [Set.image_insert_eq,
            Set.image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, convexHull_singleton,
            Set.mem_singleton_iff] at hO1 hO2
          rw [hO1] at hO2
          have h : c ∈ segment ℝ a b := lone_in_hull a b d c D hcd hda hdb hO2
          exact ⟨c, mem_segment_iff_wbtw.1 h, wbtw_self_left ℝ c d⟩
      · by_cases h3 : (3 : Fin 4) ∈ I
        · -- I = {3}, Iᶜ = {0,1,2} : lone d
          have hI : I = {3} := by ext i; fin_cases i <;> simp_all
          have hIc : Iᶜ = {0, 1, 2} := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1; rw [hIc] at hO2
          simp only [Set.image_insert_eq,
            Set.image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, convexHull_singleton,
            Set.mem_singleton_iff] at hO1 hO2
          rw [hO1] at hO2
          have h : d ∈ segment ℝ a b :=
            lone_in_hull a b c d D (by rw [dist_comm]; exact hcd) hca hcb hO2
          exact ⟨d, mem_segment_iff_wbtw.1 h, wbtw_self_right ℝ c d⟩
        · -- I = ∅
          have hI : I = ∅ := by ext i; fin_cases i <;> simp_all
          rw [hI] at hO1
          simp only [Set.image_empty, convexHull_empty,
            Set.mem_empty_iff_false] at hO1

end HopfPannwitz
