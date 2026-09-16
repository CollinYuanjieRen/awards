import MerLeanExperiment.SquareMass

namespace ReciprocalSquares

/-- The denominators of `F` outside the selected color. -/
noncomputable def oppositeColor (F : Finset ℕ) (X : Set ℕ) : Finset ℕ := by
  classical
  exact F.filter (fun d => d ∉ X)

/-- The mass of one color is positive and bounded below by any witness in that
color, while a witness in the other color gives a lower bound for the omitted
mass. -/
theorem color_mass_bounds
    (F : Finset ℕ) (X : Set ℕ) (x y : ℕ)
    (hF : ∀ d ∈ F, 1 < d ∧ IsSquare d)
    (hx : x ∈ F) (hxX : x ∈ X)
    (hy : y ∈ F) (hyX : y ∉ X) :
    let Y := oppositeColor F X
    0 < recipSumQ Y ∧
      (1 : ℚ) / (y : ℚ) ≤ recipSumQ Y ∧
      recipSumQ Y ≤ recipSumQ F ∧
      recipSumQ F ≤ 3 / 4 ∧
      (1 : ℚ) / (x : ℚ) ≤ recipSumQ F - recipSumQ Y := by
  classical
  dsimp only
  let Y := oppositeColor F X
  let C := F.filter (fun d => d ∈ X)
  have hxpos : 0 < x := by have := (hF x hx).1; omega
  have hypos : 0 < y := by have := (hF y hy).1; omega
  have hxq : (0 : ℚ) < x := by exact_mod_cast hxpos
  have hyq : (0 : ℚ) < y := by exact_mod_cast hypos
  have hyY : y ∈ Y := by
    simpa only [Y, oppositeColor, Finset.mem_filter] using And.intro hy hyX
  have hxC : x ∈ C := Finset.mem_filter.mpr ⟨hx, hxX⟩
  have hnonneg : ∀ d ∈ F, (0 : ℚ) ≤ 1 / (d : ℚ) := by
    intro d hd
    have hdpos : 0 < d := by have := (hF d hd).1; omega
    have hdq : (0 : ℚ) < d := by exact_mod_cast hdpos
    positivity
  have hyterm : (1 : ℚ) / (y : ℚ) ≤ recipSumQ Y := by
    unfold recipSumQ
    apply Finset.single_le_sum
      (f := fun d : ℕ => (1 : ℚ) / (d : ℚ))
    · intro d hd
      exact hnonneg d (Finset.mem_filter.mp hd).1
    · exact hyY
  have hYpos : 0 < recipSumQ Y :=
    (one_div_pos.mpr hyq).trans_le hyterm
  have hYsub : Y ⊆ F := by
    intro d hd
    exact (by
      simpa only [Y, oppositeColor, Finset.mem_filter] using hd : d ∈ F ∧ d ∉ X).1
  have hYle : recipSumQ Y ≤ recipSumQ F := by
    unfold recipSumQ
    exact Finset.sum_le_sum_of_subset_of_nonneg hYsub
      (fun d hd _ => hnonneg d hd)
  have hFle : recipSumQ F ≤ 3 / 4 :=
    recipSumQ_square_le_three_quarters F hF
  have hsplit : recipSumQ Y + recipSumQ C = recipSumQ F := by
    unfold recipSumQ
    simpa only [Y, oppositeColor, C, not_not] using
      Finset.sum_filter_add_sum_filter_not F (fun d => d ∉ X)
        (fun d => (1 : ℚ) / (d : ℚ))
  have hxterm : (1 : ℚ) / (x : ℚ) ≤ recipSumQ C := by
    unfold recipSumQ
    apply Finset.single_le_sum
      (f := fun d : ℕ => (1 : ℚ) / (d : ℚ))
    · intro d hd
      exact hnonneg d (Finset.mem_filter.mp hd).1
    · exact hxC
  have hxgap : (1 : ℚ) / (x : ℚ) ≤ recipSumQ F - recipSumQ Y := by
    linarith
  exact ⟨hYpos, hyterm, hYle, hFle, hxgap⟩

/-- The two color witnesses give the strict initial slack and the coarse mass
ratio needed by the finite greedy selection. -/
theorem color_mass_initial_ratio
    (F : Finset ℕ) (X : Set ℕ) (x y : ℕ)
    (hF : ∀ d ∈ F, 1 < d ∧ IsSquare d)
    (hx : x ∈ F) (hxX : x ∈ X)
    (hy : y ∈ F) (hyX : y ∉ X)
    (ε A : ℚ) (hεpos : 0 < ε)
    (hεle : ε ≤ 1 / (10 * (x : ℚ)))
    (hA : (y : ℚ) ≤ A) :
    let Y := oppositeColor F X
    (1 + ε / 8) * recipSumQ Y < recipSumQ F ∧
      recipSumQ F ≤ A * recipSumQ Y := by
  classical
  dsimp only
  let Y := oppositeColor F X
  obtain ⟨hYpos, hyterm, hYle, hFle, hxgap⟩ :=
    color_mass_bounds F X x y hF hx hxX hy hyX
  have hxpos : 0 < x := by have := (hF x hx).1; omega
  have hypos : 0 < y := by have := (hF y hy).1; omega
  have hxq : (0 : ℚ) < x := by exact_mod_cast hxpos
  have hyq : (0 : ℚ) < y := by exact_mod_cast hypos
  have hεeight_pos : (0 : ℚ) < ε / 8 := div_pos hεpos (by norm_num)
  have hYone : recipSumQ Y ≤ 1 := by
    linarith
  have hεdiv : ε / 8 ≤ 1 / (80 * (x : ℚ)) := by
    calc
      ε / 8 ≤ (1 / (10 * (x : ℚ))) / 8 :=
        div_le_div_of_nonneg_right hεle (by norm_num)
      _ = 1 / (80 * (x : ℚ)) := by ring
  have hcoeff0 : (0 : ℚ) ≤ 1 / (80 * (x : ℚ)) := by positivity
  have hsmall : ε / 8 * recipSumQ Y < 1 / (x : ℚ) := by
    calc
      ε / 8 * recipSumQ Y ≤
          (1 / (80 * (x : ℚ))) * recipSumQ Y :=
        mul_le_mul_of_nonneg_right hεdiv hYpos.le
      _ ≤ (1 / (80 * (x : ℚ))) * 1 :=
        mul_le_mul_of_nonneg_left hYone hcoeff0
      _ < 1 / (x : ℚ) := by
        have hlt : 1 / (80 * (x : ℚ)) < 1 / (x : ℚ) := by
          apply one_div_lt_one_div_of_lt hxq
          nlinarith
        simpa using hlt
  have hstrict : (1 + ε / 8) * recipSumQ Y < recipSumQ F := by
    rw [add_mul, one_mul]
    linarith [hεeight_pos]
  have hA0 : (0 : ℚ) ≤ A := by linarith
  have hratio_lower : (1 : ℚ) ≤ A * recipSumQ Y := by
    have hmul : (y : ℚ) * (1 / (y : ℚ)) ≤ A * recipSumQ Y :=
      mul_le_mul hA hyterm (by positivity) hA0
    have hyne : (y : ℚ) ≠ 0 := ne_of_gt hyq
    field_simp [hyne] at hmul
    exact hmul
  have hratio : recipSumQ F ≤ A * recipSumQ Y := by
    linarith
  exact ⟨hstrict, hratio⟩

end ReciprocalSquares
