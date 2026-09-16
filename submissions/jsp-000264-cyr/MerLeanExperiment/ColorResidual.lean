import MerLeanExperiment.PrefixReserve
import MerLeanExperiment.ColorMass

namespace ReciprocalSquares

theorem squareZ_erase_one_members (N : ℕ) :
    ∀ d ∈ (squareZ N).erase 1, 1 < d ∧ IsSquare d := by
  intro d hd
  obtain ⟨hd1, hdZ⟩ := Finset.mem_erase.mp hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hdZ
  have hapos := rootsZ_pos ha
  refine ⟨?_, ⟨a, pow_two a⟩⟩
  have := pow_pos hapos 2
  omega

/-- Every fixed square denominator greater than one eventually belongs to the construction. -/
theorem square_mem_squareZ_erase_one_of_le (N d : ℕ) (hN : 2 ≤ N)
    (hd : 1 < d) (hsquare : IsSquare d) (hdN : d ≤ N) :
    d ∈ (squareZ N).erase 1 := by
  obtain ⟨a, rfl⟩ := hsquare
  apply Finset.mem_erase.mpr
  refine ⟨by omega, ?_⟩
  have hapos : 0 < a := by nlinarith
  have haN : a ≤ N := by nlinarith
  have ha : a ∈ smoothRoots N := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hNN : N < N ^ 3 := by
        calc
          N < N ^ 2 := by nlinarith
          _ ≤ N ^ 3 := pow_le_pow_right₀ (by omega : 1 ≤ N) (by decide)
      exact haN.trans_lt hNN
    · exact Nat.mem_smoothNumbers_of_lt hapos (by omega)
  exact Finset.mem_image.mpr
    ⟨a, smoothRoots_subset_rootsZ N ha, pow_two a⟩

/-- The exact coloring witnesses instantiate every initial greedy condition. -/
theorem exists_color_residual (N x y : ℕ) (X : Set ℕ) (ε A : ℚ)
    (hN : 20 < N)
    (hx : x ∈ (squareZ N).erase 1) (hxX : x ∈ X)
    (hy : y ∈ (squareZ N).erase 1) (hyX : y ∉ X)
    (hε : 0 < ε) (hεle : ε ≤ 1 / (10 * (x : ℚ)))
    (hεN : 3 ≤ ε ^ 2 * (N : ℚ))
    (hA : (y : ℚ) ≤ A) (hcap : 1 + ε / 8 ≤ ε * A) :
    ∃ S : Finset ℕ, S ⊆ (squareE N).erase 1 ∧
      0 < recipSumQ (oppositeColor ((squareZ N).erase 1) X) - recipSumQ S ∧
      (1 + ε / 8) *
          (recipSumQ (oppositeColor ((squareZ N).erase 1) X) - recipSumQ S) <
        recipSumQ (squareD N) ∧
      recipSumQ (squareD N) ≤ A *
        (recipSumQ (oppositeColor ((squareZ N).erase 1) X) - recipSumQ S) := by
  have hF := squareZ_erase_one_members N
  have hxpos : (0 : ℚ) < x := by
    exact_mod_cast (show 0 < x by have := (hF x hx).1; omega)
  have hxone : (1 : ℚ) ≤ x := by
    exact_mod_cast (show 1 ≤ x by have := (hF x hx).1; omega)
  have hεsmall : ε ≤ 1 / 10 := hεle.trans (by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 10)
    linarith)
  obtain ⟨hb, _, _, _, _⟩ :=
    color_mass_bounds ((squareZ N).erase 1) X x y hF hx hxX hy hyX
  obtain ⟨hlo, hhi⟩ := color_mass_initial_ratio
    ((squareZ N).erase 1) X x y hF hx hxX hy hyX ε A hε hεle hA
  rw [← prefix_reserve_mass_eq N (by omega)] at hlo hhi
  obtain ⟨S, hS, hpos, hlow, hupp⟩ := exists_greedy_prefix_roots N ε
    (recipSumQ (oppositeColor ((squareZ N).erase 1) X)) A
    hN hε hεsmall hεN hcap hb hlo hhi
  refine ⟨S.image (fun j => j ^ 2), ?_, ?_⟩
  · intro d hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hj1, hjE⟩ := Finset.mem_erase.mp (hS hj)
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_image.mpr ⟨j, hjE, rfl⟩⟩
    intro heq
    have hj : j = 1 := by nlinarith
    exact hj1 hj
  · rw [recipSumQ_square_image]
    exact ⟨hpos, hlow, hupp⟩

end ReciprocalSquares
