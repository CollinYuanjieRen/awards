import MerLeanExperiment.IntervalRetained
import MerLeanExperiment.SortedPrefix
import MerLeanExperiment.SquareMass

namespace ReciprocalSquares

theorem recipSumQ_square_image (s : Finset ℕ) :
    recipSumQ (s.image (fun j => j ^ 2)) =
      ∑ j ∈ s, (1 : ℚ) / (j : ℚ) ^ 2 := by
  rw [recipSumQ, Finset.sum_image (fun a _ b _ hab =>
    Nat.pow_left_injective (by decide : 2 ≠ 0) hab)]
  simp only [Nat.cast_pow]

/-- The initial mass is exactly the disjoint prefix and retained reserve. -/
theorem prefix_reserve_mass_eq (N : ℕ) (hN : 2 ≤ N) :
    recipSumQ (squareD N) +
      listMass (fun j : ℕ => (1 : ℚ) / (j : ℚ) ^ 2) (prefixList N) =
    recipSumQ ((squareZ N).erase 1) := by
  have hEsub : prefixRoots N ⊆ rootsZ N :=
    (prefixRoots_subset_smoothRoots N (by omega)).trans (smoothRoots_subset_rootsZ N)
  have h1E : 1 ∈ prefixRoots N := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      nlinarith
    · simp only [Nat.mem_smoothNumbers]
      exact ⟨by decide, by simp⟩
  have hunion : (rootsZ N).erase 1 = retainedRoots N ∪ (prefixRoots N).erase 1 := by
    ext j
    simp only [retainedRoots, Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff]
    constructor
    · rintro ⟨hne, hj⟩
      by_cases hE : j ∈ prefixRoots N
      · exact Or.inr ⟨hne, hE⟩
      · exact Or.inl ⟨hj, hE⟩
    · rintro (⟨hj, hnot⟩ | ⟨hne, hE⟩)
      · exact ⟨by intro h; subst j; exact hnot h1E, hj⟩
      · exact ⟨hne, hEsub hE⟩
  have hdisj : Disjoint (retainedRoots N) ((prefixRoots N).erase 1) := by
    apply Finset.disjoint_left.mpr
    intro j hjR hjE
    exact (Finset.mem_sdiff.mp hjR).2 (Finset.mem_of_mem_erase hjE)
  have himage : ((rootsZ N).erase 1).image (fun j => j ^ 2) =
      (squareZ N).erase 1 := by
    simpa only [one_pow, squareZ] using
      Finset.image_erase (Nat.pow_left_injective (by decide : 2 ≠ 0)) (rootsZ N) 1
  rw [← himage, recipSumQ_square_image, hunion, Finset.sum_union hdisj]
  rw [squareD_eq_image_retainedRoots, recipSumQ_square_image]
  congr 1
  unfold listMass prefixList
  rw [← List.sum_toFinset _ (Finset.sort_nodup _ _)]
  simp

/-- Every retained interval term belongs to the reserve or the remaining prefix. -/
theorem interval_mass_le_reserve (N d : ℕ) :
    (∑ j ∈ (Finset.Icc (d + 1) (20 * d)) ∩ rootsZ N,
      (1 : ℚ) / (j : ℚ) ^ 2) ≤
    recipSumQ (squareD N) +
      ∑ j ∈ (prefixRoots N).filter (fun j => d < j), (1 : ℚ) / (j : ℚ) ^ 2 := by
  have hsub : (Finset.Icc (d + 1) (20 * d)) ∩ rootsZ N ⊆
      retainedRoots N ∪ (prefixRoots N).filter (fun j => d < j) := by
    intro j hj
    obtain ⟨hjI, hjZ⟩ := Finset.mem_inter.mp hj
    by_cases hjE : j ∈ prefixRoots N
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hjE, (Finset.mem_Icc.mp hjI).1⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hjZ, hjE⟩)
  have hdisj : Disjoint (retainedRoots N)
      ((prefixRoots N).filter (fun j => d < j)) := by
    apply Finset.disjoint_left.mpr
    intro j hjR hjE
    exact (Finset.mem_sdiff.mp hjR).2 (Finset.mem_filter.mp hjE).1
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun j : ℕ => (1 : ℚ) / (j : ℚ) ^ 2) hsub (by intros; positivity)
  rw [Finset.sum_union hdisj] at hsum
  rw [squareD_eq_image_retainedRoots, recipSumQ_square_image]
  exact hsum

theorem prefixList_greedy_slack (N : ℕ) (ε : ℚ)
    (hN : 20 < N) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10)
    (hεN : 3 ≤ ε ^ 2 * (N : ℚ)) :
    ∀ (pre : List ℕ) (d : ℕ) (post : List ℕ), prefixList N = pre ++ d :: post →
      (1 + ε / 8) * ((1 : ℚ) / (d : ℚ) ^ 2) <
        (1 - ε) * (recipSumQ (squareD N) +
          listMass (fun j : ℕ => (1 : ℚ) / (j : ℚ) ^ 2) post) := by
  intro pre d post hs
  have hdmem : d ∈ prefixList N := by rw [hs]; simp
  obtain ⟨hd2, hdN⟩ := prefixList_mem_bounds N d hdmem
  rw [prefixList_suffix_mass N d pre post hs]
  exact (retained_interval_greedy_slack N d ε hN hd2 hdN hε hεsmall hεN).trans_le
    (mul_le_mul_of_nonneg_left (interval_mass_le_reserve N d) (by linarith))

/-- Greedy deletion instantiated at the exact finite smooth prefix. Initial
mass ratios remain explicit inputs here and must be supplied by the coloring. -/
theorem exists_greedy_prefix_roots (N : ℕ) (ε b A : ℚ)
    (hN : 20 < N) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10)
    (hεN : 3 ≤ ε ^ 2 * (N : ℚ)) (hcap : 1 + ε / 8 ≤ ε * A)
    (hb : 0 < b)
    (hlow : (1 + ε / 8) * b < recipSumQ (squareD N) +
      listMass (fun j : ℕ => (1 : ℚ) / (j : ℚ) ^ 2) (prefixList N))
    (hupp : recipSumQ (squareD N) +
      listMass (fun j : ℕ => (1 : ℚ) / (j : ℚ) ^ 2) (prefixList N) ≤ A * b) :
    ∃ S : Finset ℕ, S ⊆ (prefixRoots N).erase 1 ∧
      0 < b - ∑ j ∈ S, (1 : ℚ) / (j : ℚ) ^ 2 ∧
      (1 + ε / 8) * (b - ∑ j ∈ S, (1 : ℚ) / (j : ℚ) ^ 2) <
        recipSumQ (squareD N) ∧
      recipSumQ (squareD N) ≤ A * (b - ∑ j ∈ S, (1 : ℚ) / (j : ℚ) ^ 2) := by
  obtain ⟨selected, hsub, hpos, hlo, hhi⟩ := exists_greedy_sublist
    (fun j : ℕ => (1 : ℚ) / (j : ℚ) ^ 2) (prefixList N)
    (recipSumQ (squareD N)) b (1 + ε / 8) ε A
    (by linarith) hε (by linarith) hcap (by intros; positivity)
    (prefixList_greedy_slack N ε hN hε hεsmall hεN) hb hlow hupp
  have hnodup : selected.Nodup := hsub.nodup
    (Finset.sort_nodup ((prefixRoots N).erase 1) (· ≤ ·))
  have hmass : listMass (fun j : ℕ => (1 : ℚ) / (j : ℚ) ^ 2) selected =
      ∑ j ∈ selected.toFinset, (1 : ℚ) / (j : ℚ) ^ 2 :=
    (List.sum_toFinset _ hnodup).symm
  rw [hmass] at hpos hlo hhi
  refine ⟨selected.toFinset, ?_, hpos, hlo, hhi⟩
  intro j hj
  exact (Finset.mem_sort (· ≤ ·)).mp
    (hsub.subset (List.mem_toFinset.mp hj))

end ReciprocalSquares
