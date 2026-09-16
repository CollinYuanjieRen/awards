import MerLeanExperiment.Erdos318Definitions

namespace ReciprocalSquares

theorem mem_signed_square_domain_iff (n : ℕ) :
    n ∈ (({n : ℕ | IsSquare n} \ {1}) \ {0} : Set ℕ) ↔ 1 < n ∧ IsSquare n := by
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hsq, h1⟩, h0⟩
    exact ⟨by omega, hsq⟩
  · rintro ⟨hgt, hsq⟩
    exact ⟨⟨hsq, by omega⟩, by omega⟩

/-- The two nonconstant clauses in the canonical statement supply both color witnesses. -/
theorem signed_square_color_witnesses (f : ℕ → ℝ)
    (hplus : f ∘ (Subtype.val :
      (({n : ℕ | IsSquare n} \ {1}) \ {0} : Set ℕ) → ℕ) ≠ (fun _ => 1))
    (hminus : f ∘ (Subtype.val :
      (({n : ℕ | IsSquare n} \ {1}) \ {0} : Set ℕ) → ℕ) ≠ (fun _ => -1))
    (hrange : Set.range f ⊆ {1, -1}) :
    (∃ n : ℕ, 1 < n ∧ IsSquare n ∧ f n = 1) ∧
      (∃ n : ℕ, 1 < n ∧ IsSquare n ∧ f n = -1) := by
  classical
  have hsigned (n : ℕ) : f n = 1 ∨ f n = -1 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      hrange (Set.mem_range_self n)
  constructor
  · obtain ⟨n, hn⟩ := Function.ne_iff.mp hminus
    have hdomain := (mem_signed_square_domain_iff n.val).mp n.property
    have hvalue : f n.val = 1 := (hsigned n.val).resolve_right hn
    exact ⟨n.val, hdomain.1, hdomain.2, hvalue⟩
  · obtain ⟨n, hn⟩ := Function.ne_iff.mp hplus
    have hdomain := (mem_signed_square_domain_iff n.val).mp n.property
    have hvalue : f n.val = -1 := (hsigned n.val).resolve_left hn
    exact ⟨n.val, hdomain.1, hdomain.2, hvalue⟩

/-- Opposite-color equal reciprocal sums give the canonical signed zero sum. -/
theorem signed_zero_sum_of_equal_reciprocals (f : ℕ → ℝ) (A B : Finset ℕ)
    (hAne : A.Nonempty)
    (hA : ∀ n ∈ A, 1 < n ∧ IsSquare n ∧ f n = 1)
    (hB : ∀ n ∈ B, 1 < n ∧ IsSquare n ∧ f n = -1)
    (heq : (∑ n ∈ A, (1 : ℚ) / n) = ∑ n ∈ B, (1 : ℚ) / n) :
    ∃ S : Finset ℕ, S.Nonempty ∧
      (↑S : Set ℕ) ⊆ ({n : ℕ | IsSquare n} \ {1}) \ {0} ∧
      ∑ n ∈ S, f n / n = 0 := by
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro n hnA hnB
    have hplus := (hA n hnA).2.2
    have hminus := (hB n hnB).2.2
    linarith
  refine ⟨A ∪ B, hAne.mono (Finset.subset_union_left), ?_, ?_⟩
  · intro n hn
    apply (mem_signed_square_domain_iff n).mpr
    rcases Finset.mem_union.mp hn with hnA | hnB
    · exact ⟨(hA n hnA).1, (hA n hnA).2.1⟩
    · exact ⟨(hB n hnB).1, (hB n hnB).2.1⟩
  · have heqR : (∑ n ∈ A, (1 : ℝ) / n) = ∑ n ∈ B, (1 : ℝ) / n := by
      have h := congrArg (fun z : ℚ => (z : ℝ)) heq
      simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using h
    rw [Finset.sum_union hdisj]
    have hAsum : (∑ n ∈ A, f n / (n : ℝ)) = ∑ n ∈ A, (1 : ℝ) / n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [(hA n hn).2.2]
    have hBsum : (∑ n ∈ B, f n / (n : ℝ)) = -(∑ n ∈ B, (1 : ℝ) / n) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      rw [(hB n hn).2.2, neg_div]
    rw [hAsum, hBsum, heqR]
    ring

end ReciprocalSquares
