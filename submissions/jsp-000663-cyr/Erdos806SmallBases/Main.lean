import Erdos806SmallBases.Params

/-! # Erdős Problem 806 -/

namespace Erdos806

open Filter Asymptotics

/-- A crude bound: `A` itself (together with `0`) is a basis for `A`, so the minimal basis size for
subsets of `Finset.Icc 1 n` of size at most `√n` is at most `n + 1`. This makes the predicate
`∃ m, …` below nonempty, so that `Nat.find` can pick the least such bound. -/
private theorem exists_trivial_basis_card_bound (n : ℕ) :
    ∃ m : ℕ, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → (A.card : ℝ) ≤ Real.sqrt n →
      ∃ B : Finset ℤ, HasBasis A B ∧ B.card ≤ m := by
  refine ⟨n + 1, fun A hA _ => ⟨insert 0 (A.image (Nat.cast : ℕ → ℤ)), ?_, ?_⟩⟩
  · intro a ha
    exact ⟨0, Finset.mem_insert_self _ _, (a : ℤ),
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha), by ring⟩
  · have hcard : A.card ≤ n := by
      have := Finset.card_le_card hA
      rw [Nat.card_Icc] at this
      omega
    calc (insert (0 : ℤ) (A.image (Nat.cast : ℕ → ℤ))).card
        ≤ (A.image (Nat.cast : ℕ → ℤ)).card + 1 := Finset.card_insert_le _ _
      _ ≤ A.card + 1 := by gcongr; exact Finset.card_image_le
      _ ≤ n + 1 := by omega

/-- Erdős Problem 806 (Erdős–Newman; answered by Alon–Bukh–Sudakov): there is a bound
`β n = o(√n)` such that every `A ⊆ {1, …, n}` with `|A| ≤ √n` is contained in `B + B` for some
`B ⊂ ℤ` with `|B| ≤ β n`. -/
theorem erdos_806 :
    ∃ β : ℕ → ℕ, (fun n : ℕ => (β n : ℝ)) =o[atTop] (fun n : ℕ => Real.sqrt n) ∧
      ∀ n, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → (A.card : ℝ) ≤ Real.sqrt n →
        ∃ B : Finset ℤ, HasBasis A B ∧ B.card ≤ β n := by
  classical
  refine ⟨fun n => Nat.find (exists_trivial_basis_card_bound n), ?_,
    fun n => Nat.find_spec (exists_trivial_basis_card_bound n)⟩
  refine Asymptotics.isLittleO_iff.2 (fun c hc => ?_)
  obtain ⟨N, hN⟩ := erdos_806_eps c hc
  refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have hfloor : Nat.find (exists_trivial_basis_card_bound n) ≤ ⌊c * Real.sqrt n⌋₊ := by
    refine Nat.find_min' _ (fun A hA hcard => ?_)
    obtain ⟨B, hB, hBcard⟩ := hN n hn A hA hcard
    exact ⟨B, hB, Nat.le_floor hBcard⟩
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc ((Nat.find (exists_trivial_basis_card_bound n) : ℕ) : ℝ) ≤ (⌊c * Real.sqrt n⌋₊ : ℝ) :=
        Nat.cast_le.2 hfloor
    _ ≤ c * Real.sqrt n := Nat.floor_le (by positivity)

end Erdos806
