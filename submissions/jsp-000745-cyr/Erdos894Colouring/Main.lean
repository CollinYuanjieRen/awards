import Erdos894Colouring.Nested
import Erdos894Colouring.Split
import Erdos894Colouring.Colouring

/-! # Erdős Problem 894 -/

namespace Erdos894

/-- Erdős Problem 894 (Katznelson 2001): every lacunary sequence admits a finite colouring of the
integers with no monochromatic pair whose difference is a term of the sequence. -/
theorem erdos_894 (n : ℕ → ℕ) (hn : IsLacunary n) : HasAvoidingColouring n := by
  obtain ⟨r, hr, hsplit⟩ := exists_split_of_isLacunary n hn
  have hθ : ∀ j : ℕ, ∃ θ : ℝ, ∀ i, 1 / 4 ≤ Int.fract (θ * n (j + r * i)) ∧
      Int.fract (θ * n (j + r * i)) ≤ 3 / 4 := fun j =>
    exists_rotation_of_four_mul_le (fun i => n (j + r * i)) (fun i => hn.1 _) (fun i => hsplit j i)
  choose θ hθ using hθ
  exact hasAvoidingColouring_of_rotations n r hr θ (fun j i _ => hθ j i)

/-- The same statement for colourings of the natural numbers. -/
theorem erdos_894_nat (n : ℕ → ℕ) (hn : IsLacunary n) :
    ∃ (r : ℕ) (c : ℕ → Fin r), ∀ a b : ℕ, c a = c b → ∀ k, a ≠ b + n k := by
  obtain ⟨r, c, hc⟩ := erdos_894 n hn
  refine ⟨r, fun a => c a, fun a b hab k hk => hc a b hab k ?_⟩
  subst hk
  push_cast
  ring

/-- Closed form of `erdos_894`: there is no lacunary sequence without an avoiding colouring. -/
theorem erdos_894_closed : ¬ ∃ n : ℕ → ℕ, IsLacunary n ∧ ¬ HasAvoidingColouring n :=
  fun ⟨n, hn, h⟩ => h (erdos_894 n hn)

end Erdos894
