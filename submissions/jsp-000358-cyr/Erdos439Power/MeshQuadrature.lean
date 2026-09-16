import Erdos439Power.RealPhase

open scoped BigOperators
open Erdos439 Erdos439.PowerDecay

namespace Erdos439Power

lemma sum_normalizedPowerGap (k L N : ℕ) :
    (∑ n ∈ Finset.range N, normalizedPowerGap k L n) = normalizedPower k L N := by
  unfold normalizedPowerGap
  simpa using Finset.sum_range_sub (fun n => (normalizedPower k L n : ℝ)) N

lemma gap_mul_value_eq_sum (k L n : ℕ) (f : ℕ → ℂ) :
    (normalizedPowerGap k L n : ℂ) * f (normalizedPower k L n) =
      ∑ _s ∈ Finset.Ico (normalizedPower k L n) (normalizedPower k L (n + 1)),
        f (normalizedPower k L n) := by
  have hmono := (normalizedPower_strictMono k L (Nat.lt_succ_self n)).le
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, normalizedPowerGap]
  rw [Nat.cast_sub hmono]
  push_cast
  rfl

/-- The mesh Riemann sum is compared directly with the complete finite sum. -/
theorem norm_mesh_quadrature_le (k L N : ℕ) (f : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ a b : ℕ, a ≤ b → ‖f a - f b‖ ≤ K * ((b : ℝ) - a)) :
    ‖(∑ n ∈ Finset.range N, (normalizedPowerGap k L n : ℂ) *
        f (normalizedPower k L n)) -
      ∑ s ∈ Finset.range (normalizedPower k L N), f s‖ ≤
      K * normalizedPowerGap k L N * normalizedPower k L N := by
  have hrepr : (∑ n ∈ Finset.range N, (normalizedPowerGap k L n : ℂ) *
        f (normalizedPower k L n)) -
      ∑ s ∈ Finset.range (normalizedPower k L N), f s =
      ∑ n ∈ Finset.range N,
        ∑ s ∈ Finset.Ico (normalizedPower k L n) (normalizedPower k L (n + 1)),
          (f (normalizedPower k L n) - f s) := by
    simp_rw [gap_mul_value_eq_sum]
    rw [← sum_valueIntervals k L N f, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.sum_sub_distrib]
  rw [hrepr]
  calc
    ‖∑ n ∈ Finset.range N,
        ∑ s ∈ Finset.Ico (normalizedPower k L n) (normalizedPower k L (n + 1)),
          (f (normalizedPower k L n) - f s)‖ ≤
      ∑ n ∈ Finset.range N,
        ∑ s ∈ Finset.Ico (normalizedPower k L n) (normalizedPower k L (n + 1)),
          ‖f (normalizedPower k L n) - f s‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => norm_sum_le _ _))
    _ ≤ ∑ n ∈ Finset.range N,
        normalizedPowerGap k L n * (K * normalizedPowerGap k L N) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnN : n ≤ N := (Finset.mem_range.mp hn).le
      have hgapmono : normalizedPowerGap k L n ≤ normalizedPowerGap k L N :=
        (monotone_nat_of_le_succ (normalizedPowerGap_mono k L)) hnN
      calc
        (∑ s ∈ Finset.Ico (normalizedPower k L n) (normalizedPower k L (n + 1)),
            ‖f (normalizedPower k L n) - f s‖) ≤
            ∑ _s ∈ Finset.Ico (normalizedPower k L n) (normalizedPower k L (n + 1)),
              K * normalizedPowerGap k L N := by
          apply Finset.sum_le_sum
          intro s hs
          refine (hf _ s (Finset.mem_Ico.mp hs).1).trans ?_
          apply mul_le_mul_of_nonneg_left _ hK
          have hsle : (s : ℝ) ≤ normalizedPower k L (n + 1) := by
            exact_mod_cast (Finset.mem_Ico.mp hs).2.le
          unfold normalizedPowerGap at hgapmono ⊢
          linarith
        _ = normalizedPowerGap k L n * (K * normalizedPowerGap k L N) := by
          simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, normalizedPowerGap]
          rw [Nat.cast_sub (normalizedPower_strictMono k L (Nat.lt_succ_self n)).le]
    _ = K * normalizedPowerGap k L N * normalizedPower k L N := by
      rw [← Finset.sum_mul, sum_normalizedPowerGap]
      ring

end Erdos439Power
