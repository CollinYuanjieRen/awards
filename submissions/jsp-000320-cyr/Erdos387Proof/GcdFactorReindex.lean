import Erdos387Proof.BrunLocalDensity
import Erdos387Proof.CoprimeHarmonic

/-! Exact gcd stratification of a coprime factor interval. -/

namespace Erdos387Proof.GcdFactorReindex

open scoped BigOperators

noncomputable def interval (A B Q : ℕ) : Finset ℕ :=
  (Finset.Ioc A B).filter (fun d => Nat.Coprime d Q)

theorem mul_mem_interval_filter_gcd_iff {A B Q u v t : ℕ}
    (hu : 0 < u) (huQ : Nat.Coprime u Q) :
    u * t ∈ (interval A B Q).filter (fun d => Nat.gcd (u * v) d = u) ↔
      t ∈ interval (A / u) (B / u) (Q * v) := by
  classical
  have hlo : A < u * t ↔ A / u < t := by
    rw [Nat.div_lt_iff_lt_mul hu, Nat.mul_comm t u]
  have hhi : u * t ≤ B ↔ t ≤ B / u := by
    rw [Nat.le_div_iff_mul_le hu, Nat.mul_comm t u]
  simp only [interval, Finset.mem_filter, Finset.mem_Ioc,
    gcd_mul_split_iff hu, hlo, hhi, Nat.coprime_mul_iff_left,
    Nat.coprime_mul_iff_right]
  rw [show Nat.Coprime v t ↔ Nat.Coprime t v from Nat.coprime_comm]
  tauto

/-- Each gcd fibre is exactly the image of the divided interval with the
remaining coprimality condition. No inequality is used in the reindexing. -/
theorem filter_gcd_eq_image {A B Q u v : ℕ}
    (hu : 0 < u) (huQ : Nat.Coprime u Q) :
    (interval A B Q).filter (fun d => Nat.gcd (u * v) d = u) =
      (interval (A / u) (B / u) (Q * v)).image (fun t => u * t) := by
  classical
  ext d
  constructor
  · intro hd
    have hgd := (Finset.mem_filter.mp hd).2
    have hud : u ∣ d := by
      rw [← hgd]
      exact Nat.gcd_dvd_right _ _
    obtain ⟨t, rfl⟩ := hud
    exact Finset.mem_image.mpr
      ⟨t, (mul_mem_interval_filter_gcd_iff hu huQ).mp hd, rfl⟩
  · intro hd
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
    exact (mul_mem_interval_filter_gcd_iff hu huQ).mpr ht

theorem sum_filter_gcd_eq {A B Q u v : ℕ}
    (hu : 0 < u) (huQ : Nat.Coprime u Q) (F : ℕ → ℝ) :
    (∑ d ∈ (interval A B Q).filter (fun d => Nat.gcd (u * v) d = u), F d) =
      ∑ t ∈ interval (A / u) (B / u) (Q * v), F (u * t) := by
  classical
  rw [filter_gcd_eq_image hu huQ, Finset.sum_image]
  intro a ha b hb hab
  exact Nat.eq_of_mul_eq_mul_left hu hab

end Erdos387Proof.GcdFactorReindex
