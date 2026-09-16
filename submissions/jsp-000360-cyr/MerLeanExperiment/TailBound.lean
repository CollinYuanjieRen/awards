import MerLeanExperiment.External.Erdos441
import Mathlib.Tactic

namespace Erdos441

/-- The integer reciprocal quotients distinguish all members of an admissible set. -/
theorem lcm_quotient_injective (N : ℕ) (A : Finset ℕ) (hA : LcmBounded N A) :
    Set.InjOn (fun a => N / a) (A : Set ℕ) := by
  have hneq (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) :
      N / a ≠ N / b := by
    intro heq
    have ha0 : 0 < a := (Finset.mem_Icc.mp (hA.1 ha)).1
    have hb0 : 0 < b := lt_trans ha0 hab
    have hg : Nat.gcd a b ≤ b - a := Nat.le_of_dvd (Nat.sub_pos_of_lt hab)
      (Nat.dvd_sub (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_left a b))
    have hprod : a * b ≤ N * (b - a) := by
      calc
        a * b = Nat.gcd a b * Nat.lcm a b := (Nat.gcd_mul_lcm a b).symm
        _ ≤ (b - a) * N := Nat.mul_le_mul hg (hA.2 a ha b hb)
        _ = N * (b - a) := Nat.mul_comm _ _
    have hlow : (N / a) * b ≤ N := by
      rw [heq]
      exact Nat.div_mul_le_self N b
    have hhigh : N < a * (N / a + 1) := Nat.lt_mul_div_succ N ha0
    have hlow' := Nat.mul_le_mul_right a hlow
    have hhigh' := Nat.mul_lt_mul_of_pos_right hhigh hb0
    have hsub : b - a + a = b := Nat.sub_add_cancel (le_of_lt hab)
    nlinarith
  intro a ha b hb heq
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (hneq a b ha hb hab heq)
  · exact hab
  · exact False.elim (hneq b a hb ha hab heq.symm)

/-- A positive integral cutoff gives a finite reciprocal-quotient count. -/
theorem lcm_tail_nat_bound (N K : ℕ) (A : Finset ℕ) (hA : LcmBounded N A)
    (hK : 0 < K) : (A.filter fun a => K ≤ a).card ≤ N / K := by
  let B := A.filter fun a => K ≤ a
  have hinj : Set.InjOn (fun a => N / a) (B : Set ℕ) :=
    (lcm_quotient_injective N A hA).mono (Finset.filter_subset _ _)
  have hsub : B.image (fun a => N / a) ⊆ Finset.Icc 1 (N / K) := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    have haA := (Finset.mem_filter.mp ha).1
    have hKa := (Finset.mem_filter.mp ha).2
    have haN := (Finset.mem_Icc.mp (hA.1 haA)).2
    have ha0 : 0 < a := lt_of_lt_of_le hK hKa
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.div_pos haN ha0
    · exact Nat.div_le_div_left hKa hK
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hcard
  simpa using hcard

/-- A uniform tail bound, with no dyadic decomposition or rounding error. -/
theorem lcm_tail_bound (N : ℕ) (A : Finset ℕ) (hA : LcmBounded N A)
    (H : ℝ) (hH : 0 < H) :
    ((A.filter fun a : ℕ => H < (a : ℝ)).card : ℝ) ≤ (N : ℝ) / H := by
  let K := ⌊H⌋₊ + 1
  have hK : 0 < K := Nat.zero_lt_succ _
  have hHK : H < (K : ℝ) := by simpa [K] using Nat.lt_floor_add_one H
  have heq : (A.filter fun a : ℕ => H < (a : ℝ)) = A.filter fun a => K ≤ a := by
    ext a
    simp only [Finset.mem_filter, K, Nat.add_one_le_iff,
      Nat.floor_lt (le_of_lt hH)]
  rw [heq]
  have hcount := lcm_tail_nat_bound N K A hA hK
  have hdiv := Nat.div_mul_le_self N K
  have hcast : ((N / K : ℕ) : ℝ) * (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdiv
  have hc : ((A.filter fun a => K ≤ a).card : ℝ) ≤ ((N / K : ℕ) : ℝ) := by
    exact_mod_cast hcount
  apply (le_div_iff₀ hH).mpr
  have hc0 : (0 : ℝ) ≤ (A.filter fun a => K ≤ a).card := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hc hK0,
    mul_le_mul_of_nonneg_left (le_of_lt hHK) hc0]

end Erdos441

#print axioms Erdos441.lcm_tail_bound
