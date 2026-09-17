import Mathlib

namespace NoDivTwo

/-- The construction: integers in the interval (⌊n/3⌋, n]. -/
def A (n : ℕ) : Finset ℕ := Finset.Icc (n / 3 + 1) n

theorem A_card (n : ℕ) : (A n).card = n - n / 3 := by
  rw [A, Nat.card_Icc]
  omega

/-- No element of `A n` divides two DISTINCT other elements. -/
theorem A_no_two_multiples (n : ℕ) :
    ∀ a ∈ A n, ∀ b ∈ A n, ∀ c ∈ A n, b ≠ c → a ∣ b → a ∣ c → a = b ∨ a = c := by
  intro a ha b hb c hc hbc hab hac
  rw [A, Finset.mem_Icc] at ha hb hc
  obtain ⟨k, hk⟩ := hab
  obtain ⟨j, hj⟩ := hac
  have hmod : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hdiv : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
  -- From a ≥ n/3 + 1 we get 3*a > n.
  have h3a : n < 3 * a := by omega
  have ha_pos : 0 < a := by omega
  -- k < 3 since a*k = b ≤ n < 3*a.
  have hk3 : k < 3 := by
    apply Nat.lt_of_mul_lt_mul_left (a := a)
    calc a * k = b := hk.symm
      _ ≤ n := hb.2
      _ < 3 * a := h3a
      _ = a * 3 := by ring
  have hj3 : j < 3 := by
    apply Nat.lt_of_mul_lt_mul_left (a := a)
    calc a * j = c := hj.symm
      _ ≤ n := hc.2
      _ < 3 * a := h3a
      _ = a * 3 := by ring
  interval_cases k <;> interval_cases j <;> omega

/-- Lower bound on the extremal function via the construction. -/
theorem exists_large_no_div_two (n : ℕ) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 n ∧ B.card = n - n / 3 ∧
      (∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, b ≠ c → a ∣ b → a ∣ c → a = b ∨ a = c) := by
  refine ⟨A n, ?_, A_card n, A_no_two_multiples n⟩
  rw [A]
  exact Finset.Icc_subset_Icc_left (by omega)

#print axioms NoDivTwo.A_card
#print axioms NoDivTwo.A_no_two_multiples
#print axioms NoDivTwo.exists_large_no_div_two

end NoDivTwo
