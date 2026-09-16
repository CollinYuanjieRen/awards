import JSP620.Target

#print axioms Erdos754Lower.half_le_f
#print axioms Erdos754Lower.half_add_two_le_f_of_eight_dvd
#print axioms Erdos754Lower.erdos_754_two_sided
#print axioms Erdos754Lower.abs_f_sub_half_le
#print axioms Erdos754Lower.f_sub_half_isBigO
#print axioms Erdos754.erdos_754

example : (∀ n : ℕ, n / 2 ≤ Erdos754.f n) ∧
    (∀ n : ℕ, n ≠ 0 → 8 ∣ n → n / 2 + 2 ≤ Erdos754.f n) ∧
    (∃ C : ℝ, ∀ n : ℕ, (Erdos754.f n : ℝ) ≤ (n : ℝ) / 2 + C) :=
  Erdos754Lower.erdos_754_two_sided
