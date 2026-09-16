import JSP573

#print axioms FranklFuredi.shadow_card_add_level_card_le
#print axioms FranklFuredi.exists_ffPoly_expansion
#print axioms FranklFuredi.frankl_singhi
#print axioms FranklFuredi.shadow_card_mul_choose_ge
#print axioms FranklFuredi.level_inequality
#print axioms FranklFuredi.card_le_ffBound_add_middle
#print axioms FranklFuredi.card_le_ffBound_add_middle_sub
#print axioms FranklFuredi.level_card_le_choose_sub
#print axioms FranklFuredi.card_franklFurediOdd
#print axioms FranklFuredi.card_franklFurediEven
#print axioms FranklFuredi.eventually_mul_pow_lt_two_pow
#print axioms FranklFuredi.exists_upper_bound
#print axioms FranklFuredi.frankl_furedi
#print axioms FranklFuredi.erdos_703_exact
#print axioms Erdos703.T_zero
#print axioms Erdos703.franklFurediOdd_card_le_T
#print axioms Erdos703.franklFurediEven_card_le_T
#print axioms Erdos703.erdos_703

open Finset in
example (r : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      Erdos703.T n r = if r = 0 then 2 ^ (n - 1) else FranklFuredi.ffBound n r :=
  FranklFuredi.erdos_703_exact r

example (t : ℕ) (ht : 1 ≤ t) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Erdos703.T n t = FranklFuredi.ffBound n t :=
  FranklFuredi.frankl_furedi t ht
