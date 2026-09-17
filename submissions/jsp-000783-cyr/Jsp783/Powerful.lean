import Mathlib

namespace PowerfulSquares

/-- `n` is powerful: every prime factor divides it to exponent >= 2. -/
def Powerful (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, 2 ≤ n.factorization p

theorem powerful_27 : Powerful 27 := by
  have h3 : Nat.Prime 3 := by norm_num
  have hpf : (27 : ℕ).primeFactors = {3} := by
    rw [show (27 : ℕ) = 3 ^ 3 from rfl]
    exact Nat.primeFactors_prime_pow (by norm_num) h3
  have hfac : (27 : ℕ).factorization 3 = 3 := by
    rw [show (27 : ℕ) = 3 ^ 3 from rfl, Nat.Prime.factorization_pow h3]
    simp
  intro p hp
  rw [hpf, Finset.mem_singleton] at hp
  subst hp
  rw [hfac]
  norm_num

theorem powerful_32 : Powerful 32 := by
  have h2 : Nat.Prime 2 := by norm_num
  have hpf : (32 : ℕ).primeFactors = {2} := by
    rw [show (32 : ℕ) = 2 ^ 5 from rfl]
    exact Nat.primeFactors_prime_pow (by norm_num) h2
  have hfac : (32 : ℕ).factorization 2 = 5 := by
    rw [show (32 : ℕ) = 2 ^ 5 from rfl, Nat.Prime.factorization_pow h2]
    simp
  intro p hp
  rw [hpf, Finset.mem_singleton] at hp
  subst hp
  rw [hfac]
  norm_num

theorem powerful_pair_between_squares :
    Powerful 27 ∧ Powerful 32 ∧ 5 ^ 2 < 27 ∧ 27 < 32 ∧ 32 < 6 ^ 2 :=
  ⟨powerful_27, powerful_32, by norm_num, by norm_num, by norm_num⟩

#print axioms PowerfulSquares.powerful_27
#print axioms PowerfulSquares.powerful_32
#print axioms PowerfulSquares.powerful_pair_between_squares

end PowerfulSquares
