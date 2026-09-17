import Mathlib
namespace SquarefreeSums

theorem sqfree_pp {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Squarefree (p * q) :=
  (Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr hpq)).mpr ⟨hp.squarefree, hq.squarefree⟩

theorem sf3 : Squarefree (3:ℕ) := (by norm_num : Nat.Prime 3).squarefree
theorem sf5 : Squarefree (5:ℕ) := (by norm_num : Nat.Prime 5).squarefree
theorem sf6 : Squarefree (6:ℕ) := by
  have : (6:ℕ) = 2 * 3 := by norm_num
  rw [this]; exact sqfree_pp (by norm_num) (by norm_num) (by norm_num)
theorem sf10 : Squarefree (10:ℕ) := by
  have : (10:ℕ) = 2 * 5 := by norm_num
  rw [this]; exact sqfree_pp (by norm_num) (by norm_num) (by norm_num)
theorem sf11 : Squarefree (11:ℕ) := (by norm_num : Nat.Prime 11).squarefree
theorem sf13 : Squarefree (13:ℕ) := (by norm_num : Nat.Prime 13).squarefree
theorem sf14 : Squarefree (14:ℕ) := by
  have : (14:ℕ) = 2 * 7 := by norm_num
  rw [this]; exact sqfree_pp (by norm_num) (by norm_num) (by norm_num)
theorem sf15 : Squarefree (15:ℕ) := by
  have : (15:ℕ) = 3 * 5 := by norm_num
  rw [this]; exact sqfree_pp (by norm_num) (by norm_num) (by norm_num)
theorem sf17 : Squarefree (17:ℕ) := (by norm_num : Nat.Prime 17).squarefree
theorem sf22 : Squarefree (22:ℕ) := by
  have : (22:ℕ) = 2 * 11 := by norm_num
  rw [this]; exact sqfree_pp (by norm_num) (by norm_num) (by norm_num)

def S : Finset ℕ := {1, 2, 4, 9, 13}

theorem S_pairwise_sum_squarefree :
    ∀ a ∈ S, ∀ b ∈ S, a < b → Squarefree (a + b) := by
  intro a ha b hb hab
  fin_cases ha <;> fin_cases hb <;> first
    | (exfalso; omega)
    | exact sf3 | exact sf5 | exact sf6 | exact sf10 | exact sf11
    | exact sf13 | exact sf14 | exact sf15 | exact sf17 | exact sf22

theorem exists_squarefree_sum_set :
    ∃ T : Finset ℕ, T.card = 5 ∧ ∀ a ∈ T, ∀ b ∈ T, a < b → Squarefree (a + b) :=
  ⟨S, by decide, S_pairwise_sum_squarefree⟩

#print axioms SquarefreeSums.S_pairwise_sum_squarefree
#print axioms SquarefreeSums.exists_squarefree_sum_set
end SquarefreeSums
