import Mathlib

/-!
# Erdős Problem #407: the four-representation identities

Newman's conjecture (Erdős #407): the number `w(n)` of solutions of `n = 2^a + 3^b + 2^c 3^d`
(`a, b, c, d ≥ 0`) is bounded — PROVED by Evertse–Győry–Stewart–Tijdeman, with effective bounds by
Bajpai–Bennett (`w(n) ≤ 4` for `n ≥ 131082` in the distinct-set convention); none of this is
formalized here.  The problem page records: "There are infinitely many `n` with `w(n) = 4`, given by
the identities `2^{a−1} + 3^b + 2^{a−1}·3^0 = 2^{a−2} + 3^b + 2^{a−2}·3^1 = 2^a + 3^{b−1} + 2·3^{b−1} =
2^a + 3^{b−2} + 2^3·3^{b−2}`."  This file verifies the identities and the lower bound they give:
for `a ≥ 3`, `b ≥ 2`, the four exponent quadruples `(a−1, b, a−1, 0)`, `(a−2, b, a−2, 1)`,
`(a, b−1, 1, b−1)`, `(a, b−2, 3, b−2)` are pairwise distinct solutions for
`n = 2^{a−1} + 3^b + 2^{a−1}`, so `w(n) ≥ 4` for infinitely many `n`.  The matching upper bound
`w(n) ≤ 4` (so that `w(n) = 4` exactly) is Bajpai–Bennett's theorem and is NOT claimed.

`Rep`, `Rep.value`, `solutions` and `w` are copied verbatim from the plby/lean-proofs comparator
statement of the problem (`w` counts ordered exponent quadruples, the literal convention of the
problem statement; the page's `w(n) = 4` is in the distinct-set convention of Tijdeman–Wang, under
which the same four solutions are also distinct).
-/

namespace Erdos407

structure Rep where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ

def Rep.value (r : Rep) : ℕ :=
  2 ^ r.a + 3 ^ r.b + 2 ^ r.c * 3 ^ r.d

def solutions (n : ℕ) : Set Rep := {r | r.value = n}

noncomputable def w (n : ℕ) : ℕ := (solutions n).ncard

/-- The value shared by the four representations. -/
def N (a b : ℕ) : ℕ := 2 ^ (a - 1) + 3 ^ b + 2 ^ (a - 1)

/-- The page's four identities: for `a ≥ 3`, `b ≥ 2`, the four quadruples all represent
`N a b`. -/
theorem four_identities (a b : ℕ) (ha : 3 ≤ a) (hb : 2 ≤ b) :
    (Rep.mk (a - 1) b (a - 1) 0).value = N a b ∧ (Rep.mk (a - 2) b (a - 2) 1).value = N a b ∧
      (Rep.mk a (b - 1) 1 (b - 1)).value = N a b ∧ (Rep.mk a (b - 2) 3 (b - 2)).value = N a b := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
  simp only [Rep.value, N]
  rw [show a' + 3 - 1 = a' + 2 by omega, show a' + 3 - 2 = a' + 1 by omega,
    show b' + 2 - 1 = b' + 1 by omega, show b' + 2 - 2 = b' by omega]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- The solution set of any `n` is finite: every exponent `e` occurring in a representation of `n`
satisfies `e < 2 ^ e ≤ n`, so `solutions n` embeds into a finite box of quadruples. -/
theorem solutions_finite (n : ℕ) : (solutions n).Finite := by
  refine Set.Finite.subset (((Set.finite_Iio n).prod ((Set.finite_Iio n).prod
    ((Set.finite_Iio n).prod (Set.finite_Iio n)))).image
      (fun p : ℕ × ℕ × ℕ × ℕ => Rep.mk p.1 p.2.1 p.2.2.1 p.2.2.2)) ?_
  rintro ⟨x, y, z, t⟩ hr
  have hv : 2 ^ x + 3 ^ y + 2 ^ z * 3 ^ t = n := hr
  have h2x : 2 ^ x ≤ n := by
    rw [← hv]; exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have h3y : 3 ^ y ≤ n := by
    rw [← hv]; exact le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
  have hzt : 2 ^ z * 3 ^ t ≤ n := by rw [← hv]; exact Nat.le_add_left _ _
  refine ⟨(x, y, z, t), ?_, rfl⟩
  simp only [Set.mem_prod, Set.mem_Iio]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le Nat.lt_two_pow_self h2x
  · exact lt_of_lt_of_le Nat.lt_two_pow_self
      (le_trans (Nat.pow_le_pow_left (by norm_num) y) h3y)
  · exact lt_of_lt_of_le Nat.lt_two_pow_self
      (le_trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by norm_num))) hzt)
  · exact lt_of_lt_of_le Nat.lt_two_pow_self
      (le_trans (Nat.pow_le_pow_left (by norm_num) t)
        (le_trans (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by norm_num))) hzt))

/-- The four quadruples are pairwise distinct, so `w (N a b) ≥ 4`. -/
theorem four_le_w (a b : ℕ) (ha : 3 ≤ a) (hb : 2 ≤ b) : 4 ≤ w (N a b) := by
  obtain ⟨h1, h2, h3, h4⟩ := four_identities a b ha hb
  have hsub : ({Rep.mk (a - 1) b (a - 1) 0, Rep.mk (a - 2) b (a - 2) 1,
      Rep.mk a (b - 1) 1 (b - 1), Rep.mk a (b - 2) 3 (b - 2)} : Set Rep) ⊆ solutions (N a b) := by
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4]
  have hn1 : Rep.mk (a - 1) b (a - 1) 0 ∉ ({Rep.mk (a - 2) b (a - 2) 1,
      Rep.mk a (b - 1) 1 (b - 1), Rep.mk a (b - 2) 3 (b - 2)} : Set Rep) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Rep.mk.injEq, not_or]
    omega
  have hn2 : Rep.mk (a - 2) b (a - 2) 1 ∉ ({Rep.mk a (b - 1) 1 (b - 1),
      Rep.mk a (b - 2) 3 (b - 2)} : Set Rep) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Rep.mk.injEq, not_or]
    omega
  have hn3 : Rep.mk a (b - 1) 1 (b - 1) ∉ ({Rep.mk a (b - 2) 3 (b - 2)} : Set Rep) := by
    simp only [Set.mem_singleton_iff, Rep.mk.injEq, not_and]
    omega
  have hcard : ({Rep.mk (a - 1) b (a - 1) 0, Rep.mk (a - 2) b (a - 2) 1,
      Rep.mk a (b - 1) 1 (b - 1), Rep.mk a (b - 2) 3 (b - 2)} : Set Rep).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem hn1, Set.ncard_insert_of_notMem hn2,
      Set.ncard_insert_of_notMem hn3, Set.ncard_singleton]
  have hle := Set.ncard_le_ncard hsub (solutions_finite (N a b))
  rw [hcard] at hle
  exact hle

/-- **Infinitely many `n` have at least four representations.** -/
theorem erdos_407_infinite_four : {n : ℕ | 4 ≤ w n}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => N (k + 3) 2) ?_ ?_
  · intro x y hxy
    simp only [N] at hxy
    rw [show x + 3 - 1 = x + 2 by omega, show y + 3 - 1 = y + 2 by omega] at hxy
    have hp : (2 : ℕ) ^ (x + 2) = 2 ^ (y + 2) := by omega
    have := Nat.pow_right_injective (le_refl 2) hp
    omega
  · intro k
    show 4 ≤ w (N (k + 3) 2)
    exact four_le_w (k + 3) 2 (by omega) (by omega)

end Erdos407

open Erdos407 in
/-- **Erdős #407, the page's identities, closed form**: for all `a ≥ 3`, `b ≥ 2` the four
quadruples are solutions of the same `n` with `w(n) ≥ 4`, and the set of `n` with `w(n) ≥ 4` is
infinite. -/
theorem erdos_407_identities_closed :
    (∀ a b : ℕ, 3 ≤ a → 2 ≤ b →
      (Rep.mk (a - 1) b (a - 1) 0).value = N a b ∧ (Rep.mk (a - 2) b (a - 2) 1).value = N a b ∧
        (Rep.mk a (b - 1) 1 (b - 1)).value = N a b ∧ (Rep.mk a (b - 2) 3 (b - 2)).value = N a b ∧
        4 ≤ w (N a b)) ∧
      ¬ {n : ℕ | 4 ≤ w n}.Finite := by
  refine ⟨fun a b ha hb => ⟨(four_identities a b ha hb).1, (four_identities a b ha hb).2.1,
    (four_identities a b ha hb).2.2.1, (four_identities a b ha hb).2.2.2,
    four_le_w a b ha hb⟩, erdos_407_infinite_four⟩
