/-
JSP-000232 / Erdős #271 — the Odlyzko–Stanley description of the Stanley sequence `A(1)`.

Combining the greedy specification of `Jsp232.Defs` with the base-3 combinatorics of
`Jsp232.Ternary`, we identify `A(1)` with `binToTer`, i.e. `a k` is the binary expansion of `k`
read in base 3.  Consequently the range of `A(1)` is exactly the set of naturals whose base-3
expansion avoids the digit `2`, and `3 ^ ⌊log₂ k⌋ ≤ a k < 3 ^ (⌊log₂ k⌋ + 1)` for `k ≥ 1`.
-/
import Jsp232.Defs
import Jsp232.Ternary

namespace Erdos271

/-! ### AP-freeness of sets of digit-`2`-free numbers -/

/-- A set all of whose members avoid the digit `2` in base 3 has no three-term AP. -/
private theorem not_hasThreeAP_of_noTwo {S : Set ℕ} (hS : ∀ x ∈ S, NoTwo x) :
    ¬ HasThreeAP S := by
  rintro ⟨a, b, c, ha, hb, hc, hab, hbc, habc⟩
  have := NoTwo.eq_of_add_eq_two_mul (hS a ha) (hS b hb) (hS c hc) habc
  omega

/-! ### `A(1) = binToTer` -/

/-- The greedy characterisation of `binToTer (j + 2)` over the prefix `binToTer '' Iic (j + 1)`. -/
private theorem isLeast_binToTer (j : ℕ) :
    IsLeast {m : ℕ | binToTer (j + 1) < m ∧
      ¬ HasThreeAP (insert m (binToTer '' Set.Iic (j + 1)))} (binToTer (j + 2)) := by
  constructor
  · refine ⟨binToTer_strictMono (by omega), not_hasThreeAP_of_noTwo ?_⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_image, Set.mem_Iic] at hx
    rcases hx with rfl | ⟨i, -, rfl⟩ <;> exact noTwo_binToTer _
  · rintro m ⟨hm1, hm2⟩
    by_contra hcon
    have hlt : m < binToTer (j + 2) := by omega
    by_cases hnt : NoTwo m
    · obtain ⟨i, hi⟩ := exists_binToTer_eq hnt
      have h1 : j + 1 < i := binToTer_strictMono.lt_iff_lt.1 (by rw [hi]; exact hm1)
      have h2 : i < j + 2 := binToTer_strictMono.lt_iff_lt.1 (by rw [hi]; exact hlt)
      omega
    · obtain ⟨i₁, hi₁⟩ := exists_binToTer_eq (noTwo_dropTwo m)
      obtain ⟨i₂, hi₂⟩ := exists_binToTer_eq (noTwo_lowerTwo m)
      have hdl : dropTwo m < lowerTwo m := dropTwo_lt_lowerTwo hnt
      have hlm : lowerTwo m < m := lowerTwo_lt hnt
      have h1 : i₁ < j + 2 := binToTer_strictMono.lt_iff_lt.1 (by rw [hi₁]; omega)
      have h2 : i₂ < j + 2 := binToTer_strictMono.lt_iff_lt.1 (by rw [hi₂]; omega)
      refine hm2 ⟨dropTwo m, lowerTwo m, m, ?_, ?_, Set.mem_insert _ _, hdl, hlm,
        dropTwo_add_self m⟩
      · exact Set.mem_insert_of_mem _ ⟨i₁, Set.mem_Iic.2 (by omega), hi₁⟩
      · exact Set.mem_insert_of_mem _ ⟨i₂, Set.mem_Iic.2 (by omega), hi₂⟩

/-- The Stanley sequence `A(1)` is the binary expansion of the index read in base 3. -/
theorem stanley_one_eq (k : ℕ) : stanley 1 k = binToTer k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => rw [stanley_zero, binToTer_zero]
    | 1 => rw [stanley_one, binToTer_one]
    | j + 2 =>
      have hprefix : stanley 1 '' Set.Iic (j + 1) = binToTer '' Set.Iic (j + 1) :=
        Set.image_congr fun i hi => ih i (by simp only [Set.mem_Iic] at hi; omega)
      have h1 : stanley 1 (j + 1) = binToTer (j + 1) := ih (j + 1) (by omega)
      have hL := isLeast_stanley_succ_succ 1 j
      rw [hprefix, h1] at hL
      exact IsLeast.unique hL (isLeast_binToTer j)

theorem stanley_one_eq_ofDigits (k : ℕ) : stanley 1 k = Nat.ofDigits 3 (Nat.digits 2 k) := by
  rw [stanley_one_eq, binToTer_eq_ofDigits]

private theorem stanley_one_eq_fun : stanley 1 = binToTer := funext stanley_one_eq

theorem stanley_one_strictMono : StrictMono (stanley 1) := by
  rw [stanley_one_eq_fun]
  exact binToTer_strictMono

theorem mem_range_stanley_one_iff (m : ℕ) : (∃ k, stanley 1 k = m) ↔ 2 ∉ Nat.digits 3 m := by
  constructor
  · rintro ⟨k, rfl⟩
    rw [stanley_one_eq]
    exact noTwo_binToTer k
  · intro hm
    obtain ⟨k, hk⟩ := exists_binToTer_eq (hm : NoTwo m)
    exact ⟨k, by rw [stanley_one_eq]; exact hk⟩

theorem range_stanley_one : Set.range (stanley 1) = {m : ℕ | 2 ∉ Nat.digits 3 m} := by
  ext m
  simp only [Set.mem_range]
  exact mem_range_stanley_one_iff m

theorem stanley_one_bounds {k : ℕ} (hk : 0 < k) :
    3 ^ Nat.log 2 k ≤ stanley 1 k ∧ stanley 1 k < 3 ^ (Nat.log 2 k + 1) := by
  rw [stanley_one_eq]
  exact binToTer_bounds hk

/-! ### Characterisation of the Stanley sequence by its defining property -/

/-- `IsStanleySeq n a`: `a` is the Stanley sequence `A(n)`: `a 0 = 0`, `a 1 = n`, and `a (k+2)` is the
least integer `> a (k+1)` such that `{a 0, …, a (k+2)}` has no three-term arithmetic progression. -/
structure IsStanleySeq (n : ℕ) (a : ℕ → ℕ) : Prop where
  zero : a 0 = 0
  one : a 1 = n
  greedy : ∀ k, IsLeast {m : ℕ | a (k + 1) < m ∧ ¬ HasThreeAP (insert m (a '' Set.Iic (k + 1)))} (a (k + 2))

theorem isStanleySeq_stanley (n : ℕ) : IsStanleySeq n (stanley n) where
  zero := stanley_zero n
  one := stanley_one n
  greedy := isLeast_stanley_succ_succ n

theorem IsStanleySeq.eq {n : ℕ} {a : ℕ → ℕ} (ha : IsStanleySeq n a) : a = stanley n := by
  funext k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => rw [ha.zero, stanley_zero]
    | 1 => rw [ha.one, stanley_one]
    | j + 2 =>
      have hprefix : a '' Set.Iic (j + 1) = stanley n '' Set.Iic (j + 1) :=
        Set.image_congr fun i hi => ih i (by simp only [Set.mem_Iic] at hi; omega)
      have h1 : a (j + 1) = stanley n (j + 1) := ih (j + 1) (by omega)
      have hL := ha.greedy j
      rw [hprefix, h1] at hL
      exact IsLeast.unique hL (isLeast_stanley_succ_succ n j)

theorem isStanleySeq_iff {n : ℕ} {a : ℕ → ℕ} : IsStanleySeq n a ↔ a = stanley n :=
  ⟨IsStanleySeq.eq, fun h => h ▸ isStanleySeq_stanley n⟩

theorem IsStanleySeq.one_eq {a : ℕ → ℕ} (ha : IsStanleySeq 1 a) (k : ℕ) :
    a k = Nat.ofDigits 3 (Nat.digits 2 k) := by
  rw [ha.eq, stanley_one_eq_ofDigits]

theorem IsStanleySeq.range_one {a : ℕ → ℕ} (ha : IsStanleySeq 1 a) :
    Set.range a = {m : ℕ | 2 ∉ Nat.digits 3 m} := by
  rw [ha.eq, range_stanley_one]

end Erdos271

/-! ### Axiom audit -/

#print axioms Erdos271.stanley_one_eq
#print axioms Erdos271.stanley_one_eq_ofDigits
#print axioms Erdos271.stanley_one_strictMono
#print axioms Erdos271.mem_range_stanley_one_iff
#print axioms Erdos271.range_stanley_one
#print axioms Erdos271.stanley_one_bounds
#print axioms Erdos271.isStanleySeq_stanley
#print axioms Erdos271.IsStanleySeq.eq
#print axioms Erdos271.isStanleySeq_iff
#print axioms Erdos271.IsStanleySeq.one_eq
#print axioms Erdos271.IsStanleySeq.range_one
