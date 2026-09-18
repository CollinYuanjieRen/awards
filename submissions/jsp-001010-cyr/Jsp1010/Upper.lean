import Jsp1010.Defs

/-!
# JSP-001010 / Erdős #1205 — the upper bound `F x ≤ log x + 2`

Double counting: `∑_{m ∈ [1,x]} coverCount a x m = ∑_{n ∈ [1,x]} #{m ∈ [1,x] : m ≡ a n (mod n)}`,
each inner term is at most `x / n + 1`, so `x · F x ≤ x · H_x + x`, i.e. `F x ≤ H_x + 1 ≤ log x + 2`.
-/

open Finset

namespace Erdos1205

/-! ### `Defs`-level facts about `F` -/

theorem coverCount_le (a : ℕ → ℕ) (x m : ℕ) : coverCount a x m ≤ x :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- The set whose supremum defines `F x`. -/
private def Fset (x : ℕ) : Set ℕ := {k : ℕ | ∃ a : ℕ → ℕ, ∀ m ∈ Icc 1 x, k ≤ coverCount a x m}

private theorem F_eq_sSup (x : ℕ) : F x = sSup (Fset x) := rfl

private theorem Fset_nonempty (x : ℕ) : (Fset x).Nonempty :=
  ⟨0, fun _ => 0, fun _ _ => Nat.zero_le _⟩

private theorem Fset_bddAbove {x : ℕ} (hx : 1 ≤ x) : BddAbove (Fset x) := by
  refine ⟨x, ?_⟩
  rintro k ⟨a, ha⟩
  exact (ha 1 (mem_Icc.mpr ⟨le_rfl, hx⟩)).trans (coverCount_le a x 1)

/-- The defining set of `F x` is bounded by `x`, so any uniform lower bound `k` is `≤ F x`.
(The hypothesis `1 ≤ x` is needed: for `x = 0` the hypothesis is vacuous while `F 0 = 0`.) -/
theorem le_F_of_forall {x k : ℕ} (hx : 1 ≤ x) (a : ℕ → ℕ)
    (h : ∀ m ∈ Icc 1 x, k ≤ coverCount a x m) : k ≤ F x :=
  le_csSup (Fset_bddAbove hx) ⟨a, h⟩

theorem F_le_x (x : ℕ) : F x ≤ x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · have hnb : ¬ BddAbove (Fset 0) := by
      rintro ⟨n, hn⟩
      have hmem : n + 1 ∈ Fset 0 := ⟨fun _ => 0, by simp⟩
      exact absurd (hn hmem) (by omega)
    simp [F_eq_sSup, Nat.sSup_of_not_bddAbove hnb]
  · refine csSup_le (Fset_nonempty x) ?_
    rintro k ⟨a, ha⟩
    exact (ha 1 (mem_Icc.mpr ⟨le_rfl, hx⟩)).trans (coverCount_le a x 1)

/-- `F x` is attained by some choice of classes. -/
theorem exists_forall_F_le (x : ℕ) : ∃ a : ℕ → ℕ, ∀ m ∈ Icc 1 x, F x ≤ coverCount a x m := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · exact ⟨fun _ => 0, by simp⟩
  · exact Nat.sSup_mem (Fset_nonempty x) (Fset_bddAbove hx)

/-! ### Double counting -/

/-- Double counting: the total coverage is the sum over moduli of the class sizes. -/
theorem sum_coverCount (a : ℕ → ℕ) (x : ℕ) :
    ∑ m ∈ Icc 1 x, coverCount a x m
      = ∑ n ∈ Icc 1 x, ((Icc 1 x).filter fun m => m % n = a n % n).card := by
  simp only [coverCount, Finset.card_filter]
  exact Finset.sum_comm

/-- A residue class mod `n ≥ 1` has at most `x / n + 1` elements in `[1, x]`. -/
theorem card_residueClass_le {n : ℕ} (hn : 1 ≤ n) (x r : ℕ) :
    ((Icc 1 x).filter fun m => m % n = r).card ≤ x / n + 1 := by
  -- (the bound in fact also holds for `n = 0`, where both sides count at most one element)
  have _hn : 1 ≤ n := hn
  have hcard : (range (x / n + 1)).card = x / n + 1 := by simp
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun m => m / n) ?_ ?_
  · intro m hm
    simp only [mem_coe, mem_filter, mem_Icc] at hm
    have : m / n ∈ range (x / n + 1) :=
      mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hm.1.2))
    exact_mod_cast this
  · intro m₁ hm₁ m₂ hm₂ hdiv
    simp only [mem_coe, mem_filter, mem_Icc] at hm₁ hm₂
    have hdiv' : m₁ / n = m₂ / n := hdiv
    have e₁ := Nat.div_add_mod m₁ n
    have e₂ := Nat.div_add_mod m₂ n
    rw [hm₁.2] at e₁
    rw [hm₂.2] at e₂
    rw [← e₁, ← e₂, hdiv']

/-! ### The upper bound -/

private theorem harmonic_cast (x : ℕ) : ((harmonic x : ℚ) : ℝ) = ∑ n ∈ Icc 1 x, (n : ℝ)⁻¹ := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  ring

theorem F_le_harmonic_add_one (x : ℕ) (hx : 1 ≤ x) : (F x : ℝ) ≤ (harmonic x : ℝ) + 1 := by
  obtain ⟨a, ha⟩ := exists_forall_F_le x
  have hcard : (Icc 1 x).card = x := by simp
  -- `x * F x ≤ ∑_{m} coverCount a x m`
  have h1 : x * F x ≤ ∑ m ∈ Icc 1 x, coverCount a x m := by
    have := Finset.card_nsmul_le_sum (Icc 1 x) (fun m => coverCount a x m) (F x) ha
    simpa [hcard, smul_eq_mul] using this
  -- `∑_{m} coverCount a x m ≤ ∑_{n} (x / n + 1)`
  have h2 : ∑ m ∈ Icc 1 x, coverCount a x m ≤ ∑ n ∈ Icc 1 x, (x / n + 1) := by
    rw [sum_coverCount]
    refine Finset.sum_le_sum ?_
    intro n hn
    exact card_residueClass_le (mem_Icc.mp hn).1 x (a n % n)
  have h3 : x * F x ≤ ∑ n ∈ Icc 1 x, (x / n + 1) := h1.trans h2
  -- cast to `ℝ`
  have h4 : ((∑ n ∈ Icc 1 x, (x / n + 1) : ℕ) : ℝ) ≤ ∑ n ∈ Icc 1 x, ((x : ℝ) / n + 1) := by
    push_cast
    gcongr with n hn
    exact Nat.cast_div_le
  have h5 : ∑ n ∈ Icc 1 x, ((x : ℝ) / n + 1) = x * ((harmonic x : ℚ) : ℝ) + x := by
    rw [Finset.sum_add_distrib, harmonic_cast, Finset.mul_sum]
    simp [hcard, div_eq_mul_inv]
  have h6 : (x : ℝ) * F x ≤ x * ((harmonic x : ℚ) : ℝ) + x := by
    calc (x : ℝ) * F x = ((x * F x : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((∑ n ∈ Icc 1 x, (x / n + 1) : ℕ) : ℝ) := by exact_mod_cast h3
      _ ≤ ∑ n ∈ Icc 1 x, ((x : ℝ) / n + 1) := h4
      _ = x * ((harmonic x : ℚ) : ℝ) + x := h5
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have : (x : ℝ) * F x ≤ x * (((harmonic x : ℚ) : ℝ) + 1) := by linarith
  exact le_of_mul_le_mul_left this hxpos

theorem F_le_log_add_two (x : ℕ) (hx : 1 ≤ x) : (F x : ℝ) ≤ Real.log x + 2 := by
  have h := F_le_harmonic_add_one x hx
  have h2 : ((harmonic x : ℚ) : ℝ) ≤ 1 + Real.log x := harmonic_le_one_add_log x
  linarith

end Erdos1205

