import Erdos210Ordinary.Count
import Erdos210Ordinary.Count2
import Erdos210Ordinary.Bridge
import Erdos210Ordinary.Witness

/-!
# Erdős Problem 210 — the bound and `f n → ∞`

`erdos_210_bound` is the explicit rate: `n` non-collinear points in the plane determine `m`
ordinary lines with `n ≤ 2 m + 2 ^ m` (`card_le_of_notCollinear` transported along
`ncard_ordinaryLines` and `notCollinear_iff`).

Since `f n` is attained for `n ≥ 3` (`f_mem`), the same inequality holds for `f n` itself
(`le_f`), and as `m ↦ 2 m + 2 ^ m` is finite for each `m`, the bound `f n < m` becomes impossible
once `n` exceeds `2 m + 2 ^ m`; hence `f` tends to infinity.
-/

namespace Erdos210

theorem erdos_210_bound (P : Finset (ℝ × ℝ)) (hP : ¬ Collinear ℝ (P : Set (ℝ × ℝ))) :
    P.card ≤ 2 * (ordinaryLines P).ncard + 2 ^ (ordinaryLines P).ncard := by
  rw [ncard_ordinaryLines]
  exact card_le_of_notCollinear ((notCollinear_iff P).2 hP)

theorem le_f (n : ℕ) (hn : 3 ≤ n) : n ≤ 2 * f n + 2 ^ f n := by
  obtain ⟨P, hcard, hP, hf⟩ := f_mem n hn
  have hbound := erdos_210_bound P hP
  rwa [hcard, hf] at hbound

theorem erdos_210 : Filter.Tendsto f Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun m => ⟨2 * m + 2 ^ m + 3, fun n hn => ?_⟩
  by_contra hcon
  have hlt : f n < m := not_le.1 hcon
  have h3n : 3 ≤ n := le_trans (Nat.le_add_left 3 (2 * m + 2 ^ m)) hn
  have h1 : n ≤ 2 * f n + 2 ^ f n := le_f n h3n
  have h2 : (2 : ℕ) ^ f n ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hlt.le
  have h4 : 2 * f n + 2 ^ f n ≤ 2 * m + 2 ^ m :=
    Nat.add_le_add (Nat.mul_le_mul_left 2 hlt.le) h2
  have hfin : 2 * m + 2 ^ m + 3 ≤ 2 * m + 2 ^ m := le_trans hn (le_trans h1 h4)
  exact absurd hfin (not_le.2 (Nat.lt_add_of_pos_right (by norm_num)))

/-- **Erdős Problem 210, closed form.** Both halves of the answer in one proposition: the explicit
rate `n ≤ 2 f(n) + 2^{f(n)}` for every `n ≥ 3`, and `f(n) → ∞`. -/
theorem erdos_210_closed :
    (∀ n : ℕ, 3 ≤ n → n ≤ 2 * f n + 2 ^ f n) ∧ Filter.Tendsto f Filter.atTop Filter.atTop :=
  ⟨fun n hn => le_f n hn, erdos_210⟩

/-- **Motzkin's bound.** The `2 ^ m` of `erdos_210_bound` replaced by the number of cells of an
arrangement of `m` lines, `1 + m (m + 1) / 2`. -/
theorem erdos_210_motzkin (P : Finset (ℝ × ℝ)) (hP : ¬ Collinear ℝ (P : Set (ℝ × ℝ))) :
    P.card ≤ 2 * (ordinaryLines P).ncard +
      (1 + (ordinaryLines P).ncard * ((ordinaryLines P).ncard + 1) / 2) := by
  rw [ncard_ordinaryLines]
  exact card_le_of_notCollinear_motzkin ((notCollinear_iff P).2 hP)

theorem le_f_motzkin (n : ℕ) (hn : 3 ≤ n) : n ≤ 2 * f n + (1 + f n * (f n + 1) / 2) := by
  obtain ⟨P, hcard, hP, hf⟩ := f_mem n hn
  have hbound := erdos_210_motzkin P hP
  rwa [hcard, hf] at hbound

end Erdos210
