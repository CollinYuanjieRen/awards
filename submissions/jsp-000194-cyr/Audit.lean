import Erdos210Ordinary

open Erdos210

#print axioms Erdos210.erdos_210_closed
#print axioms Erdos210.erdos_210
#print axioms Erdos210.erdos_210_bound
#print axioms Erdos210.le_f
#print axioms Erdos210.erdos_210_motzkin
#print axioms Erdos210.le_f_motzkin
#print axioms Erdos210.erdos_210_linear
#print axioms Erdos210.le_f_linear
#print axioms Erdos210.ncard_realized_le
#print axioms Erdos210.card_le_of_notCollinear
#print axioms Erdos210.ordinary_of_visible
#print axioms Erdos210.not_mem_W_of_conn_missing
#print axioms Erdos210.ncard_ordinaryLines
#print axioms Erdos210.notCollinear_iff
#print axioms Erdos210.exists_config

/-- Erdős Problem 210: `f(n) → ∞`, where `f n` is the least number of ordinary lines determined by
`n` points of the plane not all on a line. -/
example : Filter.Tendsto f Filter.atTop Filter.atTop := Erdos210.erdos_210

/-- The closed form: the explicit rate and the limit together. -/
example : (∀ n : ℕ, 3 ≤ n → n ≤ 2 * f n + 2 ^ f n) ∧ Filter.Tendsto f Filter.atTop Filter.atTop :=
  Erdos210.erdos_210_closed

/-- The explicit rate: a non-collinear finite set with `m` ordinary lines has at most `2m + 2^m`
points. -/
example (P : Finset (ℝ × ℝ)) (hP : ¬ Collinear ℝ (P : Set (ℝ × ℝ))) :
    P.card ≤ 2 * (ordinaryLines P).ncard + 2 ^ (ordinaryLines P).ncard :=
  Erdos210.erdos_210_bound P hP

/-- Hence `n ≤ 2 f(n) + 2^{f(n)}` for `n ≥ 3`. -/
example (n : ℕ) (hn : 3 ≤ n) : n ≤ 2 * f n + 2 ^ f n := Erdos210.le_f n hn

/-- Motzkin's bound: a non-collinear finite set with `m` ordinary lines has at most
`2m + 1 + m(m+1)/2` points, so `f(n) ≥ √(2n) − O(1)`. -/
example (P : Finset (ℝ × ℝ)) (hP : ¬ Collinear ℝ (P : Set (ℝ × ℝ))) :
    P.card ≤ 2 * (ordinaryLines P).ncard +
      (1 + (ordinaryLines P).ncard * ((ordinaryLines P).ncard + 1) / 2) :=
  Erdos210.erdos_210_motzkin P hP

example (n : ℕ) (hn : 3 ≤ n) : n ≤ 2 * f n + (1 + f n * (f n + 1) / 2) := Erdos210.le_f_motzkin n hn

/-- The linear bound: a non-collinear finite set with `m` ordinary lines has at most `8m` points, so
`f(n) ≥ n/8`. -/
example (P : Finset (ℝ × ℝ)) (hP : ¬ Collinear ℝ (P : Set (ℝ × ℝ))) :
    P.card ≤ 8 * (ordinaryLines P).ncard :=
  Erdos210.erdos_210_linear P hP

example (n : ℕ) (hn : 3 ≤ n) : n ≤ 8 * f n := Erdos210.le_f_linear n hn

/-- `f n` is attained: for `n ≥ 3` there are `n` points of the plane not all on a line. -/
example (n : ℕ) (hn : 3 ≤ n) : ∃ P : Finset (ℝ × ℝ), P.card = n ∧ ¬ Collinear ℝ (P : Set (ℝ × ℝ)) :=
  Erdos210.exists_config n hn

/-- The ordinary lines are genuine affine lines of the plane, and membership in `line[ℝ, a, b]` is
the vanishing of the determinant used internally. -/
example (a b z : ℝ × ℝ) (hab : a ≠ b) : z ∈ line[ℝ, a, b] ↔ OnLine a b z := Erdos210.mem_line_iff hab z

-- The definitions, printed in full.
#print Erdos210.D
#print Erdos210.OnLine
#print Erdos210.ordinaryLines
#print Erdos210.f
