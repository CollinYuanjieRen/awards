import Proof.Main

/-!
# Erdős problem #1030 — the off-diagonal gap `r(k+1, k) − r(k, k)`

Erdős problem #1030 asks whether `r(k+1, k) / r(k, k) > 1 + c` for some `c > 0` and all large
`k`; this is open.  The problem page records two lower bounds for the *difference*:

* the trivial bound `r(k+1, k) − r(k, k) ≥ k − 2`;
* the Burr–Erdős–Faudree–Schelp bound `r(k+1, k) − r(k, k) ≥ 2k − 5`.

Both are proved here, as `Erdos1030.offdiag_sub_ge_trivial` and `Erdos1030.offdiag_sub_ge`,
from the sharp form `Erdos1030.offdiag_ge`, which is Theorem 1 of Burr–Erdős–Faudree–Schelp
(1989) with the two arguments exchanged — already available in this package as
`Erdos1030.ramsey_succ_left`.

Not claimed here: the question of Erdős problem #1030 itself (whether lim R(k+1,k)/R(k,k) > 1 + c
for some c > 0), which is open.
-/

namespace Erdos1030

/-- The sharp form: `r(k+1, k) ≥ r(k, k) + 2k − 3` for `k ≥ 2` (Theorem 1 of BEFS89 with the
arguments exchanged). -/
theorem offdiag_ge (k : ℕ) (hk : 2 ≤ k) : R k + (2 * k - 3) ≤ ramsey (k + 1) k := by
  unfold R
  exact ramsey_succ_left k k hk hk

/-- The bound stated on the problem page, for every `k`: `R(k+1, k) − R(k, k) ≥ 2k − 5`. -/
theorem offdiag_sub_ge (k : ℕ) : (ramsey (k + 1) k : ℤ) - (R k : ℤ) ≥ 2 * (k : ℤ) - 5 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · have h0 : R 0 = 0 := R_zero
      omega
    · have h1 : R 1 = 1 := R_one
      omega
  · have h := offdiag_ge k hk
    omega

/-- The trivial bound stated on the problem page, for every `k`: `R(k+1, k) − R(k, k) ≥ k − 2`. -/
theorem offdiag_sub_ge_trivial (k : ℕ) : (ramsey (k + 1) k : ℤ) - (R k : ℤ) ≥ (k : ℤ) - 2 := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k
    · have h0 : R 0 = 0 := R_zero
      omega
    · have h1 : R 1 = 1 := R_one
      omega
    · have h2 : R 2 = 2 := ramsey_two_right 2 (by omega)
      have h3 : ramsey (2 + 1) 2 = 3 := ramsey_two_right 3 (by omega)
      omega
  · have h := offdiag_sub_ge k
    omega

end Erdos1030
