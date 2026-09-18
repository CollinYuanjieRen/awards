import Jsp825.Defs

/-!
# The construction: shared parameters

Blocks `j = 1, 2, 3, …` in dyadic groups `i = Nat.log 2 j`; block `j` has length `L j = (i+1) 2^i` and
consists of the integers `2^(m j) * s`, `1 ≤ s ≤ L j`; `m (j+1) = m j + r j` with `2^(r j) ≥ 16 L j`.
The digit event `E j` fixes the `r j` binary digits of `α` after position `m j`.
-/

open MeasureTheory Filter Set

namespace Erdos992

/-- Group index of block `j`: `2^(grp j) ≤ j < 2^(grp j + 1)` for `j ≥ 1`. -/
def grp (j : ℕ) : ℕ := Nat.log 2 j

/-- Length of block `j`. -/
def L (j : ℕ) : ℕ := (grp j + 1) * 2 ^ grp j

/-- Number of binary digits reserved for block `j` (`16 L j < 2^(r j)`; see `sixteen_L_lt`). -/
def r (j : ℕ) : ℕ := Nat.log 2 (L j) + 5

/-- Scale exponent of block `j` (`m 0 = 0`, `m (j+1) = m j + r j`). Block `0` is unused. -/
def m : ℕ → ℕ
  | 0 => 0
  | j + 1 => m j + r j

/-- Number of terms in blocks `1..j` (`N 0 = 0`). -/
def N : ℕ → ℕ
  | 0 => 0
  | j + 1 => N j + L (j + 1)

theorem L_pos (j : ℕ) : 0 < L j := by
  unfold L; positivity

theorem N_succ (j : ℕ) : N (j + 1) = N j + L (j + 1) := rfl

theorem le_N (j : ℕ) : j ≤ N j := by
  induction j with
  | zero => simp [N]
  | succ k ih => have := L_pos (k + 1); rw [N_succ]; omega

theorem exists_lt_N (n : ℕ) : ∃ j, n < N j := ⟨n + 1, by have := le_N (n + 1); omega⟩

/-- The block containing position `n`: the least `j` with `n < N j` (always `≥ 1`). -/
noncomputable def blockOf (n : ℕ) : ℕ := Nat.find (exists_lt_N n)

/-- The sequence: position `n` lies in block `j = blockOf n` at offset `t = n - N (j-1)`, and
`x n = 2^(m j) * (t + 1)`. -/
noncomputable def x (n : ℕ) : ℤ := 2 ^ m (blockOf n) * (((n - N (blockOf n - 1) : ℕ) : ℤ) + 1)

/-- The admissible digit patterns of block `j`: `g < 2^(r j)` with
`[g / 2^(r j), (g+1) / 2^(r j)) ⊆ [3 / (8 L j), 5 / (8 L j)]`. -/
def G (j : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ r j)).filter fun g ↦
    3 * 2 ^ r j ≤ 8 * L j * g ∧ 8 * L j * (g + 1) ≤ 5 * 2 ^ r j

/-- The digit event of block `j`: `α ∈ [0,1)` whose `r j` binary digits after position `m j`
form a pattern in `G j`. -/
def E (j : ℕ) : Set ℝ := {α | α ∈ Ico (0 : ℝ) 1 ∧ ⌊(2 : ℝ) ^ (m j + r j) * α⌋₊ % 2 ^ r j ∈ G j}

/-- The probability of `E j`. -/
noncomputable def p (j : ℕ) : ℝ := ((G j).card : ℝ) / 2 ^ r j

/-- The witness interval `[0, 1/2)`. -/
def I₀ : Set ℝ := Ico 0 (1 / 2)

end Erdos992
