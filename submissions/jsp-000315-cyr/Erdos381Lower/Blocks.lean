import Erdos381Lower.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fin.SuccPred

/-!
# Erdős #381, lower bound: the four prime blocks (§3.3)

Erdős surrounds the largest prime factor `p` of a highly composite `n`, and the largest prime
`q` with exponent `≥ 2`, by blocks of primes that are logarithmically close to `p` and to `q`.
Consecutiveness of those primes is never used — only pairwise distinctness, closeness in `log`,
and the exponents they carry in `n`.  This file therefore packages plby's

```
Erdos381.prime_blocks_log_error
    {L N₀ H a : ℕ} {x : ℝ} (hL : 0 < L)
    (hwindow : ∀ n : ℕ, N₀ ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ L < p ∧ p ≤ (n + 1) ^ L)
    (hrootLow : ((a : ℝ) ^ L) ≤ x) (hrootHigh : x < (((a + 1 : ℕ) : ℝ) ^ L))
    (ha : N₀ + H + 1 ≤ a) (hHa : 2 * H + 4 ≤ a) :
    ∃ up down : Fin H → ℕ, Function.Injective up ∧ Function.Injective down ∧
      (∀ i, (up i).Prime ∧ x < up i ∧
        |Real.log (up i) - Real.log x| ≤ (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a : ℝ)) ∧
      (∀ i, (down i).Prime ∧ (down i : ℝ) < x ∧
        |Real.log (down i) - Real.log x| ≤ (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a : ℝ))
```

into the record `PrimeBlocks H x ε` and supplies the three things the gap argument needs:

* `eventually_nonempty_primeBlocks` — the side conditions `N₀ + H + 1 ≤ a` and `2H + 4 ≤ a`
  (with `a = ⌊x ^ (1/L)⌋₊`) are discharged *eventually in `x`*, uniformly in every block size
  `H ≤ x ^ B + 2` with `B < 1/L`, and the resulting error is put in the clean asymptotic form
  `ε ≤ 8L · x ^ (B - 1/L)`.  Taking `B = 1/(8L)` at `x = p` gives `ε_p ≤ 8L · p ^ (-7/(8L))`.
  The threshold is never a numeral: `N₀` is opaque, so everything stays inside `Eventually`.
* `PrimeBlocks.restrict` / `PrimeBlocks.monoError` — shrinking a block from `Fin H` to `Fin s`
  (`s ≤ H`) and weakening the error bound.
* `FourBlocks` and `exists_fourBlocks` — the §3.3 table.  The exponent (`κ`) column is *not*
  proved here: the highly-composite input is taken as the hypotheses `hzero`, `hone`, `htwo`
  (supplied by `Structure.lean`), and this file only performs the location bookkeeping that
  turns them into exponents for the four families.
-/

namespace Erdos381Lower

open Filter

/-! ### Logarithmic closeness -/

/-- If `y` is within logarithmic distance `ε` of `x`, then `y ≤ x · exp ε`. -/
theorem le_mul_exp_of_abs_log_sub_le {x y ε : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : |Real.log y - Real.log x| ≤ ε) : y ≤ x * Real.exp ε := by
  have h1 : Real.log y ≤ Real.log x + ε := by
    have := (abs_le.1 h).2
    linarith
  have h2 : y ≤ Real.exp (Real.log x + ε) := (Real.log_le_iff_le_exp hy).1 h1
  rwa [Real.exp_add, Real.exp_log hx] at h2

/-- If `y` is within logarithmic distance `ε` of `x`, then `x / exp ε ≤ y`. -/
theorem div_exp_le_of_abs_log_sub_le {x y ε : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : |Real.log y - Real.log x| ≤ ε) : x / Real.exp ε ≤ y := by
  have h1 : Real.log x - ε ≤ Real.log y := by
    have := (abs_le.1 h).1
    linarith
  have h2 : Real.exp (Real.log x - ε) ≤ y := (Real.le_log_iff_exp_le hy).1 h1
  rwa [Real.exp_sub, Real.exp_log hx] at h2

/-! ### The block record -/

/-- `PrimeBlocks H x ε` packages two blocks of `H` pairwise distinct primes, one strictly
above the real number `x` and one strictly below it, each within logarithmic distance `ε`
of `x`.  This is exactly the payload of `Erdos381.prime_blocks_log_error`. -/
structure PrimeBlocks (H : ℕ) (x ε : ℝ) where
  /-- The block of primes lying above `x`. -/
  up : Fin H → ℕ
  /-- The block of primes lying below `x`. -/
  down : Fin H → ℕ
  /-- The upper block is pairwise distinct. -/
  up_injective : Function.Injective up
  /-- The lower block is pairwise distinct. -/
  down_injective : Function.Injective down
  /-- Every member of the upper block is prime. -/
  up_prime : ∀ i, (up i).Prime
  /-- Every member of the lower block is prime. -/
  down_prime : ∀ i, (down i).Prime
  /-- Every member of the upper block lies strictly above `x`. -/
  lt_up : ∀ i, x < (up i : ℝ)
  /-- Every member of the lower block lies strictly below `x`. -/
  down_lt : ∀ i, (down i : ℝ) < x
  /-- The upper block has logarithmic displacement at most `ε`. -/
  up_log_error : ∀ i, |Real.log (up i) - Real.log x| ≤ ε
  /-- The lower block has logarithmic displacement at most `ε`. -/
  down_log_error : ∀ i, |Real.log (down i) - Real.log x| ≤ ε

namespace PrimeBlocks

variable {H : ℕ} {x ε : ℝ}

/-- Restrict both blocks to their first `s` members (`s ≤ H`), keeping injectivity and all
bounds.  This is how the gap argument passes from the common size `H` to the Dirichlet data
`s` and `t`. -/
def restrict (B : PrimeBlocks H x ε) {s : ℕ} (hs : s ≤ H) : PrimeBlocks s x ε where
  up := fun i ↦ B.up (Fin.castLE hs i)
  down := fun i ↦ B.down (Fin.castLE hs i)
  up_injective := B.up_injective.comp (Fin.castLE_injective hs)
  down_injective := B.down_injective.comp (Fin.castLE_injective hs)
  up_prime := fun i ↦ B.up_prime (Fin.castLE hs i)
  down_prime := fun i ↦ B.down_prime (Fin.castLE hs i)
  lt_up := fun i ↦ B.lt_up (Fin.castLE hs i)
  down_lt := fun i ↦ B.down_lt (Fin.castLE hs i)
  up_log_error := fun i ↦ B.up_log_error (Fin.castLE hs i)
  down_log_error := fun i ↦ B.down_log_error (Fin.castLE hs i)

/-- Weaken the logarithmic error bound of a block. -/
def monoError (B : PrimeBlocks H x ε) {ε' : ℝ} (h : ε ≤ ε') : PrimeBlocks H x ε' where
  up := B.up
  down := B.down
  up_injective := B.up_injective
  down_injective := B.down_injective
  up_prime := B.up_prime
  down_prime := B.down_prime
  lt_up := B.lt_up
  down_lt := B.down_lt
  up_log_error := fun i ↦ (B.up_log_error i).trans h
  down_log_error := fun i ↦ (B.down_log_error i).trans h

/-- Members of the upper block are at most `x · exp ε`. -/
theorem up_le_mul_exp (B : PrimeBlocks H x ε) (hx : 0 < x) (i : Fin H) :
    (B.up i : ℝ) ≤ x * Real.exp ε :=
  le_mul_exp_of_abs_log_sub_le hx (hx.trans (B.lt_up i)) (B.up_log_error i)

/-- Members of the lower block are at least `x / exp ε`. -/
theorem div_exp_le_down (B : PrimeBlocks H x ε) (hx : 0 < x) (i : Fin H) :
    x / Real.exp ε ≤ (B.down i : ℝ) := by
  refine div_exp_le_of_abs_log_sub_le hx ?_ (B.down_log_error i)
  exact_mod_cast (B.down_prime i).pos

end PrimeBlocks

/-! ### Existence of blocks -/

/-- Direct wrapper of `Erdos381.prime_blocks_log_error` at the root index
`a = ⌊x ^ (1/L)⌋₊`, with the bracketing hypotheses supplied by
`Erdos381.floor_rpow_root_bracket`. -/
theorem nonempty_primeBlocks_of_root {L N₀ H : ℕ} (hL : 0 < L)
    (hwindow : ∀ n : ℕ, N₀ ≤ n → ∃ r : ℕ, r.Prime ∧ n ^ L < r ∧ r ≤ (n + 1) ^ L)
    {x : ℝ} (hx : 0 < x) (ha : N₀ + H + 1 ≤ ⌊x ^ (1 / (L : ℝ))⌋₊)
    (hHa : 2 * H + 4 ≤ ⌊x ^ (1 / (L : ℝ))⌋₊) :
    Nonempty (PrimeBlocks H x
      ((2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / ((⌊x ^ (1 / (L : ℝ))⌋₊ : ℕ) : ℝ))) := by
  have hbracket := Erdos381.floor_rpow_root_bracket hx hL
  obtain ⟨up, down, hupInj, hdownInj, hup, hdown⟩ :=
    Erdos381.prime_blocks_log_error hL hwindow hbracket.1 hbracket.2 ha hHa
  exact ⟨{
    up := up
    down := down
    up_injective := hupInj
    down_injective := hdownInj
    up_prime := fun i ↦ (hup i).1
    down_prime := fun i ↦ (hdown i).1
    lt_up := fun i ↦ (hup i).2.1
    down_lt := fun i ↦ (hdown i).2.1
    up_log_error := fun i ↦ (hup i).2.2
    down_log_error := fun i ↦ (hdown i).2.2 }⟩

/-- **The analytic input of §3.3, in asymptotic form.**  Fix the Hoheisel data `L`, `N₀` of
`Erdos381.exists_fixedPower_prime_windows` and an exponent `B` with `0 < B < 1/L`.  Then for
all large `x` and *every* block size `H ≤ x ^ B + 2` the side conditions `N₀ + H + 1 ≤ a` and
`2H + 4 ≤ a` of `Erdos381.prime_blocks_log_error` hold at `a = ⌊x ^ (1/L)⌋₊`, and the
resulting logarithmic error `2L(H+2)/a` is at most `8L · x ^ (B - 1/L)`.

Used twice: at `x = p` with `B = 1/(8L)` (error `8L · p ^ (-7/(8L))`) and at `x = q` with
`B = 1/(4L)` (legitimate because `q > √p`, so the `p`-sized `H` is still `≤ q ^ (1/(4L)) + 2`).
No numeral threshold ever appears, since `N₀` is opaque. -/
theorem eventually_nonempty_primeBlocks {L N₀ : ℕ} (hL : 0 < L)
    (hwindow : ∀ n : ℕ, N₀ ≤ n → ∃ r : ℕ, r.Prime ∧ n ^ L < r ∧ r ≤ (n + 1) ^ L)
    {B : ℝ} (hB : 0 < B) (hBL : B < 1 / (L : ℝ)) :
    ∀ᶠ x : ℝ in atTop, ∀ H : ℕ, (H : ℝ) ≤ x ^ B + 2 →
      Nonempty (PrimeBlocks H x (8 * L * x ^ (B - 1 / (L : ℝ)))) := by
  have hc : (0 : ℝ) < 1 / (L : ℝ) := hB.trans hBL
  have hBc : (0 : ℝ) < 1 / (L : ℝ) - B := by linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hBc).eventually_ge_atTop (4 : ℝ),
    (tendsto_rpow_atTop hc).eventually_ge_atTop (2 * ((N₀ : ℝ) + 10)),
    (tendsto_rpow_atTop hB).eventually_ge_atTop (4 : ℝ)] with x hx1 hx2 hx3 hx4 H hH
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hxc0 : (0 : ℝ) < x ^ (1 / (L : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hxB0 : (0 : ℝ) < x ^ B := Real.rpow_pos_of_pos hx0 _
  have hsplit : x ^ B * x ^ (1 / (L : ℝ) - B) = x ^ (1 / (L : ℝ)) := by
    rw [← Real.rpow_add hx0]
    ring_nf
  have hkey : 4 * x ^ B ≤ x ^ (1 / (L : ℝ)) := by
    calc 4 * x ^ B = x ^ B * 4 := by ring
      _ ≤ x ^ B * x ^ (1 / (L : ℝ) - B) := by gcongr
      _ = x ^ (1 / (L : ℝ)) := hsplit
  have hN0 : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg _
  have hafloor : ((⌊x ^ (1 / (L : ℝ))⌋₊ : ℕ) : ℝ) ≤ x ^ (1 / (L : ℝ)) := Nat.floor_le hxc0.le
  have halt : x ^ (1 / (L : ℝ)) < ((⌊x ^ (1 / (L : ℝ))⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hAR : 2 * (H : ℝ) + (N₀ : ℝ) + 5 < ((⌊x ^ (1 / (L : ℝ))⌋₊ : ℕ) : ℝ) := by linarith
  have hAN : 2 * H + N₀ + 5 < ⌊x ^ (1 / (L : ℝ))⌋₊ := by exact_mod_cast hAR
  have ha : N₀ + H + 1 ≤ ⌊x ^ (1 / (L : ℝ))⌋₊ := by omega
  have hHa : 2 * H + 4 ≤ ⌊x ^ (1 / (L : ℝ))⌋₊ := by omega
  have ha0 : (0 : ℝ) < ((⌊x ^ (1 / (L : ℝ))⌋₊ : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
    linarith
  have hden : x ^ (1 / (L : ℝ)) / 2 ≤ ((⌊x ^ (1 / (L : ℝ))⌋₊ : ℕ) : ℝ) := by linarith
  have hnum : ((2 * L : ℕ) : ℝ) * ((H + 2 : ℕ) : ℝ) ≤ 2 * (L : ℝ) * (2 * x ^ B) := by
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith
  have herr : ((2 * L : ℕ) : ℝ) * ((H + 2 : ℕ) : ℝ) / ((⌊x ^ (1 / (L : ℝ))⌋₊ : ℕ) : ℝ) ≤
      8 * L * x ^ (B - 1 / (L : ℝ)) := by
    have hpos : (0 : ℝ) < x ^ (1 / (L : ℝ)) / 2 := by linarith
    calc ((2 * L : ℕ) : ℝ) * ((H + 2 : ℕ) : ℝ) / ((⌊x ^ (1 / (L : ℝ))⌋₊ : ℕ) : ℝ)
        ≤ 2 * (L : ℝ) * (2 * x ^ B) / (x ^ (1 / (L : ℝ)) / 2) := by gcongr
      _ = 8 * L * (x ^ B / x ^ (1 / (L : ℝ))) := by field_simp; ring
      _ = 8 * L * x ^ (B - 1 / (L : ℝ)) := by rw [← Real.rpow_sub hx0]
  exact ⟨(Classical.choice (nonempty_primeBlocks_of_root hL hwindow hx0 ha hHa)).monoError herr⟩

/-- Threshold form of `eventually_nonempty_primeBlocks`, convenient when the blocks are needed
at two different centres (`x = p` and `x = q`) under a single threshold. -/
theorem exists_threshold_nonempty_primeBlocks {L N₀ : ℕ} (hL : 0 < L)
    (hwindow : ∀ n : ℕ, N₀ ≤ n → ∃ r : ℕ, r.Prime ∧ n ^ L < r ∧ r ≤ (n + 1) ^ L)
    {B : ℝ} (hB : 0 < B) (hBL : B < 1 / (L : ℝ)) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ H : ℕ, (H : ℝ) ≤ x ^ B + 2 →
      Nonempty (PrimeBlocks H x (8 * L * x ^ (B - 1 / (L : ℝ)))) :=
  eventually_atTop.1 (eventually_nonempty_primeBlocks hL hwindow hB hBL)

/-! ### The §3.3 table -/

/-- The four blocks of §3.3 attached to a highly composite `n` with largest prime factor `p`
and `q` the largest prime with exponent `≥ 2`: `t` primes just above `p` (exponent `0` in `n`),
`t` primes just below `p` (exponent `1`), `s` primes just above `q` (exponent `1`) and `s`
primes just below `q` (exponent `≥ 2`).  The last five fields record the ordering
`q' i < q < Q j < p' k < p < P l`, which in particular makes `{P} ∪ {q'}` and `{Q} ∪ {p'}`
disjoint families. -/
structure FourBlocks (n p q s t : ℕ) (εp εq : ℝ) where
  /-- The `t` primes just above `p`. -/
  P : Fin t → ℕ
  /-- The `t` primes just below `p`. -/
  p' : Fin t → ℕ
  /-- The `s` primes just above `q`. -/
  Q : Fin s → ℕ
  /-- The `s` primes just below `q`. -/
  q' : Fin s → ℕ
  /-- The block above `p` is pairwise distinct. -/
  P_injective : Function.Injective P
  /-- The block below `p` is pairwise distinct. -/
  p'_injective : Function.Injective p'
  /-- The block above `q` is pairwise distinct. -/
  Q_injective : Function.Injective Q
  /-- The block below `q` is pairwise distinct. -/
  q'_injective : Function.Injective q'
  /-- The block above `p` consists of primes. -/
  P_prime : ∀ i, (P i).Prime
  /-- The block below `p` consists of primes. -/
  p'_prime : ∀ i, (p' i).Prime
  /-- The block above `q` consists of primes. -/
  Q_prime : ∀ i, (Q i).Prime
  /-- The block below `q` consists of primes. -/
  q'_prime : ∀ i, (q' i).Prime
  /-- The block above `p` is logarithmically `εp`-close to `p`. -/
  P_log_error : ∀ i, |Real.log (P i) - Real.log p| ≤ εp
  /-- The block below `p` is logarithmically `εp`-close to `p`. -/
  p'_log_error : ∀ i, |Real.log (p' i) - Real.log p| ≤ εp
  /-- The block above `q` is logarithmically `εq`-close to `q`. -/
  Q_log_error : ∀ i, |Real.log (Q i) - Real.log q| ≤ εq
  /-- The block below `q` is logarithmically `εq`-close to `q`. -/
  q'_log_error : ∀ i, |Real.log (q' i) - Real.log q| ≤ εq
  /-- Primes above `p` do not divide `n`. -/
  P_factorization : ∀ i, n.factorization (P i) = 0
  /-- Primes just below `p` have exponent `1` in `n`. -/
  p'_factorization : ∀ i, n.factorization (p' i) = 1
  /-- Primes just above `q` have exponent `1` in `n`. -/
  Q_factorization : ∀ i, n.factorization (Q i) = 1
  /-- Primes just below `q` have exponent at least `2` in `n`. -/
  q'_factorization : ∀ i, 2 ≤ n.factorization (q' i)
  /-- The block below `q` lies below `q`. -/
  q'_lt : ∀ i, q' i < q
  /-- The block above `q` lies above `q`. -/
  lt_Q : ∀ i, q < Q i
  /-- The block above `q` lies entirely below the block below `p`. -/
  Q_lt_p' : ∀ (i : Fin s) (j : Fin t), Q i < p' j
  /-- The block below `p` lies below `p`. -/
  p'_lt : ∀ j, p' j < p
  /-- The block above `p` lies above `p`. -/
  lt_P : ∀ j, p < P j

/-- **Assembling the §3.3 table.**  From blocks of common size `H` around `p` and around `q`,
the Dirichlet sizes `s, t ≤ H`, the separation `2q ≤ p` (Lemma 2′ places `q` below `p/2`), the
smallness `εp + εq < log 2` of the two errors, and the three *hypotheses on `n`* supplied by
`Structure.lean` — primes above `p` do not divide `n`, primes strictly between `q` and `p`
have exponent `1`, primes below `q` have exponent `≥ 2` — one obtains the four blocks with
their exponents and the full ordering chain. -/
theorem exists_fourBlocks {n p q s t H : ℕ} {εp εq : ℝ}
    (Bp : PrimeBlocks H (p : ℝ) εp) (Bq : PrimeBlocks H (q : ℝ) εq)
    (hs : s ≤ H) (ht : t ≤ H) (hq0 : 0 < q) (hqp : 2 * q ≤ p)
    (hεp0 : 0 ≤ εp) (hεq0 : 0 ≤ εq) (hε : εp + εq < Real.log 2)
    (hzero : ∀ r : ℕ, r.Prime → p < r → n.factorization r = 0)
    (hone : ∀ r : ℕ, r.Prime → q < r → r < p → n.factorization r = 1)
    (htwo : ∀ r : ℕ, r.Prime → r < q → 2 ≤ n.factorization r) :
    Nonempty (FourBlocks n p q s t εp εq) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hqpR : 2 * (q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hqp
  have hEp1 : (1 : ℝ) ≤ Real.exp εp := Real.one_le_exp hεp0
  have hEq1 : (1 : ℝ) ≤ Real.exp εq := Real.one_le_exp hεq0
  have hEp0 : (0 : ℝ) < Real.exp εp := Real.exp_pos _
  have hEq0 : (0 : ℝ) < Real.exp εq := Real.exp_pos _
  have hE : Real.exp εp * Real.exp εq < 2 := by
    rw [← Real.exp_add]
    calc Real.exp (εp + εq) < Real.exp (Real.log 2) := Real.exp_lt_exp.2 hε
      _ = 2 := Real.exp_log two_pos
  have hqE : (q : ℝ) * (Real.exp εp * Real.exp εq) < (p : ℝ) := by nlinarith
  set Bp' : PrimeBlocks t (p : ℝ) εp := Bp.restrict ht with hBp'
  set Bq' : PrimeBlocks s (q : ℝ) εq := Bq.restrict hs with hBq'
  have hQlt : ∀ i : Fin s, (Bq'.up i : ℝ) < (p : ℝ) := by
    intro i
    have h1 : (Bq'.up i : ℝ) ≤ (q : ℝ) * Real.exp εq := Bq'.up_le_mul_exp hqR i
    nlinarith
  have hp'gt : ∀ j : Fin t, (q : ℝ) < (Bp'.down j : ℝ) := by
    intro j
    have h1 : (p : ℝ) / Real.exp εp ≤ (Bp'.down j : ℝ) := Bp'.div_exp_le_down hpR j
    refine lt_of_lt_of_le ?_ h1
    rw [lt_div_iff₀ hEp0]
    have h3 : (q : ℝ) * Real.exp εp ≤ (q : ℝ) * Real.exp εp * Real.exp εq :=
      le_mul_of_one_le_right (mul_pos hqR hEp0).le hEq1
    nlinarith
  have hQp' : ∀ (i : Fin s) (j : Fin t), (Bq'.up i : ℝ) < (Bp'.down j : ℝ) := by
    intro i j
    have h1 : (Bq'.up i : ℝ) ≤ (q : ℝ) * Real.exp εq := Bq'.up_le_mul_exp hqR i
    have h2 : (p : ℝ) / Real.exp εp ≤ (Bp'.down j : ℝ) := Bp'.div_exp_le_down hpR j
    rw [div_le_iff₀ hEp0] at h2
    nlinarith
  refine ⟨{
    P := Bp'.up
    p' := Bp'.down
    Q := Bq'.up
    q' := Bq'.down
    P_injective := Bp'.up_injective
    p'_injective := Bp'.down_injective
    Q_injective := Bq'.up_injective
    q'_injective := Bq'.down_injective
    P_prime := Bp'.up_prime
    p'_prime := Bp'.down_prime
    Q_prime := Bq'.up_prime
    q'_prime := Bq'.down_prime
    P_log_error := Bp'.up_log_error
    p'_log_error := Bp'.down_log_error
    Q_log_error := Bq'.up_log_error
    q'_log_error := Bq'.down_log_error
    P_factorization := ?_
    p'_factorization := ?_
    Q_factorization := ?_
    q'_factorization := ?_
    q'_lt := ?_
    lt_Q := ?_
    Q_lt_p' := ?_
    p'_lt := ?_
    lt_P := ?_ }⟩
  · exact fun i ↦ hzero _ (Bp'.up_prime i) (by exact_mod_cast Bp'.lt_up i)
  · exact fun j ↦ hone _ (Bp'.down_prime j) (by exact_mod_cast hp'gt j)
      (by exact_mod_cast Bp'.down_lt j)
  · exact fun i ↦ hone _ (Bq'.up_prime i) (by exact_mod_cast Bq'.lt_up i)
      (by exact_mod_cast hQlt i)
  · exact fun i ↦ htwo _ (Bq'.down_prime i) (by exact_mod_cast Bq'.down_lt i)
  · exact fun i ↦ by exact_mod_cast Bq'.down_lt i
  · exact fun i ↦ by exact_mod_cast Bq'.lt_up i
  · exact fun i j ↦ by exact_mod_cast hQp' i j
  · exact fun j ↦ by exact_mod_cast Bp'.down_lt j
  · exact fun j ↦ by exact_mod_cast Bp'.lt_up j

end Erdos381Lower
