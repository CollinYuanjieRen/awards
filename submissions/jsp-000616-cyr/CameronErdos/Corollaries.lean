import CameronErdos.Main
import CameronErdos.Counting.Basic

/-!
# Corollaries of the Cameron–Erdős theorem (JSP-000616 / Erdős #748)

This file restates the root theorem `CameronErdos.cameronErdos`
(`CameronErdos/Main.lean`) in the shapes used on the problem page
(<https://www.erdosproblems.com/748>) and in the literature.  Writing
`f(n) = CameronErdos.sumFreeCount n` for the number of sum-free subsets of `[1, n]`:

* `CameronErdos.two_pow_half_le_sumFreeCount`, `CameronErdos.two_pow_ceil_half_le_sumFreeCount`
  — the trivial lower bounds `2^{⌊n/2⌋} ≤ 2^{⌈n/2⌉} ≤ f(n)` coming from the all-odd sets
  (`CameronErdos.lem_oddCount`);
* `CameronErdos.sumFreeCount_le_mul_two_pow_half` — the real-valued reading
  `f(n) ≤ C · 2^{n/2}` of the frozen (squared) root statement;
* `CameronErdos.sumFreeCount_isBigO`, `CameronErdos.two_pow_half_isBigO_sumFreeCount`
  — `f(n) = Θ(2^{n/2})`;
* `CameronErdos.tendsto_logb_sumFreeCount_div` — the displayed form
  `log₂ f(n) / n → 1/2`, and `CameronErdos.sumFreeCount_eq_two_pow_half_add_littleO`
  — `f(n) = 2^{(1/2 + o(1))n}`.

No new mathematics happens here: everything is derived from `CameronErdos.cameronErdos`
and `CameronErdos.lem_oddCount`.
-/

open Finset Filter Topology

namespace CameronErdos

/-! ## Lower bounds: the sets of odd numbers -/

/-- **`2^{⌈n/2⌉} ≤ f(n)`.**  Every set of odd numbers in `[1, n]` is sum-free, and there are
`2^{⌈n/2⌉} = 2^{(n+1)/2}` of them (`CameronErdos.lem_oddCount`). -/
theorem two_pow_ceil_half_le_sumFreeCount (n : ℕ) : 2 ^ ((n + 1) / 2) ≤ sumFreeCount n := by
  obtain ⟨-, hcard, hmem⟩ := lem_oddCount n
  rw [← hcard]
  refine Finset.card_le_card ?_
  intro A hA
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨(hmem A hA).1, (hmem A hA).2⟩

/-- **`2^{⌊n/2⌋} ≤ f(n)`.**  A weaker form of `two_pow_ceil_half_le_sumFreeCount`. -/
theorem two_pow_half_le_sumFreeCount (n : ℕ) : 2 ^ (n / 2) ≤ sumFreeCount n :=
  le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right (Nat.le_succ n)))
    (two_pow_ceil_half_le_sumFreeCount n)

/-- `f(n) ≥ 1`: the empty set is sum-free. -/
private lemma one_le_sumFreeCount (n : ℕ) : 1 ≤ sumFreeCount n :=
  le_trans Nat.one_le_two_pow (two_pow_half_le_sumFreeCount n)

private lemma sumFreeCount_pos_real (n : ℕ) : (0:ℝ) < (sumFreeCount n : ℝ) := by
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_sumFreeCount n)

/-! ## Real-valued upper bound -/

private lemma sqrt_two_pow (n : ℕ) : Real.sqrt ((2:ℝ) ^ n) = (2:ℝ) ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (2:ℝ) n, ← Real.rpow_mul (by norm_num)]
  ring_nf

/-- **The Cameron–Erdős conjecture, real-valued form.**  There is `C > 0` with
`f(n) ≤ C · 2^{n/2}` for all `n`. -/
theorem sumFreeCount_le_mul_two_pow_half :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (sumFreeCount n : ℝ) ≤ C * 2 ^ ((n : ℝ) / 2) := by
  obtain ⟨C₀, hC₀, hC⟩ := cameronErdos
  have hC₀R : (0:ℝ) < (C₀ : ℝ) := by exact_mod_cast hC₀
  refine ⟨Real.sqrt C₀, Real.sqrt_pos.mpr hC₀R, fun n => ?_⟩
  have h : ((sumFreeCount n : ℝ)) ^ 2 ≤ (C₀ : ℝ) * 2 ^ n := by exact_mod_cast hC n
  have h1 := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq (le_of_lt (sumFreeCount_pos_real n)),
    Real.sqrt_mul (le_of_lt hC₀R), sqrt_two_pow] at h1
  exact h1

/-! ## `f(n) = Θ(2^{n/2})` -/

private lemma rpow_half_le_two : (2:ℝ) ^ ((1:ℝ)/2) ≤ 2 := by
  calc (2:ℝ) ^ ((1:ℝ)/2) ≤ (2:ℝ) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2

/-- `n/2 − 1/2 ≤ ⌊n/2⌋ ≤ n/2` as reals. -/
private lemma cast_div_two_bounds (n : ℕ) :
    (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) ∧ ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
  have hmod : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
  have hmodle : n % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt n (by norm_num))
  have hcast : (2:ℝ) * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hmod
  have hmodR : ((n % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hmodle
  have hmodR0 : (0:ℝ) ≤ ((n % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith

private lemma two_rpow_half_le_two_mul (n : ℕ) :
    (2:ℝ) ^ ((n : ℝ) / 2) ≤ 2 * ((2 ^ (n / 2) : ℕ) : ℝ) := by
  have hb := (cast_div_two_bounds n).1
  have hnat : ((2 ^ (n / 2) : ℕ) : ℝ) = (2:ℝ) ^ (((n / 2 : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]; push_cast; ring
  have hpos : (0:ℝ) ≤ (2:ℝ) ^ (((n / 2 : ℕ) : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  rw [hnat]
  calc (2:ℝ) ^ ((n : ℝ) / 2) ≤ (2:ℝ) ^ (((n / 2 : ℕ) : ℝ) + 1 / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (2:ℝ) ^ (((n / 2 : ℕ) : ℝ)) * (2:ℝ) ^ ((1:ℝ) / 2) := Real.rpow_add (by norm_num) _ _
    _ ≤ (2:ℝ) ^ (((n / 2 : ℕ) : ℝ)) * 2 := mul_le_mul_of_nonneg_left rpow_half_le_two hpos
    _ = 2 * (2:ℝ) ^ (((n / 2 : ℕ) : ℝ)) := by ring

/-- **`f(n) = O(2^{n/2})`** — the Cameron–Erdős conjecture in `IsBigO` form. -/
theorem sumFreeCount_isBigO :
    (fun n : ℕ => (sumFreeCount n : ℝ)) =O[atTop] (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) / 2)) := by
  obtain ⟨C, hCpos, hC⟩ := sumFreeCount_le_mul_two_pow_half
  refine Asymptotics.isBigO_of_le' (c := C) atTop (fun n => ?_)
  rw [Real.norm_of_nonneg (le_of_lt (sumFreeCount_pos_real n)),
    Real.norm_of_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))]
  exact hC n

/-- **`2^{n/2} = O(f(n))`** — the matching lower bound, from the all-odd sets. -/
theorem two_pow_half_isBigO_sumFreeCount :
    (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) / 2)) =O[atTop] (fun n : ℕ => (sumFreeCount n : ℝ)) := by
  refine Asymptotics.isBigO_of_le' (c := 2) atTop (fun n => ?_)
  rw [Real.norm_of_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)),
    Real.norm_of_nonneg (le_of_lt (sumFreeCount_pos_real n))]
  have h1 : ((2 ^ (n / 2) : ℕ) : ℝ) ≤ (sumFreeCount n : ℝ) := by
    exact_mod_cast two_pow_half_le_sumFreeCount n
  calc (2:ℝ) ^ ((n : ℝ) / 2) ≤ 2 * ((2 ^ (n / 2) : ℕ) : ℝ) := two_rpow_half_le_two_mul n
    _ ≤ 2 * (sumFreeCount n : ℝ) := by linarith

/-! ## The displayed form: `log₂ f(n) / n → 1/2` -/

private lemma logb_sumFreeCount_lower (n : ℕ) :
    (n : ℝ) / 2 - 1 ≤ Real.logb 2 (sumFreeCount n) := by
  have h1 : ((2 ^ (n / 2) : ℕ) : ℝ) ≤ (sumFreeCount n : ℝ) := by
    exact_mod_cast two_pow_half_le_sumFreeCount n
  have hpos : (0:ℝ) < ((2 ^ (n / 2) : ℕ) : ℝ) := by positivity
  have h2 : Real.logb 2 ((2 ^ (n / 2) : ℕ) : ℝ) ≤ Real.logb 2 (sumFreeCount n) :=
    Real.logb_le_logb_of_le (by norm_num) hpos h1
  have h3 : Real.logb 2 ((2 ^ (n / 2) : ℕ) : ℝ) = ((n / 2 : ℕ) : ℝ) := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (b := 2) (by norm_num), mul_one]
  rw [h3] at h2
  have hb := (cast_div_two_bounds n).1
  linarith

private lemma logb_sumFreeCount_upper {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ n : ℕ, (sumFreeCount n : ℝ) ≤ C * 2 ^ ((n : ℝ) / 2)) (n : ℕ) :
    Real.logb 2 (sumFreeCount n) ≤ (n : ℝ) / 2 + Real.logb 2 C := by
  have hrpow : (0:ℝ) < (2:ℝ) ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : Real.logb 2 (sumFreeCount n) ≤ Real.logb 2 (C * 2 ^ ((n : ℝ) / 2)) :=
    Real.logb_le_logb_of_le (by norm_num) (sumFreeCount_pos_real n) (hC n)
  rw [Real.logb_mul (ne_of_gt hCpos) (ne_of_gt hrpow),
    Real.logb_rpow (by norm_num) (by norm_num)] at h1
  linarith

/-- **The form displayed on erdosproblems.com/748**: `log₂ f(n) / n → 1/2`. -/
theorem tendsto_logb_sumFreeCount_div :
    Tendsto (fun n : ℕ => Real.logb 2 (sumFreeCount n) / n) atTop (𝓝 (1 / 2)) := by
  obtain ⟨C, hCpos, hC⟩ := sumFreeCount_le_mul_two_pow_half
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hlow : Tendsto (fun n : ℕ => 1 / 2 - 1 * (1 / (n : ℝ))) atTop (𝓝 (1 / 2)) := by
    have := (tendsto_const_nhds (x := (1/2 : ℝ)) (f := atTop (α := ℕ))).sub
      (hinv.const_mul (1 : ℝ))
    simpa using this
  have hhigh : Tendsto (fun n : ℕ => 1 / 2 + Real.logb 2 C * (1 / (n : ℝ))) atTop (𝓝 (1 / 2)) := by
    have := (tendsto_const_nhds (x := (1/2 : ℝ)) (f := atTop (α := ℕ))).add
      (hinv.const_mul (Real.logb 2 C))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h := logb_sumFreeCount_lower n
    rw [le_div_iff₀ hnR]
    have : (1 / 2 - 1 * (1 / (n : ℝ))) * (n : ℝ) = (n : ℝ) / 2 - 1 := by
      field_simp
    rw [this]
    exact h
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h := logb_sumFreeCount_upper hCpos hC n
    rw [div_le_iff₀ hnR]
    have : (1 / 2 + Real.logb 2 C * (1 / (n : ℝ))) * (n : ℝ) = (n : ℝ) / 2 + Real.logb 2 C := by
      field_simp
    rw [this]
    exact h

/-- **`f(n) = 2^{(1/2 + o(1))n}`**, the shape in which the Cameron–Erdős count is usually
quoted. -/
theorem sumFreeCount_eq_two_pow_half_add_littleO :
    ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∀ n, 0 < n → (sumFreeCount n : ℝ) = 2 ^ ((1 / 2 + g n) * n) := by
  refine ⟨fun n => Real.logb 2 (sumFreeCount n) / n - 1 / 2, ?_, ?_⟩
  · have := tendsto_logb_sumFreeCount_div.sub_const (1 / 2 : ℝ)
    simpa using this
  · intro n hn
    have hnR : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hexp : (1 / 2 + (Real.logb 2 (sumFreeCount n) / n - 1 / 2)) * (n : ℝ)
        = Real.logb 2 (sumFreeCount n) := by
      field_simp
      ring
    rw [hexp, Real.rpow_logb (by norm_num) (by norm_num) (sumFreeCount_pos_real n)]

/-! ## Axiom audit -/

#print axioms two_pow_ceil_half_le_sumFreeCount
#print axioms two_pow_half_le_sumFreeCount
#print axioms one_le_sumFreeCount
#print axioms sumFreeCount_pos_real
#print axioms sqrt_two_pow
#print axioms sumFreeCount_le_mul_two_pow_half
#print axioms rpow_half_le_two
#print axioms cast_div_two_bounds
#print axioms two_rpow_half_le_two_mul
#print axioms sumFreeCount_isBigO
#print axioms two_pow_half_isBigO_sumFreeCount
#print axioms logb_sumFreeCount_lower
#print axioms logb_sumFreeCount_upper
#print axioms tendsto_logb_sumFreeCount_div
#print axioms sumFreeCount_eq_two_pow_half_add_littleO

end CameronErdos
