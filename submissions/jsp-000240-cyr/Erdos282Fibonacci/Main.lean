import Mathlib

/-!
# Erdős Problem #282: Fibonacci's greedy unit-fraction algorithm terminates for `A = ℕ`

For an infinite set `A ⊆ ℕ` and a rational `x ∈ (0, 1)`, the greedy algorithm repeatedly chooses
the least unused `n ∈ A` with `n ≥ 1/x` and replaces `x` by `x − 1/n`.  Erdős (after Stein) asked
whether this always terminates when `x` has odd denominator and `A` is the set of odd numbers,
and more generally for which `(x, A)` it terminates (OPEN; not addressed here).  The problem
page records: "In 1202 Fibonacci observed that this process terminates for any `x` when
`A = ℕ`."  This file proves that statement in the exact shape of the formal-conjectures theorem
`Erdos282.erdos_282.variants.fibonacci` (tagged "textbook" with `sorry`), with the
formal-conjectures model `greedyUnitFractionRem` of the process copied verbatim.  The odd-number
question and Graham's results are not claimed.

Proof.  Write `x = p/q` in lowest terms.  The chosen `n = ⌈q/p⌉ ≥ 2` satisfies
`(n − 1) p < q ≤ n p`, so the remainder `x − 1/n = (np − q)/(nq)` is nonnegative with numerator
`np − q < p`: the numerators strictly decrease, so after at most `p` steps the remainder is `0`,
and the model then stays at `0`.  Removing the used denominators from `A` never changes the
choice, because the next remainder is below `1/(n(n−1))`, so the next denominator exceeds every
previously used one.
-/

open Filter Real

namespace Erdos282

/-- Let $A\subseteq \mathbb{N}$ be an infinite set and consider the following
greedy algorithm for a rational $x$: choose the minimal $n\in A$ not used so far such
that $n\geq 1/x$ and repeat with $x$ replaced by $x-\frac{1}{n}$.
This process of subtracting unit fractions is modelled in `greedyUnitFractionRem`.
At each step `t : ℕ`, the function `greedyUnitFractionRem A x t` returns the remainder
of `x` with respect to the first `t + 1` unit fractions, with distinct denominators taken
from `A`. Once the remainder reaches `0` it stays `0`, and the process terminates. This
corresponds to producing a representation of `x` as the sum of distinct unit fractions with
denominators from `A`, however this function does not return this representation. -/
noncomputable def greedyUnitFractionRem (A : Set ℕ) (x : ℚ) (t : ℕ) : ℚ :=
  if x ≤ 0 then 0 else
    let n := sInf { n | n ∈ A ∧ 1 / x ≤ n }
    let rem := x - 1 / n
    match t with
    | 0 => rem
    | t + 1 => greedyUnitFractionRem (A \ {n}) rem t

/-- Once the remainder is nonpositive the model returns `0` forever. -/
private lemma greedy_of_nonpos (A : Set ℕ) (x : ℚ) (hx : x ≤ 0) (t : ℕ) :
    greedyUnitFractionRem A x t = 0 := by
  cases t <;> rw [greedyUnitFractionRem] <;> simp [hx]

/-- One greedy step: from a positive remainder `x` the model picks `n = sInf {n ∈ A | n ≥ 1/x}`
and continues with `A \ {n}` and the new remainder `x - 1/n`. -/
theorem greedyUnitFractionRem_succ (A : Set ℕ) {x : ℚ} (hx : ¬ x ≤ 0) (t : ℕ) :
    greedyUnitFractionRem A x (t + 1) =
      greedyUnitFractionRem (A \ {sInf { n | n ∈ A ∧ 1 / x ≤ (n : ℚ) }})
        (x - 1 / (sInf { n | n ∈ A ∧ 1 / x ≤ (n : ℚ) } : ℕ)) t := by
  rw [greedyUnitFractionRem]; simp [hx]

/-- The numerator of `a / b` in lowest terms is at most `a`, for positive integers `a`, `b`. -/
private lemma num_div_le {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    ((a : ℚ) / (b : ℚ)).num ≤ a :=
  Int.le_of_dvd ha (by rw [Rat.intCast_div_eq_divInt]; exact Rat.num_dvd a hb.ne')

/-- If every already used denominator is smaller than `1 / x`, the greedy choice is `⌈1/x⌉₊`. -/
private lemma sInf_eq_ceil {x : ℚ} {F : Set ℕ} (hF : ∀ m ∈ F, (m : ℚ) < 1 / x) :
    sInf { n | n ∈ Set.univ \ F ∧ 1 / x ≤ (n : ℚ) } = ⌈(1 / x : ℚ)⌉₊ := by
  set c := ⌈(1 / x : ℚ)⌉₊ with hc
  have hce : (1 / x : ℚ) ≤ (c : ℚ) := Nat.le_ceil _
  have hcmem : c ∈ { n | n ∈ Set.univ \ F ∧ 1 / x ≤ (n : ℚ) } :=
    ⟨⟨Set.mem_univ _, fun hcF => absurd hce (not_le.mpr (hF c hcF))⟩, hce⟩
  exact le_antisymm (Nat.sInf_le hcmem) (Nat.ceil_le.mpr (Nat.sInf_mem ⟨c, hcmem⟩).2)

/-- Main induction, on the numerator of `x`: for `0 < x < 1` and a set `F` of used denominators
all below `1 / x`, the greedy process over `ℕ \ F` eventually returns `0`. -/
private lemma greedy_terminates : ∀ (k : ℕ) (x : ℚ) (F : Set ℕ), 0 < x → x < 1 →
    x.num.natAbs ≤ k → (∀ m ∈ F, (m : ℚ) < 1 / x) →
    ∃ T, ∀ t ≥ T, greedyUnitFractionRem (Set.univ \ F) x t = 0 := by
  intro k
  induction k with
  | zero =>
    intro x F hx0 _ hk _
    exact absurd (Int.natAbs_eq_zero.mp (Nat.le_zero.mp hk)) (Rat.num_ne_zero.mpr hx0.ne')
  | succ k ih =>
    intro x F hx0 hx1 hk hF
    have hxne : ¬ x ≤ 0 := not_le.mpr hx0
    have h1x : (1 : ℚ) < 1 / x := one_lt_one_div hx0 hx1
    set c := ⌈(1 / x : ℚ)⌉₊ with hcdef
    have hc2 : 2 ≤ c := Nat.lt_ceil.mpr (by exact_mod_cast h1x)
    have hcq2 : (2 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc2
    have hcpos : (0 : ℚ) < (c : ℚ) := by linarith
    have hce : (1 / x : ℚ) ≤ (c : ℚ) := Nat.le_ceil _
    have hclt : (c : ℚ) - 1 < 1 / x := by
      have h := Nat.ceil_lt_add_one (R := ℚ) (a := 1 / x) (by positivity)
      rw [← hcdef] at h
      linarith
    have hsinf : sInf { n | n ∈ Set.univ \ F ∧ 1 / x ≤ (n : ℚ) } = c := sInf_eq_ceil hF
    set rem := x - 1 / (c : ℚ) with hremdef
    have hstep : ∀ t, greedyUnitFractionRem (Set.univ \ F) x (t + 1)
        = greedyUnitFractionRem ((Set.univ \ F) \ {c}) rem t := by
      intro t
      rw [greedyUnitFractionRem_succ _ hxne t, hsinf]
    have hrem0 : 0 ≤ rem := by
      have : 1 / (c : ℚ) ≤ x := (one_div_le hx0 hcpos).mp hce
      rw [hremdef]; linarith
    have hc1pos : (0 : ℚ) < (c : ℚ) - 1 := by linarith
    have hxlt : x < 1 / ((c : ℚ) - 1) := (lt_one_div hx0 hc1pos).mpr hclt
    have hremlt : rem < 1 / (c : ℚ) := by
      have h2 : 1 / ((c : ℚ) - 1) ≤ 2 / (c : ℚ) := by
        rw [div_le_div_iff₀ hc1pos hcpos]; linarith
      have h3 : (2 : ℚ) / (c : ℚ) = 1 / (c : ℚ) + 1 / (c : ℚ) := by ring
      rw [hremdef]; linarith
    have hrem1 : rem < 1 := by
      have : 1 / (c : ℚ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hcpos (by norm_num)]; linarith
      linarith
    rcases eq_or_lt_of_le hrem0 with heq | hpos
    · refine ⟨1, fun t ht => ?_⟩
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [hstep t']
      exact greedy_of_nonpos _ _ (le_of_eq heq.symm) t'
    · have hcltrem : (c : ℚ) < 1 / rem := (lt_one_div hpos hcpos).mp hremlt
      have hxnum : 0 < x.num := Rat.num_pos.mpr hx0
      have hdenq : ((x.den : ℚ)) ≠ 0 := by positivity
      have hnumeq : (x.num : ℚ) = x * x.den := (div_eq_iff hdenq).mp (Rat.num_div_den x)
      set a : ℤ := x.num * (c : ℤ) - (x.den : ℤ) with hadef
      set b : ℤ := (x.den : ℤ) * (c : ℤ) with hbdef
      have hbpos : 0 < b := by
        have h1 : 0 < (x.den : ℤ) := by exact_mod_cast x.pos
        have h2 : 0 < (c : ℤ) := by exact_mod_cast (by omega : 0 < c)
        rw [hbdef]; positivity
      have hbq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hbpos
      have hremeq : rem = (a : ℚ) / (b : ℚ) := by
        rw [hadef, hbdef, hremdef]; push_cast; rw [hnumeq]; field_simp
      have hapos : 0 < a := by
        by_contra hcon
        push Not at hcon
        have h1 : (a : ℚ) ≤ 0 := by exact_mod_cast hcon
        have h2 : (a : ℚ) / (b : ℚ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h1 hbq.le
        rw [hremeq] at hpos
        linarith
      have haltnum : a < x.num := by
        have hlt : ((c : ℚ) - 1) * x < 1 := (lt_div_iff₀ hx0).mp hclt
        have hdpos : (0 : ℚ) < (x.den : ℚ) := by positivity
        have h2 : ((c : ℚ) - 1) * x * (x.den : ℚ) < 1 * (x.den : ℚ) :=
          mul_lt_mul_of_pos_right hlt hdpos
        rw [one_mul, mul_assoc, ← hnumeq] at h2
        have h3 : ((a : ℤ) : ℚ) < ((x.num : ℤ) : ℚ) := by
          rw [hadef]; push_cast; linarith
        exact_mod_cast h3
      have hremnum_le : rem.num ≤ a := by rw [hremeq]; exact num_div_le hapos hbpos
      have hremnumpos : 0 < rem.num := Rat.num_pos.mpr hpos
      have hmeasure : rem.num.natAbs < x.num.natAbs := by omega
      have hF' : ∀ m ∈ F ∪ {c}, (m : ℚ) < 1 / rem := by
        intro m hm
        simp only [Set.mem_union, Set.mem_singleton_iff] at hm
        rcases hm with hm | rfl
        · calc (m : ℚ) < 1 / x := hF m hm
            _ ≤ (c : ℚ) := hce
            _ < 1 / rem := hcltrem
        · exact hcltrem
      obtain ⟨T, hT⟩ := ih rem (F ∪ {c}) hpos hrem1 (by omega) hF'
      refine ⟨T + 1, fun t ht => ?_⟩
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [hstep t', Set.sdiff_sdiff]
      exact hT t' (by omega)

/-- In 1202 Fibonacci observed that this process terminates for any $x$ when $A=\mathbb{N}$. -/
theorem erdos_282.variants.fibonacci {x : ℚ} (hx : x ∈ Set.Ioo 0 1) :
    greedyUnitFractionRem .univ x =ᶠ[atTop] 0 := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨T, hT⟩ := greedy_terminates x.num.natAbs x ∅ hx0 hx1 le_rfl (by simp)
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨T, fun t ht => ?_⟩
  have h := hT t ht
  rw [Set.sdiff_empty] at h
  simpa using h

end Erdos282

open Erdos282

/-- The same statement as a closed formula (no binders), used as the graded root: there is no
rational in `(0, 1)` for which the greedy process over `ℕ` fails to terminate. -/
theorem erdos_282_fibonacci_closed :
    ¬ ∃ x : ℚ, x ∈ Set.Ioo 0 1 ∧ ¬ (greedyUnitFractionRem Set.univ x =ᶠ[atTop] 0) := by
  rintro ⟨x, hx, h⟩
  exact h (erdos_282.variants.fibonacci hx)
