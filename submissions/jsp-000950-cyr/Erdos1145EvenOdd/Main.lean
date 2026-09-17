import Mathlib

/-!
# Erdős Problem #1145: the even/odd binary-digit sets have `1_A ∗ 1_B(n) = 1` for all `n`

Erdős and Sárközy asked: for sets `A`, `B` of positive integers with `aₙ/bₙ → 1` and `A + B`
containing all large integers, must `limsup 1_A ∗ 1_B(n) = ∞` (OPEN; not addressed here)?  The
problem page records: "Some condition relating `A` and `B` is necessary since, for example, if
`A` is the set of all integers with only even binary digits and `B` is the set of all integers
with only odd binary digits then `1_A ∗ 1_B(n) = 1` for all `n`."  This file proves that example,
with the formal-conjectures definitions `Set.indicatorOne` (`𝟙_`) and
`AdditiveCombinatorics.sumConv` (`∗`) copied verbatim (as used by the formal-conjectures
rendering of #1145, which includes `0` in the sets): with `A` the naturals whose binary digits
`1` occur only in even positions and `B` those with `1`s only in odd positions, every `n` has
exactly one representation `n = a + b` with `a ∈ A`, `b ∈ B`.  The conjecture itself is not
claimed.

Proof.  Every natural number splits uniquely into its even-position and odd-position binary
digits: `a` is obtained by keeping the bits at even positions, `b` the bits at odd positions,
and any `a' ∈ A`, `b' ∈ B` with `a' + b' = n` must be these (bitwise disjoint summands add
without carries, so `a' = n AND mask`, `b' = n AND mask'`).
-/

namespace Set

variable {α R : Type*} [One R] [Zero R] (A : Set α)

/-- A polymorphic indicator function `𝟙_A` which is `1` on `A` and `0` outside. -/
noncomputable def indicatorOne : α → R := indicator A (fun _ ↦ 1)

scoped notation "𝟙_" A:max => indicatorOne A

end Set

namespace AdditiveCombinatorics

open Finset Set

variable {R : Type*} [Semiring R]

/-- The sum convolution of two functions `f, g : ℕ → R`, also known as the Cauchy product.
`(f ∗ g) n = ∑_{a+b=n} f(a)g(b)`. -/
def sumConv (f g : ℕ → R) (n : ℕ) : R := ∑ p ∈ antidiagonal n, f p.1 * g p.2

infixl:70 " ∗ " => sumConv

end AdditiveCombinatorics

open Set AdditiveCombinatorics

/-- The naturals all of whose binary digits `1` are in even positions (including `0`). -/
def evenBitSet : Set ℕ := {a | ∀ i, a.testBit i → Even i}

/-- The naturals all of whose binary digits `1` are in odd positions (including `0`). -/
def oddBitSet : Set ℕ := {b | ∀ i, b.testBit i → Odd i}

/-- Membership in `evenBitSet` constrains nothing at bit `0`: a number has all its `1` bits in
even positions exactly when halving it puts all its `1` bits in odd positions. -/
theorem mem_evenBitSet_iff (a : ℕ) : a ∈ evenBitSet ↔ a / 2 ∈ oddBitSet := by
  simp only [evenBitSet, oddBitSet, Set.mem_ofPred_eq]
  constructor
  · intro ha i hi
    have h := ha (i + 1) (by rwa [Nat.testBit_add_one])
    simp only [Nat.even_iff, Nat.odd_iff] at h ⊢
    omega
  · intro ha i hi
    match i with
    | 0 => exact Even.zero
    | k + 1 =>
      have h := ha k (by rwa [Nat.testBit_add_one] at hi)
      simp only [Nat.even_iff, Nat.odd_iff] at h ⊢
      omega

/-- A number has all its `1` bits in odd positions exactly when it is even and halving it puts
all its `1` bits in even positions. -/
theorem mem_oddBitSet_iff (b : ℕ) : b ∈ oddBitSet ↔ b % 2 = 0 ∧ b / 2 ∈ evenBitSet := by
  simp only [evenBitSet, oddBitSet, Set.mem_ofPred_eq]
  constructor
  · intro hb
    refine ⟨?_, fun i hi => ?_⟩
    · by_contra h
      have h0 := hb 0 (by rw [Nat.testBit_zero]; simp only [decide_eq_true_eq]; omega)
      simp [Nat.odd_iff] at h0
    · have h := hb (i + 1) (by rwa [Nat.testBit_add_one])
      simp only [Nat.even_iff, Nat.odd_iff] at h ⊢
      omega
  · rintro ⟨hb0, hb⟩ i hi
    match i with
    | 0 =>
      rw [Nat.testBit_zero, decide_eq_true_eq] at hi
      omega
    | k + 1 =>
      have h := hb k (by rwa [Nat.testBit_add_one] at hi)
      simp only [Nat.even_iff, Nat.odd_iff] at h ⊢
      omega

/-- Every `n` splits in exactly one way as `a + b` with all `1` bits of `a` in even positions and
all `1` bits of `b` in odd positions; and likewise with the two roles exchanged.  The two
statements are proved together because halving exchanges them. -/
theorem existsUnique_add_mem_evenBitSet_oddBitSet (n : ℕ) :
    (∃! p : ℕ × ℕ, p.1 + p.2 = n ∧ p.1 ∈ evenBitSet ∧ p.2 ∈ oddBitSet) ∧
      ∃! p : ℕ × ℕ, p.1 + p.2 = n ∧ p.1 ∈ oddBitSet ∧ p.2 ∈ evenBitSet := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0E : (0 : ℕ) ∈ evenBitSet := by simp [evenBitSet]
      have h0O : (0 : ℕ) ∈ oddBitSet := by simp [oddBitSet]
      refine ⟨⟨(0, 0), ⟨rfl, h0E, h0O⟩, ?_⟩, ⟨(0, 0), ⟨rfl, h0O, h0E⟩, ?_⟩⟩ <;>
        · rintro ⟨a, b⟩ ⟨hab, -, -⟩
          simp only [Prod.mk.injEq]
          omega
    · obtain ⟨⟨⟨x, y⟩, ⟨hxy, hx, hy⟩, huniq⟩, ⟨u, v⟩, ⟨huv, hu, hv⟩, huniq'⟩ :=
        ih (n / 2) (Nat.div_lt_self hn (by omega))
      constructor
      · refine ⟨(2 * u + n % 2, 2 * v), ⟨by omega, ?_, ?_⟩, ?_⟩
        · rw [mem_evenBitSet_iff, show (2 * u + n % 2) / 2 = u by omega]
          exact hu
        · rw [mem_oddBitSet_iff, show 2 * v / 2 = v by omega]
          exact ⟨by omega, hv⟩
        · rintro ⟨a, b⟩ ⟨hab, ha, hb⟩
          rw [mem_evenBitSet_iff] at ha
          rw [mem_oddBitSet_iff] at hb
          obtain ⟨hb0, hb2⟩ := hb
          have key := huniq' (a / 2, b / 2) ⟨by omega, ha, hb2⟩
          simp only [Prod.mk.injEq] at key ⊢
          omega
      · refine ⟨(2 * x, 2 * y + n % 2), ⟨by omega, ?_, ?_⟩, ?_⟩
        · rw [mem_oddBitSet_iff, show 2 * x / 2 = x by omega]
          exact ⟨by omega, hx⟩
        · rw [mem_evenBitSet_iff, show (2 * y + n % 2) / 2 = y by omega]
          exact hy
        · rintro ⟨a, b⟩ ⟨hab, ha, hb⟩
          rw [mem_oddBitSet_iff] at ha
          obtain ⟨ha0, ha2⟩ := ha
          rw [mem_evenBitSet_iff] at hb
          have key := huniq (a / 2, b / 2) ⟨by omega, ha2, hb⟩
          simp only [Prod.mk.injEq] at key ⊢
          omega

/-- **Erdős #1145, the page's example**: with `A` the even-binary-digit set and `B` the
odd-binary-digit set, `1_A ∗ 1_B(n) = 1` for every `n`. -/
theorem erdos_1145_evenOdd_sumConv (n : ℕ) :
    ((𝟙_evenBitSet ∗ 𝟙_oddBitSet : ℕ → ℕ) n) = 1 := by
  classical
  obtain ⟨⟨p, ⟨hpsum, hp1, hp2⟩, huniq⟩, -⟩ := existsUnique_add_mem_evenBitSet_oddBitSet n
  have hpmem : p ∈ Finset.HasAntidiagonal.antidiagonal n :=
    Finset.HasAntidiagonal.mem_antidiagonal.2 hpsum
  have hzero : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal n, q ≠ p →
      (𝟙_evenBitSet : ℕ → ℕ) q.1 * (𝟙_oddBitSet : ℕ → ℕ) q.2 = 0 := by
    intro q hq hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    by_cases h1 : q.1 ∈ evenBitSet
    · by_cases h2 : q.2 ∈ oddBitSet
      · exact absurd (huniq q ⟨hq, h1, h2⟩) hne
      · simp only [Set.indicatorOne, Set.indicator_of_notMem h2, mul_zero]
    · simp only [Set.indicatorOne, Set.indicator_of_notMem h1, zero_mul]
  have hsum : ((𝟙_evenBitSet ∗ 𝟙_oddBitSet : ℕ → ℕ) n)
      = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
        (𝟙_evenBitSet : ℕ → ℕ) q.1 * (𝟙_oddBitSet : ℕ → ℕ) q.2 := rfl
  rw [hsum, Finset.sum_eq_single_of_mem p hpmem hzero]
  simp only [Set.indicatorOne, Set.indicator_of_mem hp1, Set.indicator_of_mem hp2, mul_one]
