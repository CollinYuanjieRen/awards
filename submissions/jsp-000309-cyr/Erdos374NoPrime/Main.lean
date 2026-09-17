import Mathlib

/-!
# Erdős Problem #374: no `D_k` contains a prime

For `m ∈ ℕ` let `F(m)` be the minimal `k ≥ 2` (if it exists) such that there are
`a₁ < ⋯ < a_k = m` with `a₁! ⋯ a_k!` a square, and let `D_k = {m : F(m) = k}`.  Erdős and Graham
asked for the growth of `|D_k ∩ {1, …, n}|` for `3 ≤ k ≤ 6` (OPEN; not addressed here).  The
problem page records, among the known facts: "no `D_k` contains a prime".  This file proves that
fact.  There is no formal-conjectures file for #374, so the definitions are ours: a set
`a₁ < ⋯ < a_k = m` is modelled as a finset `s` of naturals with `m ∈ s` and all elements
`≤ m`, and `k = #s`; `F m` is the least such `k ≥ 2` and `D k` is the set of `m` admitting such a
finset of size `k` with `F m = k`.  The other listed facts and the growth questions are not
claimed.

Proof.  If `a_k = p` is prime then `p ∣ p!` exactly once (`p! = p · (p − 1)!` and `p ∤ (p − 1)!`),
while `p ∤ aᵢ!` for `aᵢ < p`; so the exponent of `p` in `a₁! ⋯ a_k!` is `1`, which is odd, and
the product is not a square.  Hence no finset of the required form ends at a prime, so no prime
lies in any `D_k`.
-/

open scoped Nat

/-- `s` is a finite set of naturals with largest element `m` (so `s = {a₁ < ⋯ < a_k = m}`) whose
factorial product `∏_{a ∈ s} a!` is a perfect square. -/
def IsFactorialSquareSet (m : ℕ) (s : Finset ℕ) : Prop :=
  m ∈ s ∧ (∀ a ∈ s, a ≤ m) ∧ IsSquare (∏ a ∈ s, a !)

/-- `F m` is the minimal `k ≥ 2` such that some `a₁ < ⋯ < a_k = m` has `a₁! ⋯ a_k!` a square. -/
noncomputable def F (m : ℕ) : ℕ :=
  sInf {k | 2 ≤ k ∧ ∃ s : Finset ℕ, s.card = k ∧ IsFactorialSquareSet m s}

/-- `D k = {m : F(m) = k}`: the `m` admitting such a set of size `k`, with `F m = k`. -/
def D (k : ℕ) : Set ℕ :=
  {m | (∃ s : Finset ℕ, s.card = k ∧ IsFactorialSquareSet m s) ∧ F m = k}

/-- For `a < p` with `p` prime, `p` does not divide `a !`, so its `p`-adic valuation vanishes. -/
private lemma padicValNat_factorial_eq_zero_of_lt {p a : ℕ} (hp : p.Prime) (h : a < p) :
    padicValNat p (a !) = 0 := by
  refine padicValNat.eq_zero_of_not_dvd fun hdvd => ?_
  rw [hp.dvd_factorial] at hdvd
  omega

/-- The `p`-adic valuation of `p !` is exactly `1`, for `p` prime. -/
private lemma padicValNat_factorial_self {p : ℕ} (hp : p.Prime) : padicValNat p (p !) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [← Nat.mul_factorial_pred hp0, padicValNat.mul hp0 (Nat.factorial_ne_zero _),
    padicValNat_self, padicValNat_factorial_eq_zero_of_lt hp (by omega)]

/-- If `p` is prime, `p ∈ s` and every element of `s` is `≤ p`, then the `p`-adic valuation of
`∏_{a ∈ s} a !` is exactly `1`. -/
lemma padicValNat_prod_factorial_eq_one {p : ℕ} (hp : p.Prime) {s : Finset ℕ} (hmem : p ∈ s)
    (hle : ∀ a ∈ s, a ≤ p) : padicValNat p (∏ a ∈ s, a !) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have herase : padicValNat p (∏ a ∈ s.erase p, a !) = 0 := by
    refine padicValNat.eq_zero_of_not_dvd fun hdvd => ?_
    rw [Prime.dvd_finsetProd_iff hp.prime] at hdvd
    obtain ⟨a, ha, hda⟩ := hdvd
    rw [hp.dvd_factorial] at hda
    have hane : a ≠ p := (Finset.mem_erase.mp ha).1
    have := hle a (Finset.mem_erase.mp ha).2
    omega
  have hprod : (∏ a ∈ s.erase p, a !) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => Nat.factorial_ne_zero a
  rw [← Finset.mul_prod_erase s _ hmem, padicValNat.mul (Nat.factorial_ne_zero p) hprod,
    padicValNat_factorial_self hp, herase]

/-- No factorial-square set ends at a prime: the exponent of `p` in the product is exactly `1`. -/
theorem not_isFactorialSquareSet_of_prime (p : ℕ) (hp : p.Prime) (s : Finset ℕ) :
    ¬ IsFactorialSquareSet p s := by
  have : Fact p.Prime := ⟨hp⟩
  rintro ⟨hmem, hle, hsq⟩
  obtain ⟨r, hr⟩ := hsq
  have hval := padicValNat_prod_factorial_eq_one hp hmem hle
  have hne : (∏ a ∈ s, a !) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => Nat.factorial_ne_zero a
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [hr] at hne
    simp at hne
  rw [hr, padicValNat.mul hr0 hr0] at hval
  omega

/-- **Erdős #374, the page's remark**: no `D_k` contains a prime. -/
theorem erdos_374_prime_notMem_D (p k : ℕ) (hp : p.Prime) : p ∉ D k := by
  rintro ⟨⟨s, -, hs⟩, -⟩
  exact not_isFactorialSquareSet_of_prime p hp s hs

/-- The same as a closed statement (no binders), used as the graded root. -/
theorem erdos_374_closed : ¬ ∃ (p k : ℕ), p.Prime ∧ p ∈ D k := by
  rintro ⟨p, k, hp, hpk⟩
  exact erdos_374_prime_notMem_D p k hp hpk
