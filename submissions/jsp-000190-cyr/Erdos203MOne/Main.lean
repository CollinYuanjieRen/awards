import Mathlib

/-!
# Erdős Problem #203: the trivial answer `m = 1` to the `q₁ ⋯ q_r m + 1` variant

Erdős and Graham asked whether there is an integer `m ≥ 1` with `gcd(m, 6) = 1` such that none of
`2^k 3^ℓ m + 1` is prime (OPEN; not addressed here).  The problem page records that they "also
ask more generally about `p₁^{k₁} ⋯ p_r^{k_r} m + 1` for distinct primes `p_i`, or `q₁ ⋯ q_r m + 1`
where the `q_i` are primes congruent to `1 (mod 4)`", and then: "(Dogmachine has noted in the
comments this latter question has the trivial answer `m = 1` - perhaps some condition such as
`m` even is meant.)"  This file proves that remark: for `m = 1` and any nonempty list of primes
`q_i ≡ 1 (mod 4)` (repetitions allowed), `q₁ ⋯ q_r · 1 + 1 ≡ 2 (mod 4)` is an even number
greater than `2`, hence not prime.  The main question and the other variants are not claimed;
the formal-conjectures statement `Erdos203.erdos_203` concerns the `2^k 3^ℓ m + 1` form only.
-/

/-- A product of primes congruent to `1 (mod 4)` is congruent to `1 (mod 4)`. -/
theorem list_prod_mod_four_eq_one (l : List ℕ) (hq : ∀ q ∈ l, q.Prime ∧ q % 4 = 1) :
    l.prod % 4 = 1 := by
  induction l with
  | nil => simp
  | cons q l ih =>
    have h1 : q % 4 = 1 := (hq q (List.mem_cons_self ..)).2
    have h2 : l.prod % 4 = 1 := ih (fun x hx => hq x (List.mem_cons_of_mem _ hx))
    rw [List.prod_cons, Nat.mul_mod, h1, h2]

/-- **Erdős #203, the page's remark**: with `m = 1`, for every nonempty list of primes
`q₁, …, q_r` congruent to `1 (mod 4)`, the number `q₁ ⋯ q_r · m + 1` is not prime. -/
theorem erdos_203_variant_m_one (l : List ℕ) (hl : l ≠ [])
    (hq : ∀ q ∈ l, q.Prime ∧ q % 4 = 1) : ¬ (l.prod * 1 + 1).Prime := by
  intro hp
  have h4 := list_prod_mod_four_eq_one l hq
  obtain ⟨q, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  have hq1 := hq q (List.mem_cons_self ..)
  have hq5 : 5 ≤ q := by
    have := hq1.1.two_le
    have := hq1.2
    omega
  have hdvd : q ∣ (q :: l').prod := List.dvd_prod (List.mem_cons_self ..)
  have hpos : 0 < (q :: l').prod := by omega
  have hle : q ≤ (q :: l').prod := Nat.le_of_dvd hpos hdvd
  have h2 : 2 ∣ (q :: l').prod * 1 + 1 := by omega
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega

/-- Closed form of `erdos_203_variant_m_one`. -/
theorem erdos_203_variant_m_one_closed :
    ¬ ∃ l : List ℕ, l ≠ [] ∧ (∀ q ∈ l, q.Prime ∧ q % 4 = 1) ∧ (l.prod * 1 + 1).Prime := by
  rintro ⟨l, hl, hq, hp⟩
  exact erdos_203_variant_m_one l hl hq hp
