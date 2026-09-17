import Mathlib

/-!
# Erdős Problem #1181: the primorial below `q(n, k)` divides `∏_{1 ≤ i ≤ k} (n + i)`

Let `q(n, k)` be the least prime not dividing `∏_{1 ≤ i ≤ k} (n + i)`.  Erdős asked whether
`q(n, log n) < (1 − c)(log n)²` for some `c > 0` and all large `n` (OPEN; not addressed here).
The problem page records: "The upper bound `q(n, log n) ≤ (1 + o(1))(log n)²` follows from
observing that the primorial of `q(n, k)` is at most `∏_{1 ≤ i ≤ k} (n + i)`."  This file proves
the observation in its precise form: every prime below `q(n, k)` divides the product (by
minimality of `q(n, k)`), so the product of the primes below `q(n, k)` — Mathlib's
`primorial (q(n, k) − 1)` — divides `∏_{1 ≤ i ≤ k} (n + i)` and is therefore at most it (the
prime `q(n, k)` itself does not divide the product, so the primorial including it need not be
bounded by the product; the page's phrase is read in this sense).  The asymptotic upper bound
`(1 + o(1))(log n)²`, which additionally needs the growth of the primorial, is not claimed.

There is no formal-conjectures statement for #1181, so the definition of `q` is ours: `q n k` is
the least prime not dividing the product (`sInf`; the set is nonempty since a prime larger than
the product does not divide it, provided `k ≥ 1` so that the product is positive).
-/

open Finset

/-- The product `∏_{1 ≤ i ≤ k} (n + i)`. -/
def intervalProd (n k : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 k, (n + i)

/-- `q(n, k)`: the least prime not dividing `∏_{1 ≤ i ≤ k} (n + i)`. -/
noncomputable def q (n k : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ ¬ p ∣ intervalProd n k}

/-- The product is positive. -/
theorem intervalProd_pos (n k : ℕ) : 0 < intervalProd n k := by
  refine Finset.prod_pos ?_
  intro i hi
  rw [Finset.mem_Icc] at hi
  omega

/-- Some prime does not divide the product (e.g. any prime larger than it). -/
theorem exists_prime_not_dvd_intervalProd (n k : ℕ) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ intervalProd n k := by
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (intervalProd n k + 1)
  refine ⟨p, hpp, fun hdvd => ?_⟩
  have := Nat.le_of_dvd (intervalProd_pos n k) hdvd
  omega

/-- `q(n, k)` is a prime not dividing the product. -/
theorem q_prime_not_dvd (n k : ℕ) : (q n k).Prime ∧ ¬ q n k ∣ intervalProd n k := by
  have hne : {p : ℕ | p.Prime ∧ ¬ p ∣ intervalProd n k}.Nonempty :=
    exists_prime_not_dvd_intervalProd n k
  exact Nat.sInf_mem hne

/-- Every prime below `q(n, k)` divides the product. -/
theorem prime_lt_q_dvd (n k p : ℕ) (hp : p.Prime) (hpq : p < q n k) : p ∣ intervalProd n k := by
  by_contra hdvd
  have hle : q n k ≤ p :=
    Nat.sInf_le (show p ∈ {p : ℕ | p.Prime ∧ ¬ p ∣ intervalProd n k} from ⟨hp, hdvd⟩)
  omega

/-- **Erdős #1181, the page's observation (divisibility form)**: the primorial of the primes
below `q(n, k)` divides `∏_{1 ≤ i ≤ k} (n + i)`. -/
theorem erdos_1181_primorial_dvd (n k : ℕ) : primorial (q n k - 1) ∣ intervalProd n k := by
  have hq2 : 2 ≤ q n k := (q_prime_not_dvd n k).1.two_le
  rw [primorial]
  refine Finset.prod_primes_dvd _ (fun a ha => ?_) (fun a ha => ?_)
  · exact (Finset.mem_filter.mp ha).2.prime
  · obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    rw [Finset.mem_range] at ha1
    exact prime_lt_q_dvd n k a ha2 (by omega)

/-- **Erdős #1181, the page's observation**: the primorial of the primes below `q(n, k)` is at
most `∏_{1 ≤ i ≤ k} (n + i)`. -/
theorem erdos_1181_primorial_le (n k : ℕ) : primorial (q n k - 1) ≤ intervalProd n k := by
  exact Nat.le_of_dvd (intervalProd_pos n k) (erdos_1181_primorial_dvd n k)

/-- Closed form of the observation. -/
theorem erdos_1181_primorial_le_closed :
    ¬ ∃ n k : ℕ, intervalProd n k < primorial (q n k - 1) := by
  rintro ⟨n, k, h⟩
  exact absurd (erdos_1181_primorial_le n k) (not_le.mpr h)
