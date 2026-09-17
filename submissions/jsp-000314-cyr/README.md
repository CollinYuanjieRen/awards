# JSP-000314 / Erdős Problem #380 — scoped component: Tao's observation on bad intervals

**Scope (honest).** Erdős and Graham call an interval `[u, v]` of positive integers *bad* if the
greatest prime factor of `∏_{u ≤ m ≤ v} m` occurs with exponent greater than `1`, and ask for the
asymptotics of the number `B(x)` of `n ≤ x` lying in a bad interval.  That question is **proved**
(Tao) and is *not* formalized here.  This package proves the observation recorded on the problem
page (erdosproblems.com/380): *"Tao notes in the comments that if [u,v] is bad then it cannot
contain any primes, and hence certainly v < 2u."*

**Definitions** (`Erdos380BadIntervals/Main.lean`, namespace `Erdos380`; no formal-conjectures
rendering exists, so the definitions are ours): `intervalProd u v = ∏ m ∈ Finset.Icc u v, m`;
`P n = n.primeFactors.sup id` (largest prime factor, `0` for `n ≤ 1`);
`IsBad u v ↔ 1 ≤ u ∧ u ≤ v ∧ P (intervalProd u v) ^ 2 ∣ intervalProd u v`.

**Statements.**  `not_prime_mem_of_isBad : IsBad u v → p.Prime → ¬ (u ≤ p ∧ p ≤ v)`;
`lt_two_mul_of_isBad : IsBad u v → v < 2 * u`; graded root
`erdos_380_tao_closed : ¬ ∃ u v : ℕ, IsBad u v ∧ ((∃ p, p.Prime ∧ u ≤ p ∧ p ≤ v) ∨ 2 * u ≤ v)`.

**Proof idea (Tao).**  If a prime `q ∈ [u, v]`, the largest prime factor `p` of the product
satisfies `q ≤ p ≤ v`, so `p ∈ [u, v]`; Bertrand's postulate gives a prime in `(p, 2p]`, which
would be a larger prime factor if `2p ≤ v`, so `v < 2p` and `p` divides exactly one member of
the interval (itself), with exponent `1` — contradicting badness.  Then `v < 2u` follows from
Bertrand again.

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos380BadIntervals/Main.lean`, `Erdos380BadIntervals.lean` (library root),
`Audit.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`,
`verification.txt`, this README.
