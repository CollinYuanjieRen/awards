# JSP-000315: the growth of the counting function of highly composite numbers (Erdős #381)

This package submits a Lean formalization for intake and eligibility review. It answers
[JSP-000315](../../problems/catalog-0301-0400.md#JSP-000315), which is
[Erdős Problem #381](https://www.erdosproblems.com/381): determine the growth of `Q(x)`, the
number of highly composite numbers up to `x` (a positive integer `n` is *highly composite* when
every smaller positive integer has fewer divisors). The catalog cites Erdős [Er44] and Nicolas
[Ni71]; together they give

```
(log x)^{1+c} ≤ Q(x) ≤ (log x)^{C}       (all large x, some absolute c > 0 and C),
```

so `Q(x)` grows like a power of `log x` strictly larger than the first, and not faster than a
fixed power. The problem page (erdosproblems.com/381) asks whether `Q(x) ≫_k (log x)^k` for
every `k ≥ 1`; the answer is no, by Nicolas's upper bound (1971), which was already formalized by
Codex / GPT-5.6 Sol in
[plby/lean-proofs](https://github.com/plby/lean-proofs) (`Erdos381.not_erdos_381`,
`Erdos381.nicolasPolynomialUpperBound`). **This package formalizes the lower bound of Erdős
(1944), which had no Lean proof anywhere, and states the two-sided result.** Under the problem
page's framing the question is already settled by the upper bound alone, so the lower bound is an
addition to a settled question; under the catalog's framing ("determine the growth", citing [Er44]
and [Ni71]) both bounds are the resolution. Both readings are stated here so that reviewers can
apply whichever the catalog intends.

## Statement and proof

[Erdos381Lower.lean](Erdos381Lower.lean) proves, with plby's definitions `Erdos381.tau`
(number of divisors), `Erdos381.HighlyComposite` and `Erdos381.Q` reused verbatim,

```lean
theorem Erdos381Lower.erdos381_gap :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, HighlyComposite n →
      ∃ n' : ℕ, HighlyComposite n' ∧ n < n' ∧ (n' : ℝ) < n + n * Real.log n ^ (-c)

theorem Erdos381Lower.erdos381_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, Real.log N ^ (1 + c) ≤ (Q N : ℝ)

theorem Erdos381Lower.erdos381_two_sided :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, Real.log N ^ (1 + c) ≤ (Q N : ℝ)) ∧
      Erdos381.NicolasPolynomialUpperBound
```

(`^` with a real exponent is `Real.rpow`; `NicolasPolynomialUpperBound` is plby's statement
`∃ C : ℕ, Q =O[atTop] (log ·)^C`). These are the faces frozen, with `sorry`, in
[challenge/Target.lean](challenge/Target.lean), which nothing imports.
[Erdos381Lower/Audit.lean](Erdos381Lower/Audit.lean) prints the axioms of the roots, of every
main intermediate theorem and of the two plby theorems used; the expected output is in
[verification.txt](verification.txt): each depends on exactly `[propext, Classical.choice,
Quot.sound]`. No `sorry`, `admit`, `native_decide`, custom axiom or unsafe declaration occurs
outside the challenge file.

### Erdős's argument, as formalized

Erdős shows that for every large highly composite `n` the next highly composite number lies
below `n + n (log n)^{-c}`; the counting bound then follows by telescoping along the chain of
consecutive highly composite numbers.

* [Trial.lean](Erdos381Lower/Trial.lean): *trial numbers* `n·∏Up / ∏Dn` (raise the exponents of
  the primes in `Up`, lower those in `Dn`) and the exact divisor-count identity they satisfy.
* [Structure.lean](Erdos381Lower/Structure.lean): Erdős's Lemmas 1–3 for a large highly
  composite `n` with largest prime factor `P`: `log n / 18 < P ≤ 3 log n`; every prime in
  `(P/2, P]` has exponent exactly `1`; every prime below `4√P` has exponent at least `2`; and
  `q^{κ_q} < P^6` for every prime `q ≤ P`. The proofs are trial-number comparisons against the
  minimality of `n`, with auxiliary primes supplied by Bertrand's postulate and Mathlib's
  Chebyshev bounds. (The prime number theorem is not needed.)
* [Blocks.lean](Erdos381Lower/Blocks.lean): the primes-in-short-intervals input. Erdős invokes
  Hoheisel's theorem; here it is supplied by plby's proved `Erdos381.prime_blocks_log_error`
  (blocks of primes on both sides of `x` within a multiplicative error `x^{-1/L}`-scale, from
  `Erdos381.exists_fixedPower_prime_windows`), wrapped as `PrimeBlocks`/`FourBlocks`.
* [Dirichlet.lean](Erdos381Lower/Dirichlet.lean): the Dirichlet-approximation step
  (`Real.exists_int_int_abs_mul_sub_le`) choosing the block sizes `s, t`.
* [GapCore.lean](Erdos381Lower/GapCore.lean), [Gap.lean](Erdos381Lower/Gap.lean): the two trial
  numbers `n₁ = nV/u` and `n₂ = nU/v` of the paper; the dichotomy that one of them has more
  divisors than `n`; the size estimate `|log nᵢ − log n| ≤ n (log n)^{-c}`-scale; hence a highly
  composite number in `(n, nᵢ]`, with `c = 1/(20L)`.
* [Counting.lean](Erdos381Lower/Counting.lean): the chain of consecutive highly composite
  numbers and the telescoping bound `Q(N) ≥ (log N)^{1+c}`.

Two points where the formalization departs from the printed paper are worth stating.
The paper's dichotomy yields only `d(n₁) ≥ d(n)`, which does not by itself place a highly
composite number in `(n, n₁]`; the proof here establishes the strict inequality by an
elementary parity argument (`3^s = 2^{t+s}` is impossible). And the paper's appeals to the prime
number theorem are replaced by Chebyshev's bounds, which are in Mathlib; the one indispensable
analytic input is the short-interval prime theorem cited above, taken from plby's proved tree.

## Reproduce

```bash
cd submissions/jsp-000315-cyr
python3 fetch_pinned.py        # fetches the pinned upstream sources (see below), verifies SHA-256
lake exe cache get
lake build                     # default target: Erdos381Lower (builds its dependencies)
lake env lean Erdos381Lower/Audit.lean
```

Toolchain `leanprover/lean4:v4.33.0` ([lean-toolchain](lean-toolchain)); Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d` ([lake-manifest.json](lake-manifest.json)). The build
compiles plby's `Erdos381` closure (182 modules), the vendored `PrimeNumberTheoremAnd`
(Apache-2.0, shipped) and `BoundedGaps` from FormalPantheon (Apache-2.0, fetched and patched as
recorded in [pinned-sources.json](pinned-sources.json)); expect about 9,500 jobs.

## Upstream sources and attribution

* **Mathematics.** P. Erdős, *On highly composite numbers*, J. London Math. Soc. 19 (1944)
  130–133 (the lower bound); J.-L. Nicolas, *Répartition des nombres hautement composés de
  Ramanujan*, Canad. J. Math. 23 (1971) 116–130 (the upper bound); S. Ramanujan, *Highly
  composite numbers* (1915), for the notion. None of these is used as an assumption.
* **plby/lean-proofs**, commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` (Codex / GPT-5.6 Sol):
  the definitions `tau`, `HighlyComposite`, `Q`, the basic highly-composite lemmas (antitone
  exponents, initial segment of primes), the Hoheisel-type prime-window theorems and Nicolas's
  upper bound. That repository carries no license grant, so none of its files is redistributed
  here: `fetch_pinned.py` downloads the 182 files of the pinned closure unmodified and verifies
  each against its SHA-256 in `pinned-sources.json`. The formalization credit for everything under
  `ErdosProblems/` belongs to those authors; this submission claims only `Erdos381Lower/`.
* **PrimeNumberTheoremAnd** (Apache-2.0, shipped in place; see `LICENSES/`) and
  **frenzymath/FormalPantheon** `BoundedGaps` (Apache-2.0, fetched and patched; commit and
  per-file hashes in `pinned-sources.json`): dependencies of plby's tree, unchanged.
* **Prior submissions on this entry.** [PR #584](https://github.com/TheJustinSunPrize/awards/pull/584)
  verifies the first six highly composite numbers; [PR #477](https://github.com/TheJustinSunPrize/awards/pull/477)
  is closed. Neither contains the growth theorem. They are not disputed.

The Lean code under `Erdos381Lower/` was prepared by Collin Yuanjie Ren (@CollinYuanjieRen) with
Claude Code (Claude Fable 5.1 and Claude Opus) assistance. Code and documentation follow the
repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
