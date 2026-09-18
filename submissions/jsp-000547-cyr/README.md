# JSP-000547: the sum of ratios of consecutive divisors grows for almost all n (Erdős #673)

This package submits a Lean formalization for intake and eligibility review. It concerns [JSP-000547](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000547) / [Erdős Problem #673](https://www.erdosproblems.com/673): for `n ≥ 1` let `1 = d₁ < d₂ < ⋯ < d_{τ(n)} = n` be the divisors of `n` and `G(n) = Σ_{1 ≤ i < τ(n)} dᵢ / dᵢ₊₁`; is it true that `G(n) → ∞` for almost all `n`, and can one prove an asymptotic formula for `Σ_{n ≤ X} G(n)`? The page records the problem as PROVED: the answer to the first question is yes (Erdős [Er82e] calls it trivial; Tao's observation `τ(n/m)/m ≤ G(n) ≤ τ(n)` for divisors `m > 1` of `n` shows `G` behaves like `τ`), and Erdős notes that `(1/X) Σ_{n≤X} G(n) → ∞` is easy. No asymptotic formula for `Σ_{n≤X} G(n)` is recorded on the page or in the catalog, and none is claimed here.

## Statement and proof

The consecutive divisor pairs `(dᵢ, dᵢ₊₁)` are exactly the pairs `(d, nextDiv n d)` for the divisors `d ≠ n`, where `nextDiv n d` is the least divisor of `n` exceeding `d`; so ([Erdos673Divisors/Definitions.lean](Erdos673Divisors/Definitions.lean))

```lean
noncomputable def nextDiv (n d : ℕ) : ℕ := sInf {e : ℕ | e ∣ n ∧ d < e}
noncomputable def G (n : ℕ) : ℝ := ∑ d ∈ (Nat.divisors n).erase n, (d : ℝ) / nextDiv n d
def DensityZero (S : Set ℕ) : Prop :=
  Tendsto (fun X : ℕ => (((Finset.Icc 1 X).filter (· ∈ S)).card : ℝ) / X) atTop (𝓝 0)
```

"For almost all `n`" is taken in its standard sense: for every threshold `T` the exceptional set `{n : G(n) ≤ T}` has natural density zero. [Erdos673Divisors/Main.lean](Erdos673Divisors/Main.lean) proves

```lean
theorem erdos_673 : ∀ T : ℝ, DensityZero {n : ℕ | G n ≤ T}
theorem erdos_673_closed : (∀ T : ℝ, DensityZero {n : ℕ | G n ≤ T}) ∧
    Filter.Tendsto (fun X : ℕ => (∑ n ∈ Finset.Icc 1 X, G n) / X) Filter.atTop Filter.atTop
```

together with `erdos_673_average` ([Average.lean](Erdos673Divisors/Average.lean)), the second conjunct on its own. There are no additional hypotheses, custom axioms or unproved assumptions.

**Proof outline** (`τ(n)` = number of divisors).

1. *Tao's sandwich* ([Basic.lean](Erdos673Divisors/Basic.lean)): every term of `G(n)` is in `(0, 1)`, so `G(n) ≤ τ(n)` (`G_le_card_divisors`); for `m ∣ n`, `m > 1`, every divisor `d` of `n/m` has `nextDiv n d ≤ d·m`, so the term at `d` is at least `1/m` and `τ(n/m)/m ≤ G(n)` (`card_divisors_div_le_mul_G`). Since `τ(n) ≤ 2 τ(n/p)` for a prime `p ∣ n`, this gives `τ(n)/(2p) ≤ G(n)` (`card_divisors_le_mul_G`).
2. *Many divisors* ([Basic.lean](Erdos673Divisors/Basic.lean), `two_pow_le_card_divisors`): if `ω_Q(n)` primes of a finset `Q` divide `n` then `τ(n) ≥ 2^{ω_Q(n)}` (products of subsets of those primes are distinct divisors).
3. *Second moment* ([Moments.lean](Erdos673Divisors/Moments.lean)): with `S = Σ_{p∈Q} 1/p`, counting multiples gives `Σ_{n≤X} ω_Q(n) ≥ XS − |Q|` and `Σ_{n≤X} ω_Q(n)² ≤ XS² + XS`, hence by Chebyshev at most `4X/S + 8|Q|/S` integers `n ≤ X` have `ω_Q(n) ≤ S/2` (`card_omega_le_half`). Since `Σ 1/p` diverges (Mathlib), `S` can be made arbitrarily large, so `{n : τ(n) ≤ T}` has density zero for every `T` (`densityZero_card_divisors_le`).
4. *Small prime factors* ([Density.lean](Erdos673Divisors/Density.lean)): the integers `n ≤ X` with no prime factor in `Q` number at most `(X/m + 1)·φ(m)` with `m = ∏ Q`, and `φ(m)/m = ∏_{p∈Q}(1 − 1/p) ≤ exp(−S)` (`card_no_prime_factor_le`).
5. *Assembly* ([Main.lean](Erdos673Divisors/Main.lean)): given `T` and `ε`, choose `Q` with `exp(−S) ≤ ε/3` and let `P = max Q`; an `n` with `G(n) ≤ T` either has no prime factor in `Q` (a set of density `≤ ε/3`) or has `τ(n) ≤ 2PT` by step 1 (a set of density zero). Hence `{n : G(n) ≤ T}` has density zero.
6. *Average* ([Average.lean](Erdos673Divisors/Average.lean)): for even `n = 2k`, `G(2k) ≥ τ(2k)/4 ≥ τ(k)/4`, and `Σ_{k≤Y} τ(k) = Σ_{d≤Y} ⌊Y/d⌋ ≥ Y(log(Y+1) − 1)` (harmonic-sum bound from Mathlib), so `(1/X) Σ_{n≤X} G(n) → ∞`.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The Lean toolchain is pinned in [lean-toolchain](lean-toolchain) (`leanprover/lean4:v4.34.0-rc1`); Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the root, the almost-all statement and both halves of Tao's sandwich as typed `example`s closed by the theorems, prints the definitions, and prints the axioms of the root and of six named components (the two halves, the sandwich bounds and the two density lemmas). Every declaration depends exactly on `propext`, `Classical.choice` and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide` or custom trust extension occurs anywhere in the dependency cone. [verification.txt](verification.txt) records the local build and audit of this exported package. The published prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit by the designated verifiers and do not list the accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly. Local verification used cached upstream dependencies on arm64 macOS; it is not a clean network-disabled rebuild, and no independent-checker claim is made.

There is no Formal Conjectures module for Erdős #673 at the checkout used, so no official comparator run is possible; the statement above is this package's own transcription of the page's definition of `G` and of "almost all", argued clause by clause in this README.

## Attribution and submission status

The mathematics is Erdős's ([Er82e]: it is trivial that `G(n) → ∞` for almost all `n`, and easy that `G` grows on average) with Terence Tao's observation `τ(n/m)/m ≤ G(n) ≤ τ(n)` (for divisors `m > 1`) as recorded on the problem page; the density-zero argument for `{τ(n) ≤ T}` is the standard second-moment (Turán–Kubilius-type) computation. This package formalizes established mathematics and claims no new mathematical result. Not claimed: any asymptotic formula for `Σ_{n≤X} G(n)` (the page's second question, recorded as open), and the Erdős–Tenenbaum result that `G(n)/τ(n)` has a continuous distribution function. A Lean proof of this problem by other authors is known to exist in a public repository of unknown licence; it was not consulted, and no first-formalization or priority claim is made.

The Lean code was prepared with Claude Code (Anthropic) assistance — Claude Fable 5.1 for the mathematical design and coordination, Claude Opus for the Lean implementation — and checked locally. This is a self-submission with a direct interest in the review outcome; no solver nomination, award tier, payment status or official verification status is asserted or changed.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
