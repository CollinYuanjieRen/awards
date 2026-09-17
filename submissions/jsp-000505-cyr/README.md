# JSP-000505: Erdős #624, the weaker statement `H(2^k) ≥ k + 1` for every `k ≥ 2`

This package submits, for intake and eligibility review, a Lean proof of the "weaker statement" recorded on the page of [JSP-000505](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000505) / [Erdős Problem #624](https://www.erdosproblems.com/624): let `X` be a finite set of size `n` and `H(n)` the least `m` such that some `f : 𝒫(X) → X` has `{f(A) : A ⊆ Y} = X` for every `Y ⊆ X` with `|Y| ≥ m`; prove that `H(n) − log₂ n → ∞`.

**Scope statement.** The question itself is open and is not addressed, nor are the Erdős–Hajnal bounds or Alon's stronger results quoted on the page. The page records: "Erdős said that even the weaker statement that for `n = 2^k` we have `H(n) ≥ k + 1` is open, but Alon has provided the following simple proof: by the pigeonhole principle there are `(n−1)/2` subsets `A_i` of size `2` such that `f(A_i)` is the same. Any set `Y` of size `k` containing at least `k/2` of them can have at most `2^k − ⌊k/2⌋ + 1 < 2^k = n` distinct elements in the union of the images of `f(A)` for `A ⊆ Y`." This package proves `H(2^k) ≥ k + 1` for every `k ≥ 2`, with the definitions `ExistsEventuallySurjective` and `H` copied verbatim from the formal-conjectures rendering of #624. The literal statement fails at `k = 1`, since `H(2) = 1` (also proved), so `k ≥ 2` is the optimal range. Alon's argument as recorded needs `k ≥ 4` (the displayed inequality needs `⌊k/2⌋ ≥ 2`); a simplification of it is kept for `k ≥ 4`, and the same pigeonhole idea applied to singletons and `∅` gives all `k ≥ 2`.

## Statement and proof

[Erdos624Alon/Main.lean](Erdos624Alon/Main.lean) proves, with formal-conjectures' `Erdos624.ExistsEventuallySurjective` and `Erdos624.H`,

```lean
theorem erdos_624_alon (k : ℕ) (hk : 2 ≤ k) : k + 1 ≤ H (2 ^ k)
theorem erdos_624_alon_closed : ¬ ∃ k : ℕ, 2 ≤ k ∧ H (2 ^ k) < k + 1
theorem H_two_eq_one : H 2 = 1
```

Proof. Suppose `f` covers `X` from every `k`-set `Y`. As `|𝒫(Y)| = 2^k = n`, `f` must be injective on each `𝒫(Y)`; every set of at most two elements lies in some `k`-set (as `k ≤ n`), so `a ↦ f({a})` is injective and never equals `f(∅)`, mapping `n` elements into `n − 1` values, a contradiction. Hence no threshold `m ≤ k` works; since `m = n` works (take `f(A) = min A`), the infimum defining `H(2^k)` is at least `k + 1`. (For `k ≥ 4` the file also records the route closer to the page's: two distinct `2`-subsets share their `f`-value since `C(n, 2) > n`.) For `H(2) = 1`: `f(∅) = 0`, `f(A) = 1` otherwise, works with `m = 1`, and `m = 0` fails at `Y = ∅`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks that the definitions are the formal-conjectures ones, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
