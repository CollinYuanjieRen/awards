# JSP-000616: the Cameron–Erdős trivial lower bound f(n) ≥ 2^⌈n/2⌉ (scoped component of Erdős #748)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000616](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000616) (Erdős Problem [#748](https://www.erdosproblems.com/748), the Cameron–Erdős conjecture): let `f(n)` count the sum-free subsets `A ⊆ {1, …, n}` (no `a = b + c` with `a, b, c ∈ A`); is `f(n) = 2^{(1+o(1))n/2}`?

The page notes: "It is trivial to see that `f(n) ≥ 2^{n/2}`, considering all subsets of `[n/2, n]`." **This package formalizes exactly that trivial lower bound.** The full conjecture and the sharp result `f(n) ≍ 2^{n/2}` (Green [Gr04], Sapozhenko [Sa03]) are the hard theorems and are **not** claimed here.

## Statement and proof

`Jsp616/SumFree.lean` defines

```lean
def SumFree (A : Finset ℕ) : Prop := ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b + c
def f (n : ℕ) : ℕ := ((Finset.Icc 1 n).powerset.filter (fun A => SumFree A)).card
```

and proves

```lean
theorem sumFree_of_subset_upper {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc (n / 2 + 1) n) : SumFree A
theorem f_ge (n : ℕ) : 2 ^ (n - n / 2) ≤ f n
theorem f_ge_two_pow_half (n : ℕ) : 2 ^ (n / 2) ≤ f n
```

Every subset of the upper interval `{⌊n/2⌋+1, …, n}` is sum-free, because any two of its elements exceed `n/2`, so their sum exceeds `n` and cannot equal any element (all `≤ n`). That interval has `⌈n/2⌉ = n − ⌊n/2⌋` elements, and its `2^{⌈n/2⌉}` subsets are all sum-free and all contained in `{1, …, n}`, so they are among those counted by `f`; hence `f(n) ≥ 2^{⌈n/2⌉} ≥ 2^{⌊n/2⌋} = 2^{n/2}`.

**A note on the interval.** The page writes the closed interval `[n/2, n]`, but that is not always sum-free: for even `n`, `n/2 + n/2 = n` is a solution of `a = b + c` with `a = n` and `b = c = n/2` all in `[n/2, n]`. The correct sum-free interval is the half-open `(n/2, n] = {⌊n/2⌋+1, …, n}`, which is what this package uses; it still has `⌈n/2⌉ ≥ ⌊n/2⌋` elements, so the bound `2^{n/2}` (and better) holds.

`Challenge.lean` is a comparator-style challenge module (the same Mathlib-only definitions and the two lower-bound targets with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/748, retrieved 2026-09-16) is recorded verbatim in `sources/erdos748-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in `lake-manifest.json`. `Audit.lean` prints the axioms of the three theorems: `[propext, Classical.choice, Quot.sound]` (the `Classical.choice` is only from the classical decidability instance used to define the counting `filter`). No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` declarations occur in the built library (`Jsp616/`, `Jsp616.lean`, `Audit.lean`); the only `sorry`s in the package are the two statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The lower bound is Cameron–Erdős's [CaEr90] (described on the page as "trivial to see"). **Prior art:** an independent Lean 4 formalization of #748 exists in the public third-party repository plby/lean-proofs (`ErdosProblems/Erdos748.lean`, proving the full conjecture); this package was authored independently, without reading or copying that source. The contribution sought is this independent formalization of the trivial lower bound, following the fleet convention for scoped components. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000616-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
