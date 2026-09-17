# JSP-000432: Erdős #539, the Erdős–Szemerédi lower bound √n ≪ h(n)

This package submits, for intake and eligibility review, a Lean proof of the known lower bound in [JSP-000432](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000432) / [Erdős Problem #539](https://www.erdosproblems.com/539): let `h(n)` be maximal such that for every set `A ⊆ ℕ` of size `n` the set `{a/(a,b) : a, b ∈ A}` has size at least `h(n)`; estimate `h(n)`.

**Scope statement.** The order of `h(n)` is open (`√n ≪ h(n) ≪ e^{O(√log n)} √n`). The problem page records the Erdős–Szemerédi lower bound `n^{1/2} ≪ h(n)`. This package proves exactly that bound; the upper bounds and the order of `h(n)` are not claimed. (Public Lean proofs by KitaKen cover the disproofs of `h(n) = Θ(√n)`, `O(√n)` and `Θ(n^{2/3})`, not this lower bound.)

## Statement and proof

[Erdos539SqrtLower/Main.lean](Erdos539SqrtLower/Main.lean) copies the definitions `IsCofactorLowerBound` and `cofactorThreshold` of the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/539.lean) verbatim and proves

```lean
theorem ceil_sqrt_le_cofactorThreshold (n : ℕ) : ⌈Real.sqrt n⌉₊ ≤ cofactorThreshold n
theorem erdos_539_sq_isBigO : (fun n : ℕ ↦ √n) =O[atTop] fun n ↦ (cofactorThreshold n : ℝ)
```

the second being exactly the formal-conjectures statement `Erdos539.erdos_539.variants.sq_isBigO` (tagged "research solved" with `sorry`).

Proof. For `A` of size `n` let `I` be the set of cofactors `a/(a,b)`. The map `(a, b) ↦ (a/(a,b), b/(a,b))` sends `A × A` into `I × I` with fibres of size at most `n`: the pair is determined by `a` when `a/(a,b) ≠ 0` (then `b = (a/u)·v`), and by `b` when `a = 0`. Hence `n² ≤ n·|I|²`, so `|I| ≥ √n`, and `⌈√n⌉` is a cofactor lower bound; the set of lower bounds is bounded by `n²`, so `⌈√n⌉ ≤ h(n)`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorems as typed `example`s, checks the definition by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The bound is Erdős–Szemerédi's. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000432-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
