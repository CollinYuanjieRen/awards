# JSP-000442: the lower half of R(C_k, K_n) = (k−1)(n−1)+1 (scoped component of Erdős #551)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000442](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000442) (Erdős Problem [#551](https://www.erdosproblems.com/551), Erdős–Faudree–Rousseau–Schelp): prove `R(C_k, K_n) = (k−1)(n−1)+1` for `k ≥ n ≥ 3` (except `k = n = 3`).

**The full identity is open in general** (proved only for large `k` relative to `n`: Bondy–Erdős, Nikiforov, Keevash–Long–Skokan). This package formalizes the **unconditional lower half** `(k−1)(n−1)+1 ≤ R(C_k, K_n)`, which holds for all `k, n ≥ 1` by the standard blow-up colouring. The matching upper bound is not claimed.

## Statement and proof

With `GraphRamseyProp N G H := ∀ R : SimpleGraph (Fin N), G ⊑ R ∨ H ⊑ Rᶜ` (every red/blue colouring of `K_N`, red = `R`, blue = the complement, has a red `G` or a blue `H`; `⊑` is Mathlib's graph embedding) and `graphRamsey G H := sInf {N | GraphRamseyProp N G H}` (`MerLeanExperiment/Defs.lean`), the package proves

```lean
theorem lower_bound (k n : ℕ) :
    k * n + 1 ≤ graphRamsey (cycleGraph (k + 1)) (⊤ : SimpleGraph (Fin (n + 1)))
theorem lower_bound' (k n : ℕ) (hk : 3 ≤ k) (hn : 3 ≤ n) :
    (k - 1) * (n - 1) + 1 ≤ graphRamsey (cycleGraph k) (⊤ : SimpleGraph (Fin n))
```

The witness is the blow-up colouring `blowUp` on `Fin (k) × Fin (n)`: `k` red cliques of size `n` (edges within a block), blue between blocks. It has no red `C_{k+1}` (each red component has only `n` vertices... in the shifted form: no red cycle longer than the block) and no blue `K_{n+1}` (a blue clique meets each block at most once, so has ≤ `k` vertices), so `K_{k·n}` admits a colouring with neither, giving `k·n < R(C_{k+1}, K_{n+1})`. `MerLeanExperiment/RamseyDefs.lean` and `Ramsey.lean` are an independent two-colour Ramsey toolbox establishing that `graphRamsey` is a genuine (finite) `sInf`.

`Challenge.lean` is a comparator-style challenge module (the same Mathlib-only definitions and the two targets with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/551) is recorded verbatim in `sources/erdos551-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of `lower_bound` and `lower_bound'`: `[propext, Classical.choice, Quot.sound]`. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` in the built library; the only `sorry`s are the two statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution and submission status

The lower bound is the classical blow-up construction (Bondy–Erdős [BoEr73]). The formalization was authored independently (own Ramsey toolbox; no third-party Lean source copied), with Claude (Anthropic) assistance and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000442-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
