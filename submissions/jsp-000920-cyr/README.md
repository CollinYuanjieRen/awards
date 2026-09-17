# JSP-000920: an elementary mod-4 upper bound for squarefree sumsets (scoped component of Erdős #1109)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000920](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000920) (Erdős Problem [#1109](https://www.erdosproblems.com/1109), Erdős–Sárközy): let `f(N)` be the size of the largest `A ⊆ {1,…,N}` such that every `n ∈ A+A` is squarefree; estimate `f(N)`.

**The problem is open** (Erdős–Sárközy proved `log N ≪ f(N) ≪ N^{3/4} log N`, later improved by Konyagin; these asymptotic bounds are not claimed here). This package formalizes a clean **elementary structural upper bound**: any such set `A` consists of odd numbers all in a single residue class mod 4, which forces `4·|A| ≤ N + 3` (so `f(N) ≤ (N+3)/4`). This is weaker than the published `N^{3/4}` bound; it is submitted as a self-contained, fully verified elementary component, not as an improvement.

(The catalog paraphrase says "nonsquarefree"; the erdosproblems.com page says "squarefree", which is the version formalized here.)

## Statement and proof

`Jsp920/Sumset.lean` defines `SquarefreeSumset A := ∀ a ∈ A, ∀ b ∈ A, Squarefree (a + b)` (every pairwise sum, including `a + a`, is squarefree) and proves

```lean
theorem odd_of_mem {A : Finset ℕ} (h : SquarefreeSumset A) {a : ℕ} (ha : a ∈ A) : Odd a
theorem single_class_mod_four {A : Finset ℕ} (h : SquarefreeSumset A) :
    (∀ a ∈ A, a % 4 = 1) ∨ (∀ a ∈ A, a % 4 = 3)
theorem card_le {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (h : SquarefreeSumset A) :
    4 * A.card ≤ N + 3
```

Each element is odd because `a + a = 2a` squarefree rules out `4 ∣ 2a`. If some element were `≡ 1` and another `≡ 3` (mod 4), their sum would be `≡ 0` (mod 4), so `4 ∣ a+b` contradicts squarefreeness; hence `A` sits in a single residue class mod 4. Within one class in `{1,…,N}`, the map `a ↦ (a−r)/4` injects `A` into an interval of length `⌊(N−r)/4⌋+1`, giving `4·|A| ≤ N+3`.

`Challenge.lean` is a comparator-style challenge module (the same Mathlib-only definition and two targets with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/1109, retrieved 2026-09-17) is recorded verbatim in `sources/erdos1109-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the three theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` in the built library; the only `sorry`s are the two statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution and submission status

The observation is elementary (the mod-4 obstruction to squarefreeness). The formalization was authored independently (no third-party Lean source; no Erdős #1109 formalization is known to exist elsewhere), with Claude (Anthropic) assistance and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000920-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
