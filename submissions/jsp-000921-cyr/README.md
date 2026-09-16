# JSP-000921: Erdős #1110, the base case {2, 3} — the Erdős–Lewin theorem

This package submits, for intake and eligibility review, a Lean proof of the known base case of [JSP-000921](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000921) / [Erdős Problem #1110](https://www.erdosproblems.com/1110). Erdős and Lewin (Math. Comp. 65 (1996), 837–840) call `n` *representable* with respect to coprime `p > q ≥ 2` if `n` is a sum of distinct integers of the form `p^k q^l` none of which divides another, and proved that only finitely many integers are non-representable if and only if `{p, q} = {2, 3}`.

**Scope statement.** The open question on the problem page concerns the pairs `{p, q} ≠ {2, 3}` (density of non-representable numbers; infinitely many pairwise coprime non-representable numbers). This package proves the `{2, 3}` base case only: every natural number is representable. It is a component contribution; no progress on the open question is claimed.

## Statement and proof

[ErdosLewin23/Main.lean](ErdosLewin23/Main.lean) proves `erdos_lewin_two_three`:

```lean
def Gamma (p q : ℕ) : Set ℕ := {n : ℕ | ∃ k l : ℕ, n = p ^ k * q ^ l}

def Representable (p q n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (s : Set ℕ) ⊆ Gamma p q ∧ IsAntichain (· ∣ ·) (s : Set ℕ) ∧ s.sum id = n

theorem erdos_lewin_two_three (n : ℕ) : Representable 3 2 n
```

`Representable` is the predicate of the [formal-conjectures statement of Erdős #1110](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1110.lean): a finite set `s` of numbers `3^k 2^l`, an antichain for divisibility, with `s.sum id = n`. Distinctness is automatic for a `Finset`. The proof is the induction recorded on the problem page (attributed to Jansen and others): prove the stronger claim that `n` is representable and, if `n` is even, with all summands even. For `n = 2m` double a representation of `m`; for `n` odd let `3^k` be the largest power of three at most `n`, take an all-even representation of the even remainder `n − 3^k < 2·3^k`, and adjoin `3^k`, which no even summand divides and which divides none of them.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as typed `example`s (including the unfolded predicate) and prints its axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The theorem is due to Erdős and Lewin (1996); the short inductive proof is credited on the problem page to Jansen and others. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000921-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
