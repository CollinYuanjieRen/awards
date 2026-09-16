# JSP-000390: Erdős #479, the known cases k = 2ⁱ, k = −1, k = 0 of Graham's conjecture

This package submits, for intake and eligibility review, a Lean proof of the known cases of [JSP-000390](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000390) / [Erdős Problem #479](https://www.erdosproblems.com/479) (Graham's conjecture): is it true that for every integer `k ≠ 1` there are infinitely many `n` with `2ⁿ ≡ k (mod n)`?

**Scope statement.** The conjecture is open (for `k = 3` the least such `n` is `4700063497`). The problem page records that Graham, Lehmer and Lehmer proved it for `k = 2ⁱ` (`i ≥ 1`) and for `k = −1`, and that Tang's note "A note on Erdős Problem #479" (2025) gives proofs. This package proves exactly these cases, together with the trivial case `k = 0`. Nothing is claimed for any other `k` (Tang's note also records `k = −2` as known; it is not formalized here).

## Statement and proof

[Erdos479KnownCases/Main.lean](Erdos479KnownCases/Main.lean) uses the set `{ n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] }` of the [formal-conjectures statement `Erdos479.erdos_479`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/479.lean) verbatim and proves

```lean
theorem erdos_479_two_pow (i : ℕ) (hi : 1 ≤ i) :
    { n : ℕ | (2 : ℤ) ^ n ≡ 2 ^ i [ZMOD (n : ℤ)] }.Infinite
theorem erdos_479_neg_one : { n : ℕ | (2 : ℤ) ^ n ≡ -1 [ZMOD (n : ℤ)] }.Infinite
theorem erdos_479_zero : { n : ℕ | (2 : ℤ) ^ n ≡ 0 [ZMOD (n : ℤ)] }.Infinite

theorem erdos_479_known_cases :
    ¬ ∃ k : ℤ, (k = 0 ∨ k = -1 ∨ ∃ i : ℕ, 1 ≤ i ∧ k = 2 ^ i) ∧
      { n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] }.Finite
```

Proof. For `k = 2ⁱ` (Tang, Theorem 3.1): by Dirichlet's theorem (Mathlib's `Nat.forall_exists_prime_gt_and_modEq`) choose a prime `p > max(N, i)` with `p ≡ 1 (mod φ(i))` and put `n = ip`. Modulo `p`, `2^{ip} = (2^p)^i ≡ 2^i` by Fermat; writing `i = 2^s m` with `m` odd, `2^s ∣ 2^i` and `m ∣ 2^{i(p−1)} − 1` by Euler since `φ(m) ∣ φ(i) ∣ p − 1`; as `p`, `2^s`, `m` are pairwise coprime, `ip ∣ 2^{ip} − 2^i`, and `n = ip > N` is unbounded. For `k = −1`, `3^{m+1} ∣ 2^{3^m} + 1` by induction (`a³ + 1 = (a + 1)(a² − a + 1)`), so `n = 3^m` works; for `k = 0`, `n = 2^m` works.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorems as typed `example`s and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The results are attributed on the problem page to Graham, Lehmer and Lehmer, with proofs in Quanyu Tang's note (2025). The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000390-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
