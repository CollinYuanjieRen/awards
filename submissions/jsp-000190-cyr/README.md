# JSP-000190: Erdős #203, the trivial answer `m = 1` to the `q₁ ⋯ q_r m + 1` variant

This package submits, for intake and eligibility review, a Lean proof of a remark recorded on the page of [JSP-000190](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000190) / [Erdős Problem #203](https://www.erdosproblems.com/203): is there an integer `m ≥ 1` with `gcd(m, 6) = 1` such that none of `2^k 3^ℓ m + 1` is prime, for any `k, ℓ ≥ 0`?

**Scope statement.** The question itself is open and is not addressed. The problem page records that Erdős and Graham "also ask more generally about `p₁^{k₁} ⋯ p_r^{k_r} m + 1` for distinct primes `p_i`, or `q₁ ⋯ q_r m + 1` where the `q_i` are primes congruent to `1 (mod 4)`", and then: "(Dogmachine has noted in the comments this latter question has the trivial answer `m = 1` - perhaps some condition such as `m` even is meant.)" This package proves that remark: for `m = 1` and any nonempty list of primes `q_i ≡ 1 (mod 4)` (repetitions allowed), `q₁ ⋯ q_r · 1 + 1 ≡ 2 (mod 4)` is an even number greater than `2`, hence not prime. The formal-conjectures statement `Erdos203.erdos_203` concerns the `2^k 3^ℓ m + 1` form only, so the statement here is ours; the main question and the other variants are not claimed.

## Statement and proof

[Erdos203MOne/Main.lean](Erdos203MOne/Main.lean) proves

```lean
theorem erdos_203_variant_m_one (l : List ℕ) (hl : l ≠ [])
    (hq : ∀ q ∈ l, q.Prime ∧ q % 4 = 1) : ¬ (l.prod * 1 + 1).Prime

theorem erdos_203_variant_m_one_closed :
    ¬ ∃ l : List ℕ, l ≠ [] ∧ (∀ q ∈ l, q.Prime ∧ q % 4 = 1) ∧ (l.prod * 1 + 1).Prime
```

Proof. A product of primes `≡ 1 (mod 4)` is `≡ 1 (mod 4)` (induction on the list), so `q₁ ⋯ q_r + 1` is even; it is at least `6` because the list is nonempty and each `q_i ≥ 5`; an even number other than `2` is not prime.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: `propext` and `Quot.sound` only (a subset of the standard `propext`, `Classical.choice`, `Quot.sound`). [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the axioms used are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
