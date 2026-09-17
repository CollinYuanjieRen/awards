# JSP-000810: prime factors of 2ᵖ−1 exceed 2p (scoped component of Erdős #977)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000810](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000810) (Erdős Problem [#977](https://www.erdosproblems.com/977)): if `P(m)` is the greatest prime divisor of `m`, is `P(2ⁿ−1)/n → ∞`?

The full statement was proved by Stewart (2013); the page records Schinzel's (1962) bound `P(2ⁿ−1) > 2n` for `n > 12`. **The full theorem and Schinzel's all-`n` bound are not claimed here.** This package formalizes the clean order-argument special case for **prime exponents**: for every odd prime `p`, every prime factor of `2ᵖ−1` is `≡ 1 (mod 2p)`, hence `≥ 2p+1`, so `P(2ᵖ−1) ≥ 2p+1 > 2p`.

## Statement and proof

```lean
theorem two_mul_add_one_le_of_prime_dvd {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {q : ℕ} (hq : q.Prime) (hqd : q ∣ 2 ^ p - 1) : 2 * p + 1 ≤ q
theorem two_mul_add_one_le_greatestPrimeFactor {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    2 * p + 1 ≤ (2 ^ p - 1).primeFactors.max' …
```

If a prime `q` divides `2ᵖ−1` then `2ᵖ ≡ 1 (mod q)`, so the multiplicative order of `2` in the field `ZMod q` divides the prime `p`; it is not `1` (else `q ∣ 1`), hence equals `p`. By Fermat's little theorem that order divides `q−1`, so `p ∣ q−1`; and `q` is odd (it divides the odd number `2ᵖ−1`), so `2 ∣ q−1`. Since `p` is odd, `2` and `p` are coprime, giving `2p ∣ q−1`, i.e. `q ≥ 2p+1`. Applying this to the greatest prime factor gives `P(2ᵖ−1) ≥ 2p+1`.

`Challenge.lean` is a comparator-style challenge module (the same Mathlib-only target with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/977, retrieved 2026-09-17) is recorded verbatim in `sources/erdos977-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` in the built library; the only `sorry` is the statement-only target of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The order argument is classical (Schinzel 1962, for prime exponents). **Prior art:** an independent Lean formalization of Erdős #977 exists in plby/lean-proofs; this package was authored independently, without reading or copying that source. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000810-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
