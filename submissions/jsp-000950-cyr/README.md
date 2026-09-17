# JSP-000950: Erdős #1145, the even/odd binary-digit sets have `1_A ∗ 1_B(n) = 1` for all `n`

This package submits, for intake and eligibility review, a Lean proof of the example recorded on the page of [JSP-000950](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000950) / [Erdős Problem #1145](https://www.erdosproblems.com/1145): for sets `A = {a₁ < a₂ < …}`, `B = {b₁ < b₂ < …}` of positive integers with `aₙ / bₙ → 1` and `A + B` containing all large integers, must `limsup 1_A ∗ 1_B(n) = ∞`?

**Scope statement.** The Erdős–Sárközy question is open and is not addressed. The problem page records: "Some condition relating `A` and `B` is necessary since, for example, if `A` is the set of all integers with only even binary digits and `B` is the set of all integers with only odd binary digits then `1_A ∗ 1_B(n) = 1` for all `n`." This package proves that example, with the formal-conjectures definitions `Set.indicatorOne` (`𝟙_`) and `AdditiveCombinatorics.sumConv` (`∗`) copied verbatim (the formal-conjectures rendering of #1145 uses them with `0` allowed in the sets, as here): with `A` the naturals whose binary digits `1` occur only in even positions and `B` those with `1`s only in odd positions, every `n` has exactly one representation `n = a + b` with `a ∈ A`, `b ∈ B`. The definitions of the two sets are ours.

## Statement and proof

[Erdos1145EvenOdd/Main.lean](Erdos1145EvenOdd/Main.lean) defines

```lean
def evenBitSet : Set ℕ := {a | ∀ i, a.testBit i → Even i}
def oddBitSet : Set ℕ := {b | ∀ i, b.testBit i → Odd i}
```

and proves

```lean
theorem erdos_1145_evenOdd_sumConv (n : ℕ) :
    ((𝟙_evenBitSet ∗ 𝟙_oddBitSet : ℕ → ℕ) n) = 1
```

Proof. Halving exchanges the two sets: `a ∈ A ⟺ a / 2 ∈ B`, and `b ∈ B ⟺ b` is even and `b / 2 ∈ A`. By strong induction on `n`, there is exactly one pair `(a, b)` with `a + b = n`, `a ∈ A`, `b ∈ B` (and exactly one with the roles exchanged): from the unique decomposition of `n / 2` with the roles exchanged, `(a, b) = (2u + (n mod 2), 2v)`, and any decomposition of `n` halves to one of `n / 2`. The convolution `∑_{a + b = n} 1_A(a) 1_B(b)` therefore has exactly one nonzero term, equal to `1`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks by `rfl` that `sumConv` and `indicatorOne` are the formal-conjectures definitions, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
