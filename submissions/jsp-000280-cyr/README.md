# JSP-000280: Erdős #338, Bateman's basis of order h with no restricted order

This package submits, for intake and eligibility review, a Lean proof of the classical example recorded on the page of [JSP-000280](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000280) / [Erdős Problem #338](https://www.erdosproblems.com/338): the *restricted order* of an additive basis `A` is the least `t` such that every large integer is a sum of at most `t` distinct elements of `A`; Erdős asked when it exists and whether it can be bounded in terms of the order of the basis.

**Scope statement.** The open questions, Kelly's and Hennecart's results and the Hegyvári–Hennecart–Plagne bound are not addressed. The problem page records: "Bateman has observed that for `h ≥ 3` there is a basis of order `h` with no restricted order, taking `A = {1} ∪ {x > 0 : h ∣ x}`." This package proves that observation. Formal-conjectures has no file for #338, so the definitions and statements are ours, written to match the page's wording.

## Statements and proof

[Erdos338Bateman/Main.lean](Erdos338Bateman/Main.lean) defines

```lean
def batemanSet (h : ℕ) : Set ℕ := {1} ∪ {x | 0 < x ∧ h ∣ x}

def IsBasisOfOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ l : List ℕ, (∀ x ∈ l, x ∈ A) ∧ l.length ≤ h ∧ l.sum = n

def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ S : Finset ℕ, ↑S ⊆ A ∧ S.card ≤ t ∧ ∑ x ∈ S, x = n
```

(order: every sufficiently large integer is a sum of at most `h` elements, repetitions allowed; restricted order: at most `t` distinct elements) and proves, for every `h ≥ 3`,

```lean
theorem erdos_338_bateman (h : ℕ) (hh : 3 ≤ h) :
    IsBasisOfOrder (batemanSet h) h ∧ ¬ IsBasisOfOrder (batemanSet h) (h - 1) ∧
      ∀ t, ¬ HasRestrictedOrder (batemanSet h) t
```

so that `A` is a basis of order exactly `h` and has no restricted order.

Proof. For `n ≥ h` write `n = q·h + r` with `r < h`; then `n` is `r` ones plus the multiple `q·h`, at most `r + 1 ≤ h` summands. A sum of elements of `A` is congruent modulo `h` to its number of ones, so integers `≡ h − 1 (mod h)` need `h − 1` ones and hence `h` summands: the order is not `h − 1`. A sum of *distinct* elements of `A` contains at most one `1`, so it is `≡ 0` or `1 (mod h)`; as `h ≥ 3`, the integers `≡ 2 (mod h)` are never represented, so no restricted order exists.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, unfolds the definitions by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The example is Bateman's, as recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000280-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
