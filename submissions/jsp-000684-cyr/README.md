# JSP-000684: the exercise φ(n) ∣ n ⟺ n = 2ᵃ3ᵇ (Erdős #828, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000684](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000684) / [Erdős Problem #828](https://www.erdosproblems.com/828): is it true that for every integer `a` there are infinitely many `n` with `φ(n) ∣ n + a` (Graham)? The component formalized here is the statement recorded on the problem page as an easy exercise, **"`φ(n) ∣ n` if and only if `n = 2ᵃ3ᵇ` for some `a, b ≥ 0`"**, in its correct form: as literally written it is false (`φ(3) = 2` does not divide `3`), and the correct statement, which is also how the formal-conjectures project records it (with `sorry`), is `φ(n) ∣ n` if and only if `n ≤ 1` or `n = 2ᵃ3ᵇ` with `a ≥ 1`, `b ≥ 0`. Graham's question and Lehmer's conjecture are **not** claimed.

## Statements

Every object is Mathlib's (`Nat.totient`, natural-number divisibility); there are no definitions of our own (namespace `Erdos828`, [Proof/Main.lean](Proof/Main.lean)):

```lean
theorem totient_dvd_iff (n : ℕ) :
    Nat.totient n ∣ n ↔ n ≤ 1 ∨ ∃ a b : ℕ, 0 < a ∧ n = 2 ^ a * 3 ^ b

theorem totient_dvd_two_pow_mul_three_pow (a b : ℕ) (ha : 0 < a) :
    Nat.totient (2 ^ a * 3 ^ b) ∣ 2 ^ a * 3 ^ b

theorem exists_eq_two_pow_mul_three_pow_of_totient_dvd (n : ℕ) (hn : 2 ≤ n)
    (h : Nat.totient n ∣ n) : ∃ a b : ℕ, 0 < a ∧ n = 2 ^ a * 3 ^ b

theorem not_totient_dvd_three_pow (b : ℕ) (hb : 0 < b) : ¬ Nat.totient (3 ^ b) ∣ 3 ^ b
```

The first theorem (data binder `n`, an equivalence) is the corrected exercise; `n = 0` and `n = 1` are the degenerate solutions. The second and third are its two directions for `n ≥ 2`; the fourth records the page's imprecision (`a = 0`, `b ≥ 1` is not a solution). There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

(⇐) `φ(2ᵃ3ᵇ) = 2ᵃ3ᵇ⁻¹` for `a, b ≥ 1` and `φ(2ᵃ) = 2ᵃ⁻¹`, both dividing `n`. (⇒) Let `n ≥ 2` with `φ(n) ∣ n` and let `P` be the set of primes dividing `n`. Mathlib's identity `φ(n)·Π_{p∈P} p = n·Π_{p∈P}(p − 1)` shows that `Π_{p∈P}(p − 1)` divides `Π_{p∈P} p`. If every prime in `P` were odd the left side would be even and the right side odd, so `2 ∈ P`. Each odd prime in `P` contributes an even factor `p − 1`, so `2^{#(P∖{2})}` divides `2·(odd)`, whence `P` has at most one odd prime `q`; then `q − 1` divides `2q` and is coprime to `q`, so `q − 1 ∣ 2` and `q = 3`. Hence `n = 2ᵃ3ᵇ` with `a ≥ 1`. Finally `φ(3ᵇ) = 2·3ᵇ⁻¹` is even while `3ᵇ` is odd.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the root theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is Graham's, recorded by Erdős (Er83) and in Guy's collection (B37). The exercise is folklore, recorded on the problem page (with the imprecision noted above). The Lean development is written from scratch in this package; the formal-conjectures statement and the fork it cites were not consulted for the proof.

This is a scoped component of a catalog record whose status is OPEN; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000684-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
