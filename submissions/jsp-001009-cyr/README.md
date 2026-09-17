# JSP-001009: Erdős #1204, `B(k) < A(k)` for admissible sequences

This package submits, for intake and eligibility review, a Lean proof of a remark recorded on the page of [JSP-001009](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-1001-1022.md#JSP-001009) / [Erdős Problem #1204](https://www.erdosproblems.com/1204): a sequence `0 ≤ a₁ < ⋯ < a_k` is admissible if it misses at least one congruence class modulo every prime; with `A(k) = min a_k` and `B(k) = min (a₁ + ⋯ + a_k)/k`, estimate `A(k)` (is `A(k) ∼ k log k`?) and `B(k)`.

**Scope statement.** The estimates are open and are not addressed, nor are the Elliott, Davenport and Hensley–Richards bounds quoted on the page. The problem page records: "It is trivial that `B(k) < A(k)`." This package proves that remark for every `k ≥ 2`: an admissible sequence attaining `A(k)` has average strictly below its last term, since `a₁ < a_k`. For `k = 1` the sequence `(0)` is admissible and `A(1) = B(1) = 0`, so `k ≥ 2` is needed. There is no formal-conjectures statement for #1204, so the definitions are ours: a sequence of length `k` is a strictly increasing `a : Fin k → ℕ`, `A k` is the least largest term and `kB k` the least total over admissible sequences, so that `B(k) = kB k / k`.

## Statement and proof

[Erdos1204Admissible/Main.lean](Erdos1204Admissible/Main.lean) defines

```lean
def IsAdmissible {k : ℕ} (a : Fin k → ℕ) : Prop :=
  StrictMono a ∧ ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ i, a i % p ≠ r
def admissibleSeqs (k : ℕ) : Set (Fin k → ℕ) := {a | IsAdmissible a}
noncomputable def A (k : ℕ) : ℕ := sInf ((fun a : Fin k → ℕ => Finset.univ.sup a) '' admissibleSeqs k)
noncomputable def kB (k : ℕ) : ℕ := sInf ((fun a : Fin k → ℕ => ∑ i, a i) '' admissibleSeqs k)
```

and proves

```lean
theorem erdos_1204_B_lt_A (k : ℕ) (hk : 2 ≤ k) : (kB k : ℚ) / k < A k
theorem erdos_1204_B_lt_A_closed : ¬ ∃ k : ℕ, 2 ≤ k ∧ (A k : ℚ) ≤ (kB k : ℚ) / k
```

together with the existence of admissible sequences of every length (witness `a_i = 1 + i · k!`).

Proof. Admissible sequences exist, so the infimum defining `A(k)` is attained by some admissible `a` with largest term `A(k)`; the least total `kB k` is at most `∑ a_i`, and `∑ a_i < k · A(k)` because every term is at most `A(k)` and the first term is strictly smaller (`k ≥ 2`). Dividing by `k` gives `B(k) < A(k)`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
