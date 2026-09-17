# JSP-000591: Erdős #723, Bruck–Ryser rules out projective planes of order `6` and `14`

This package submits, for intake and eligibility review, a Lean formalization of an example recorded on the page of [JSP-000591](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000591) / [Erdős Problem #723](https://www.erdosproblems.com/723): if there is a finite projective plane of order `n`, must `n` be a prime power?

**Scope statement.** The prime-power question is open and is not addressed; the Bruck–Ryser theorem itself and the `n = 10` computer search are not claimed. The problem page records the Bruck–Ryser theorem (if a projective plane of order `n` exists and `n ≡ 1` or `2 (mod 4)`, then `n` is a sum of two squares) and continues: "For example, this rules out `n = 6` or `n = 14`." This package proves the arithmetic behind that example unconditionally — `6 ≡ 2 (mod 4)`, `14 ≡ 2 (mod 4)`, and neither is a sum of two squares — and derives the exclusion of orders `6` and `14` from the Bruck–Ryser theorem stated as an **explicit hypothesis** in exactly the shape of the formal-conjectures statement `erdos_723.variants.bruck_ryser` (over Mathlib's `Configuration.ProjectivePlane`). That hypothesis is not proved here.

## Statement and proof

[Erdos723BruckRyser/Main.lean](Erdos723BruckRyser/Main.lean) proves

```lean
theorem erdos_723_six_fourteen_closed :
    (6 ≡ 2 [MOD 4] ∧ ¬ ∃ a b : ℕ, 6 = a ^ 2 + b ^ 2) ∧
      (14 ≡ 2 [MOD 4] ∧ ¬ ∃ a b : ℕ, 14 = a ^ 2 + b ^ 2)

theorem erdos_723_bruck_ryser_rules_out_six_fourteen
    (hBR : ∀ {P L : Type} [Membership P L] [Fintype P] [Fintype L] (n : ℕ)
      (pp : ProjectivePlane P L), pp.order = n →
      (n ≡ 1 [MOD 4] ∨ n ≡ 2 [MOD 4]) → ∃ a b, n = a ^ 2 + b ^ 2)
    {P L : Type} [Membership P L] [Fintype P] [Fintype L] (pp : ProjectivePlane P L) :
    pp.order ≠ 6 ∧ pp.order ≠ 14
```

Proof. The congruences are decided; a sum of two squares equal to `6` (resp. `14`) would need `a, b ≤ 2` (resp. `≤ 3`), and no such pair works. Applying the Bruck–Ryser hypothesis at `n = 6` and `n = 14` then contradicts the non-representability.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the arithmetic statement as a typed `example` and prints the axioms of both theorems (a subset of the standard `propext`, `Classical.choice`, `Quot.sound`; see [verification.txt](verification.txt)). The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the axioms used are stated explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
