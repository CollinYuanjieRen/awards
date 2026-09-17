# JSP-000568: Erdős #697, existence of δ(m, α) and the trivial bound δ(m, α) < (m^α + 1)/m

This package submits, for intake and eligibility review, a Lean proof of the elementary component of [JSP-000568](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000568) / [Erdős Problem #697](https://www.erdosproblems.com/697): let `δ(m, α)` be the density of the integers divisible by some `d ≡ 1 (mod m)` with `1 < d < exp(m^α)`; Erdős asked for the threshold `β` at which `lim_{m→∞} δ(m, α)` jumps from `0` to `1`.

**Scope statement.** Hall's theorem (`β = 1/log 2`) and the two limit statements are not claimed. The problem page records: "It is trivial that `δ(m, α) < (m^α + 1)/m → 0` if `α < 1`". This package proves exactly that bound for `m ≥ 1`, together with the existence of the density `δ(m, α)` (which the formal-conjectures rendering also leaves as `sorry`).

## Statements and proof

[Erdos697TrivialBound/Main.lean](Erdos697TrivialBound/Main.lean) copies the definitions `Set.partialDensity` and `Set.HasDensity` (formal-conjectures `FormalConjecturesForMathlib/Data/Set/Density.lean`) and `Erdos697.δ` from the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/697.lean) verbatim and proves

```lean
theorem Erdos697.density_exists (m : ℕ) (α : ℝ) : ∃ δ, HasDensity
    {n : ℕ | ∃ d, d ≡ 1 [MOD m] ∧ (d : ℝ) ∈ Set.Ioo 1 (exp (m ^ α)) ∧ d ∣ n} δ

theorem erdos_697_delta_lt_succ (m : ℕ) (α : ℝ) :
    δ (m + 1) α < (((m + 1 : ℕ) : ℝ) ^ α + 1) / ((m + 1 : ℕ) : ℝ)

theorem Erdos697.erdos_697_delta_lt (m : ℕ) (hm : 1 ≤ m) (α : ℝ) : δ m α < (m ^ α + 1) / m
```

The first is exactly the formal-conjectures statement `Erdos697.density_exists`; the third is the formal-conjectures statement `erdos_697.variants.delta_lt` **with the added hypothesis `1 ≤ m`**. This deviation is necessary: for `m = 0` the set is empty (`d ≡ 1 [MOD 0]` forces `d = 1 ∉ (1, exp(0^α))`), so `δ 0 α = 0`, while Lean's right-hand side `(0^α + 1) / 0` is `0`, and the strict inequality fails. The file also states the bound in a closed form (`¬ ∃ m α, … ≤ δ (m + 1) α`) used by our internal audit tooling.

Proof. The admissible divisors form a finite set `D`, so the set of integers with a divisor in `D` is periodic with period `L = lcm D`, and a periodic set has natural density `|S ∩ [0, L)| / L` (an explicit `|count(b)/b − c/L| ≤ L/b` squeeze). The union bound gives `δ ≤ ∑_{d ∈ D} 1/d`; writing `d = 1 + jm` with `1 ≤ j ≤ J` and `J < exp(m^α)`, this is `< (1/m) ∑_{j ≤ J} 1/j ≤ (1 + log J)/m < (m^α + 1)/m` (Mathlib's `harmonic_le_one_add_log`).

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorems as typed `example`s, checks the definitions by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The bound is the "trivial" observation recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000568-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
