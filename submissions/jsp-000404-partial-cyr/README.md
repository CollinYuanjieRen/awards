# JSP-000404 (Erdős #504, Blumenthal / Sendov minimax angle): the unconditionally proved part

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000404](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000404) (Erdős Problem [#504](https://www.erdosproblems.com/504), Blumenthal's problem): for `n` points in the plane let `α_n` be the largest angle that is unavoidable, i.e. the supremum of all `α` such that **every** set of `n` distinct points contains three points `x, y, z` with `∠xyz ≥ α`. Determine `α_n`.

Sendov (1993/1995) announced the definitive answer. **This package does not claim the full classification.** It formalizes, from the exact definition, the entire part that is unconditionally provable, and is explicit about the part that is not (see "Scope and the open part" below).

## The definition

`MerLeanExperiment/Problem.lean` (frozen before any proof; its SHA-256 is recorded in `verification.txt`) defines, on `Plane := EuclideanSpace ℝ (Fin 2)` with Mathlib's `EuclideanGeometry.angle`:

```lean
def RealizableCap (n : ℕ) (bound : ℝ) : Prop :=
  ∃ points : Fin n → Plane, Function.Injective points ∧
    ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k → EuclideanGeometry.angle (points i) (points j) (points k) ≤ bound
noncomputable def minimaxAngle (n : ℕ) : ℝ := sInf {bound : ℝ | RealizableCap n bound}
```

`minimaxAngle n` is exactly Blumenthal's `α_n`: `RealizableCap n bound` says some `n`-point configuration keeps every angle `≤ bound`, and the infimum of such bounds is the smallest max-angle any configuration can achieve, which equals the largest unavoidable angle.

## What is proved

`MerLeanExperiment/SendovPartial.lean` proves

```lean
theorem sendov_partial :
    (minimaxAngle 3 = Real.pi / 3 ∧ minimaxAngle 4 = Real.pi / 2) ∧
    minimaxAngle 5 = 3 * Real.pi / 5 ∧
    (∀ N : ℕ, 6 ≤ N → N ≤ 8 → minimaxAngle N = 2 * Real.pi / 3) ∧
    (∀ k : ℕ, 2 ≤ k → minimaxAngle (2 ^ k) = Real.pi * (1 - 1 / (k : ℝ))) ∧
    ((∀ m : ℕ, 2 ≤ m → ∀ n : ℕ, 2 ^ m < n → n ≤ 2 ^ m + 2 ^ (m - 2) →
        minimaxAngle n ≤ Real.pi * (1 - 2 / (2 * (m : ℝ) + 1))) ∧
     (∀ m : ℕ, 2 ≤ m → ∀ n : ℕ, 2 ^ m + 2 ^ (m - 2) < n → n ≤ 2 ^ (m + 1) →
        minimaxAngle n ≤ Real.pi * (1 - 1 / ((m : ℝ) + 1))))
```

i.e.

* the **exact** value of `α_n` for every `3 ≤ n ≤ 8` (`α_3 = π/3`, `α_4 = π/2`, `α_5 = 3π/5`, `α_6 = α_7 = α_8 = 2π/3`), both bounds proved;
* the **exact** value at every dyadic endpoint `n = 2^k`, `k ≥ 2` (`α_{2^k} = π(1 − 1/k)`), both bounds proved — this is the Erdős–Szekeres value;
* both of Sendov's **construction (upper) bounds** `α_n ≤ …`, for **every** `m ≥ 2`, over the two exact intervals `2^m < n ≤ 2^m + 2^{m-2}` and `2^m + 2^{m-2} < n ≤ 2^{m+1}`.

Each face is proved from the geometric definition (constructions realise the caps; lower bounds argue that every configuration forces a large angle), with no numerical or decision shortcuts. The `#print axioms` of `sendov_partial` and of all five faces is `[propext, Classical.choice, Quot.sound]`.

## Scope and the open part (read carefully)

The full classification `SendovAnswer` (stated in `Problem.lean` and, for comparison, in `Challenge.lean`) additionally asserts the two **sharp lower** bounds `α_n ≥ …` for **all** `n` in the two intervals, in particular for non-dyadic `n` with `m ≥ 4`. Those are **not** proved here and are **not** claimed. The published argument for them (Sendov, *On a conjecture concerning the maximum angle …*, 1995) rests on its Lemma 4.1, whose `s ≥ 4` capacity-maximum step is asserted without a correct proof (the announced induction is not carried out, and the asserted maximum is exceeded by explicit weight profiles, e.g. `t = 15/4` gives weight `10 > 9`); we were unable to locate a complete proof in the literature. The classification is not numerically refuted and is very likely true, but its general sharp lower bound is, to our knowledge, currently unproved. This package therefore proves the unconditional part only. Details are in `evidence/` of the working repository; nothing in this package depends on the disputed step.

## A note on the constant

erdosproblems.com/504 prints the smaller-interval value as `π(1 − 1/(2p−1))`, where `p` is the page's exponent (`2^{p−1} < N ≤ 2^p`). That is a typo. Write `m = p − 1` for the exponent used here, so `2^m < N ≤ 2^{m+1}` and the two Erdős–Szekeres dyadic endpoints are `α_{2^m} = π(1 − 1/m)` and `α_{2^{m+1}} = π(1 − 1/(m+1))`. Monotonicity of `α_N` pins the smaller-interval value between these two, i.e. into `[π(1 − 1/m), π(1 − 1/(m+1))]`. The page's value `π(1 − 1/(2p−1)) = π(1 − 1/(2m+1))` lies **above** the ceiling `π(1 − 1/(m+1))` (since `1/(2m+1) < 1/(m+1)`), so it cannot be correct; the value that does lie in range is `π(1 − 2/(2m+1))`. The formalization uses this correct constant, and the upper-bound faces above prove `α_n ≤ π(1 − 2/(2m+1))` on the smaller interval.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in `lake-manifest.json`. `Audit.lean` prints the axioms of the scoped root and its faces: `[propext, Classical.choice, Quot.sound]`. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` declarations occur in the built library (`MerLeanExperiment/`, `Audit.lean`); the only `sorry` in the package is the single statement-only target of the comparator `Challenge.lean`, which also restates the full `SendovAnswer` to record precisely what is not claimed. `verification.txt` records the local build and audit of this exported package. The source statement (erdosproblems.com/504, retrieved 2026-09-16) is frozen in `sources/erdos504-statement.txt` with its SHA-256 in `verification.txt`.

## Attribution and submission status

The mathematics is Erdős–Szekeres's and Sendov's; the geometric formalization was authored in this development (no third-party Lean source was copied). The contribution sought is formalization of the unconditional part, following the fleet convention for scoped components. Prepared with Claude (Anthropic) assistance and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000404-partial-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
