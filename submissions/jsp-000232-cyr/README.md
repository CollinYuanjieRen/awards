# JSP-000232: the Stanley sequence A(1) is the set of integers with no digit 2 in base 3 (scoped component of Erdős #271)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000232](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000232) (Erdős Problem [#271](https://www.erdosproblems.com/271), Stanley sequences): "Let `A(n) = {a_0 < a_1 < ⋯}` be the sequence defined by `a_0 = 0` and `a_1 = n`, and for `k ≥ 1` define `a_{k+1}` as the least positive integer such that there is no three-term arithmetic progression in `{a_0, …, a_{k+1}}`. Can the `a_k` be explicitly determined? How fast do they grow?"

**The general question (an explicit description and the growth rate of `A(n)` for arbitrary `n`, e.g. `A(4)`) is open and is not claimed here.** The problem page records the classical answer for `n = 1` (Odlyzko–Stanley, *Some curious sequences constructed with the greedy algorithm*, Bell Laboratories memorandum, 1978; OEIS A005836): `A(1)` is the set of integers with no digit 2 in their base-3 expansion. This package formalizes exactly that statement, in the explicit form `a_k = Σ b_i 3^i` where `k = Σ b_i 2^i` (the binary expansion of `k` read in base 3), together with the resulting growth `a_k ≍ k^{log_2 3}` in the elementary form `3^{⌊log_2 k⌋} ≤ a_k < 3^{⌊log_2 k⌋ + 1}`.

## Statement and proof

`Jsp232/Defs.lean` defines the problem's sequence for every starting value `n` by the greedy rule itself:

```lean
def HasThreeAP (S : Set ℕ) : Prop :=
  ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a < b ∧ b < c ∧ a + c = 2 * b
noncomputable def greedyNext (S : Finset ℕ) (t : ℕ) : ℕ :=
  sInf {m : ℕ | t < m ∧ ¬ HasThreeAP (insert m (S : Set ℕ))}
noncomputable def stanleyState (n : ℕ) : ℕ → Finset ℕ × ℕ      -- (terms so far, last term)
  | 0 => ({0}, 0) | 1 => ({0, n}, n)
  | k + 2 => let s := stanleyState n (k + 1); let m := greedyNext s.1 s.2; (insert m s.1, m)
noncomputable def stanley (n : ℕ) (k : ℕ) : ℕ := (stanleyState n k).2
```

and proves the specification `isLeast_stanley_succ_succ : IsLeast {m | stanley n (k+1) < m ∧ ¬ HasThreeAP (insert m (stanley n '' Set.Iic (k+1)))} (stanley n (k+2))` for every `n` and `k` (the candidate set is nonempty because every prefix is AP-free), `stanley_strictMono` for `0 < n`, and the characterization `IsStanleySeq n a ↔ a = stanley n` (`Jsp232/Main.lean`), where `IsStanleySeq n a` is the Mathlib-only predicate "`a 0 = 0`, `a 1 = n`, and `a (k+2)` is the least `m > a (k+1)` with no three-term AP in `{a 0, …, a (k+1), m}`". Since `a_0 < a_1 < ⋯` in the problem statement, "least positive integer" is read as "least integer exceeding the previous term"; with `a_0 = 0` no positive integer is ever excluded by this reading.

`Jsp232/Ternary.lean` treats base-3 digits: `NoTwo m := 2 ∉ Nat.digits 3 m`; `binToTer` (defined recursively by `binToTer k = 3 · binToTer (k/2) + k % 2`, with `binToTer_eq_ofDigits : binToTer k = Nat.ofDigits 3 (Nat.digits 2 k)`) is strictly increasing with image exactly `{m | NoTwo m}`; three `NoTwo` numbers with `a + c = 2 b` satisfy `a = c` (digitwise, since `a + c` has no carries and `2b` has digits in `{0, 2}`); and for `m` with a digit 2, replacing every 2 by 0 (`dropTwo m`) and by 1 (`lowerTwo m`) gives `dropTwo m < lowerTwo m < m` with `dropTwo m + m = 2 · lowerTwo m`.

`Jsp232/Main.lean` proves by induction on `k`, using the `IsLeast` specification: the least `NoTwo` number above `binToTer (k+1)` is `binToTer (k+2)`, it is admissible because `NoTwo` numbers are AP-free, and every non-`NoTwo` candidate `m` below it is rejected by the progression `(dropTwo m, lowerTwo m, m)` whose first two terms already occur in the prefix. Main theorems:

```lean
theorem stanley_one_eq (k : ℕ) : stanley 1 k = binToTer k
theorem stanley_one_eq_ofDigits (k : ℕ) : stanley 1 k = Nat.ofDigits 3 (Nat.digits 2 k)
theorem range_stanley_one : Set.range (stanley 1) = {m : ℕ | 2 ∉ Nat.digits 3 m}
theorem stanley_one_bounds {k : ℕ} (hk : 0 < k) :
    3 ^ Nat.log 2 k ≤ stanley 1 k ∧ stanley 1 k < 3 ^ (Nat.log 2 k + 1)
theorem IsStanleySeq.one_eq {a : ℕ → ℕ} (ha : IsStanleySeq 1 a) (k : ℕ) :
    a k = Nat.ofDigits 3 (Nat.digits 2 k)
theorem IsStanleySeq.range_one {a : ℕ → ℕ} (ha : IsStanleySeq 1 a) :
    Set.range a = {m : ℕ | 2 ∉ Nat.digits 3 m}
```

Nothing else is asserted: no claim is made about `A(n)` for `n ≠ 1` (including the Odlyzko–Stanley descriptions of `A(3^k)` and `A(2·3^k)`, Moy's bound, or the conjectured dichotomy of growth rates).

`Challenge.lean` is a comparator-style challenge module (Mathlib-only definitions and the targets with `sorry`, not imported by the build) for mechanical statement comparison; its targets are instances of `IsStanleySeq.one_eq` / `IsStanleySeq.range_one` / `isStanleySeq_stanley`. The source statement (erdosproblems.com/271, retrieved 2026-09-16) is recorded verbatim in `sources/erdos271-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in `lake-manifest.json`. `Audit.lean` prints the axioms of the main theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` declarations occur in the built library (`Jsp232/`, `Jsp232.lean`, `Audit.lean`); the only `sorry`s in the package are the three statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package. Local verification used arm64 macOS and cached upstream dependencies; authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and submission status

The mathematics is classical (Odlyzko–Stanley 1978; described on the problem page as "easy to see"); the contribution sought is the formalization of this published component, following the fleet convention for scoped components of open problems. The formalization was prepared with Claude (Anthropic) assistance (design and hints by Claude Fable 5.1, Lean implementation by Claude Opus subagents) and locally checked. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000232-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
