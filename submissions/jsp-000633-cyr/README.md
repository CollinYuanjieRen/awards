# JSP-000633: Sidon subsets of sets with bounded representation function (Erdős #772)

This package submits a Lean formalization for intake and eligibility review. It answers [JSP-000633](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000633), which is [Erdős Problem #772](https://www.erdosproblems.com/772) ([Er80e], [Er84d]): let `k ≥ 1` and let `H_k(n)` be the maximal `r` such that if `A ⊂ ℕ` has `|A| = n` and `‖1_A * 1_A‖_∞ ≤ k` then `A` contains a Sidon set of size at least `r`. Is it true that `H_k(n)/n^{1/2} → ∞`? Or even `H_k(n) > n^{1/2+c}` for some constant `c > 0`? Both answers are yes: Alon and Erdős [AlEr85] proved `H_k(n) ≫_k n^{2/3}`.

## Statement and proof

[Erdos772Sidon/Main.lean](Erdos772Sidon/Main.lean) proves

```lean
theorem erdos_772 (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => (H k n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 + c : ℝ) < H k n
theorem erdos_772_closed :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ ¬ (Tendsto (fun n : ℕ => (H k n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 + c : ℝ) < H k n)
```

with the definitions of [Erdos772Sidon/Definitions.lean](Erdos772Sidon/Definitions.lean): `rep A m` is the number of ordered pairs `(a, b) ∈ A × A` with `a + b = m`, i.e. the value of the convolution `1_A * 1_A` at `m`; `RepBounded k A` says `rep A m ≤ k` for every `m`, i.e. `‖1_A * 1_A‖_∞ ≤ k`; `IsSidon S` says that `a + b = c + d` with `a, b, c, d ∈ S` forces `{a, b} = {c, d}`; and `H k n` is the largest `r ≤ n` such that every `n`-element `A ⊆ ℕ` with `RepBounded k A` contains a Sidon subset of size at least `r`. The cap `r ≤ n` makes "the maximal `r`" a genuine maximum: a Sidon subset of an `n`-element set has at most `n` elements, so no admissible `r` is lost, and when no admissible `A` of size `n` exists (under the ordered-pair reading of `1_A * 1_A` this happens for `k = 1` and `n ≥ 2`, since `a ≠ b` already gives `rep A (a + b) ≥ 2`; for `k ≥ 2` every Sidon set is admissible, so admissible sets of every size exist) the condition is vacuous and `H k n = n`, which is what "the maximal `r`" means there; without the cap Mathlib's convention `sSup ℕ = 0` would make the statement false in exactly those degenerate cases. `rep` counts ordered pairs, which is the literal value of the convolution `1_A * 1_A`; since the theorem is proved for every `k`, it also covers the unordered and distinct-summand readings (`rep_unordered ≤ rep ≤ 2 rep_unordered`, so `H` under those readings dominates `H` at `2k` or `2k + 2`). The first theorem answers both questions of the problem (the constant is `c = 1/12`); the second is its closed form. [Audit.lean](Audit.lean) restates both as typed `example`s, together with the explicit bound `H_lower`: for every `k ≥ 1` and `n` there is `s` with `n² < 6k(s+1)³` and `s ≤ 2 H_k(n)`, i.e. `H_k(n) > ((n²/6k)^{1/3} − 1)/2`.

The proof is the Alon–Erdős alteration argument, in a deterministic averaging form:

1. [Count.lean](Erdos772Sidon/Count.lean): the number of ordered quadruples `(a, b, c, d) ∈ A⁴` with `a + b = c + d` is at most `k n²` (for each `(a, b)` there are at most `k` pairs `(c, d)`), and the number of non-trivial such quadruples with a repeated entry (`a = b` or `c = d`, i.e. solutions of `x + y = 2z`) is at most `2kn`. A non-trivial quadruple has three distinct entries in the repeated case and four otherwise.
2. [Binom.lean](Erdos772Sidon/Binom.lean): the number of `s`-element subsets of `A` containing a fixed `j`-element set is at most `C(n−j, s−j)`, and `C(n−j, s−j) n^j ≤ C(n, s) s^j`.
3. [Average.lean](Erdos772Sidon/Average.lean): summing over all `s`-element subsets `S ⊆ A`, the total number of bad (non-trivial additive) quadruples inside `S` is at most `2kn C(n−3, s−3) + kn² C(n−4, s−4) ≤ C(n, s) (2k s³/n² + k s⁴/n²)`, which is at most `C(n, s) s/2` when `6k s³ ≤ n²`; so some `S` with `|S| = s` contains at most `s/2` bad quadruples.
4. [Alteration.lean](Erdos772Sidon/Alteration.lean): deleting from such an `S` the first entry of every bad quadruple leaves a Sidon set of size at least `s/2`.
5. [Bounds.lean](Erdos772Sidon/Bounds.lean): with `s` the largest integer with `6k s³ ≤ n²` this gives `H_k(n) ≥ (s+1)/2`, and since `(s+1)³ > n²/6k` both `H_k(n)/√n → ∞` and `n^{7/12} < H_k(n)` for all large `n` follow.

No numerical certificate, `decide` or `native_decide` is used.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness.

[Audit.lean](Audit.lean) prints the axioms of both theorems and of the main lemmas. Every printed declaration depends exactly on `propext`, `Classical.choice` and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide` or custom trust extension occurs anywhere in the package. [verification.txt](verification.txt) records the local build and audit of this exported package. The published prize rules (https://www.hejustinsun.com/prize/rules, v1.0, retrieved 16 September 2026; the rules are not part of this repository) require in their section 6 an offline axiom audit by the designated verifiers, list in section 7 the failure to detect placeholder or unreviewed axioms as a ground for revocation, and do not list the accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official process.

## Attribution and submission status

The theorem is due to Alon and Erdős (An application of graph theory to additive number theory, European J. Combin. 6 (1985), 201–203), and the argument formalized here is the standard sketch of their proof recorded on the problem page (a random subset of density about `n^{-1/3}` keeps `≫ n^{2/3}` elements and only `≪ n^{2/3}` non-trivial additive quadruples, which are then deleted), written for this package in a deterministic averaging form with explicit constants; their paper itself was not consulted. A Lean formalization of this problem exists in the repository plby/lean-proofs (file `src/latest/ErdosProblems/Erdos772.lean` at commit `8822f7dd`, whose header a coverage screen of that repository read to identify the problem; its proof text was not opened); that repository has no root LICENSE and its notice `src/latest/LICENSE` covers only externally sourced files, so no license grant applies to it, and it is registered as existing Lean evidence for this catalog entry in upstream [issue #19](https://github.com/TheJustinSunPrize/awards/issues/19) and [PR #40](https://github.com/TheJustinSunPrize/awards/pull/40) (third-party replay reports and a catalog-status correction, which submit no proof of their own). The present package is an independent formalization written from the mathematical argument without consulting or reusing that proof text; it is offered as a license-clean, first-party kernel-checked proof of the catalog question and does not dispute the credit recorded in those registrations. It was prepared with Claude Code (Claude Fable 5.1 planning, Claude Opus implementation) assistance. The contribution sought is a reusable kernel-checked formalization of the exact catalog question; no new mathematical discovery, first-formalization priority or entitlement to an award is claimed.

Proposed formalizer: `RECIPIENT-jsp-000633-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. This is a self-submission with a direct interest in the review outcome.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
