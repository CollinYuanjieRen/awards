# JSP-000577 / Erdős Problem #708 — scoped component: Gallai's observation `g(2) = 2`

**Scope (honest).** Erdős–Surányi (1959) define `g(n)` as the least `g` such that for every set
`A ⊆ [2, ∞)` of `n` integers and every set `I` of `max A` consecutive integers there is `B ⊆ I`
with `|B| = g` and `∏_{a ∈ A} a ∣ ∏_{b ∈ B} b`.  Erdős's question whether `g(n) ≤ (2 + o(1)) n`
(the $100 problem) is **open** and is *not* claimed; neither are `g(3) ≥ 4`, `g(3) = 4`, nor the
`c_n` question.  This package formalizes the settled remark recorded on the problem page
(erdosproblems.com/708): *"Gallai was the first to consider problems of this type, and observed
that `g(2) = 2` and `g(3) ≥ 4`"* — the `g(2) = 2` part.

**Definitions** (`Erdos708Gallai/Main.lean`, namespace `Erdos708`; there is no formal-conjectures
rendering of this problem, so the definitions are ours and follow the page verbatim):

- `GoodSize n k := ∀ A : Finset ℕ, (∀ a ∈ A, 2 ≤ a) → A.card = n → ∀ N : ℕ,
  ∃ B ⊆ Finset.Ico N (N + A.sup id), B.card = k ∧ ∏ a ∈ A, a ∣ ∏ b ∈ B, b`
  (the block `Finset.Ico N (N + max A)` ranges over all sets of `max A` consecutive natural
  numbers);
- `g n := sInf {k | GoodSize n k}`.

**Statements.**  `goodSize_two_two : GoodSize 2 2`; `not_goodSize_two_one : ¬ GoodSize 2 1` and
`not_goodSize_two_zero : ¬ GoodSize 2 0` (`A = {2, 3}`, `I = {1, 2, 3}`);
`erdos_708_g_two : IsLeast {k | GoodSize 2 k} 2`; `g_two : g 2 = 2`; graded root
`erdos_708_g_two_closed : g 2 = 2 ∧ IsLeast {k | GoodSize 2 k} 2`.

**Proof idea.**  For `A = {a, b}` with `2 ≤ a < b`, a block of `b` consecutive integers contains a
multiple `y` of `b`.  If it contains a multiple of `a` different from `y`, take both.  Otherwise
`y` is a multiple of `lcm(a, b)`, and since `gcd(a, b) ≤ a < b` the block contains a second
multiple `x ≠ y` of `gcd(a, b)`; then `a b = gcd(a, b) · lcm(a, b) ∣ x y`.

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; the
source contains no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See
`verification.txt`.  Before submission the package passed MerLean Heavy's research-grade audit
(target/goal contracts, kernel evidence, definition independence, two independent audits).

**Files.** `Erdos708Gallai/Main.lean` (definitions and proofs), `Erdos708Gallai.lean` (library
root), `Audit.lean` (axiom audit and a restatement), `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain`, `.gitignore`, `verification.txt`, this README.
