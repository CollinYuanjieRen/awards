# JSP-000433 / Erdős Problem #542 — scoped component: the sharpness example `{2, 3, 5}`

**Scope (honest).** Erdős asked whether `∑_{a ∈ A} 1/a ≤ 31/30` for every `A ⊆ {1, …, n}` with
`lcm(a, b) > n` for all distinct `a, b ∈ A`, and whether there must be `≫ n` integers `m ≤ n`
dividing no `a ∈ A`.  Both were **solved** by Schinzel and Szekeres (yes / no); neither theorem
is formalized here.  This package verifies the two examples recorded on the problem page
(erdosproblems.com/542): *"The first bound is best possible as A = {2,3,5} demonstrates"*, and the
second sequence `3, 4, 5, 7, 11` which Erdős, Schinzel and Szekeres conjectured to be, together
with `2, 3, 5`, the only such sequences with sum `> 1` (that conjecture is *not* claimed).

**Definition** (`Erdos542Examples/Main.lean`, namespace `Erdos542`; no formal-conjectures
rendering exists): `IsLcmLarge n A := A ⊆ Finset.Icc 1 n ∧ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b`.

**Statements.**  `two_three_five : IsLcmLarge 5 {2, 3, 5} ∧ ∑ a ∈ {2, 3, 5}, (1 : ℚ) / a = 31 / 30`;
`three_four_five_seven_eleven : IsLcmLarge 11 {3, 4, 5, 7, 11} ∧ ∑ … = 4699 / 4620 ∧ 1 < ∑ …`;
graded root `erdos_542_examples_closed` (their conjunction).  All facts are kernel-checked
(`decide` / `norm_num`; no `native_decide`).  This is a finite verification of the page's
examples, not new mathematics.

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos542Examples/Main.lean`, `Erdos542Examples.lean` (library root), `Audit.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `verification.txt`, this README.
