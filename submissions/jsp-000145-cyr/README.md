# JSP-000145 / Erdős Problem #143 — scoped component: well-separated sets of integers are primitive

**Scope (honest).** Erdős asked whether a countably infinite `A ⊆ (1, ∞)` with `|kx − y| ≥ 1` for
all `x ≠ y ∈ A` and integers `k ≥ 1` must be sparse (`∑ 1/(x log x) < ∞`, …); that question is
**open** ($500) and is *not* claimed here.  This package proves the remark recorded on the
problem page (erdosproblems.com/143): *"Note that if A is a set of integers then the condition
implies that A is a primitive set (that is, no element of A is divisible by any other)"* — in the
slightly stronger form that the natural numbers lying in *any* well-separated set form a
primitive set (the page's literal form, with the integrality hypothesis, is the corollary
`isPrimitive_of_integer_set`).

**Definitions** (`Erdos143Primitive/Main.lean`, namespace `Erdos143`).  `WellSeparatedSet` is
copied verbatim from the formal-conjectures file for the problem; `IsPrimitive S := ∀ a ∈ S,
∀ b ∈ S, a ≠ b → ¬ a ∣ b`.

**Statements.**  `not_mul_of_wellSeparated` (no element is a positive integer multiple of
another); `isPrimitive_of_wellSeparated (hA : WellSeparatedSet A) : IsPrimitive {n : ℕ | (n : ℝ) ∈ A}`;
`isPrimitive_of_integer_set` (the page's form); graded root `erdos_143_primitive_closed :
¬ ∃ A : Set ℝ, WellSeparatedSet A ∧ ∃ a b : ℕ, (a : ℝ) ∈ A ∧ (b : ℝ) ∈ A ∧ a ≠ b ∧ a ∣ b`.

**Proof idea.**  If `b = k a` with `k ≥ 1` then `|k a − b| = 0 < 1`, contradicting the separation
condition.  (An elementary one-line remark; this package is a faithful, kernel-checked statement
of it, not new mathematics.)

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos143Primitive/Main.lean`, `Erdos143Primitive.lean` (library root), `Audit.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `verification.txt`, this README.
