# JSP-000536 / Erdős Problem #661 — scoped component: Lenz's construction in `ℝ^4`

**Scope (honest).** Erdős asked whether for all large `n` there are points
`x_1, …, x_n, y_1, …, y_n ∈ ℝ^2` with `o(n / √(log n))` distinct distances `d(x_i, y_j)`; the
problem is **open** ($50) and is *not* claimed here.  This package formalizes the remark recorded
on the problem page (erdosproblems.com/661): *"In ℝ^4 Lenz observed that there are
x_1, …, x_n, y_1, …, y_n ∈ ℝ^4 such that d(x_i, y_j) = 1 for all i, j, taking the points on two
orthogonal circles."*

**Construction** (`Erdos661Lenz/Main.lean`, namespace `Erdos661`; no formal-conjectures rendering
exists, so the statement is ours, in `EuclideanSpace ℝ (Fin 4)`): `xPt n i = (cos(iπ/n),
sin(iπ/n), 0, 0) / √2` and `yPt n j = (0, 0, cos(jπ/n), sin(jπ/n)) / √2`, i.e. points on two
orthogonal circles of radius `1/√2`, with distinct angles in `[0, π)` for `0 ≤ i < n`.

**Statements.**  `dist_xPt_yPt : dist (xPt n i) (yPt n j) = 1`; `xPt_injective`, `yPt_injective`
(on `Fin n`); `xPt_ne_yPt`; and the graded root
`erdos_661_lenz (n : ℕ) : ∃ x y : Fin n → EuclideanSpace ℝ (Fin 4), Function.Injective x ∧
Function.Injective y ∧ (∀ i j, x i ≠ y j) ∧ ∀ i j, dist (x i) (y j) = 1` — for every `n`, `2n`
pairwise distinct points of `ℝ^4` with all cross distances equal to `1`.

**Proof idea.**  `d(x_i, y_j)² = (cos² + sin²)/2 + (cos² + sin²)/2 = 1`; injectivity from the
injectivity of `cos` on `[0, π]`.

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos661Lenz/Main.lean`, `Erdos661Lenz.lean` (library root), `Audit.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `verification.txt`, this README.
