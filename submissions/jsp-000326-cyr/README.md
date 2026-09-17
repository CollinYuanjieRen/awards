# JSP-000326 / Erdős Problem #396 — scoped component: `n + 1 ∣ C(2n, n)` and the Catalan identity

**Scope (honest).** Erdős Problem #396 (Erdős–Graham, 1980) asks whether for every `k` there is an
`n` with `∏_{0 ≤ i ≤ k} (n − i) ∣ C(2n, n)`; the problem is **open** and is *not* claimed here,
nor are Pomerance's density results.  This package formalizes the settled remark recorded on the
problem page (erdosproblems.com/396): *"Erdős and Graham write that `n+1` always divides
`C(2n, n)` (indeed `C(2n, n)/(n+1)` is the `n`th Catalan number)"*.  The page's informal remark
that it is "quite rare" for `n` to divide `C(2n, n)` is not formalized.

**Statements** (`Erdos396Catalan/Main.lean`, in the page's binomial form, with Mathlib's
`catalan`, which is defined by the Catalan recursion and not by the binomial formula):

- `erdos_396_remark (n : ℕ) : n + 1 ∣ (2 * n).choose n ∧ (2 * n).choose n = (n + 1) * catalan n`
  (graded root; data binder `n`);
- `erdos_396_catalan_eq_div (n : ℕ) : catalan n = (2 * n).choose n / (n + 1)`.

**Disclosure.** The proofs are short wrappers around Mathlib's `Nat.succ_dvd_centralBinom`,
`succ_mul_catalan_eq_centralBinom`, `catalan_eq_centralBinom_div` and
`Nat.centralBinom_eq_two_mul_choose`; the contribution is the faithful, kernel-checked
statement of the page's remark in the page's own form, not new mathematics.  The
formal-conjectures rendering `Erdos396.erdos_396` states only the open main question
(with `Nat.centralBinom`), so the statement here is our own.

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; the
source contains no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See
`verification.txt`.  Before submission the package passed MerLean Heavy's research-grade audit
(target/goal contracts, kernel evidence, definition independence, two independent audits).

**Files.** `Erdos396Catalan/Main.lean` (proof), `Erdos396Catalan.lean` (library root),
`Audit.lean` (axiom audit and a restatement), `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain`, `.gitignore`, `verification.txt`, this README.
