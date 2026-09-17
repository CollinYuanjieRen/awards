# JSP-000676 / Erdős Problem #820 — scoped component: the values `H(n)` for `1 ≤ n ≤ 10`

**Scope (honest).** Erdős defines `H(n)` as the smallest integer `l` such that there exists
`k < l` with `gcd(k^n − 1, l^n − 1) = 1`, and asks whether `H(n) = 3` infinitely often and how
`H(n)` grows; these questions are **open** and are *not* claimed here.  This package verifies the
table recorded on the problem page (erdosproblems.com/820): *"The sequence H(n) for 1 ≤ n ≤ 10
is 3, 3, 3, 6, 3, 18, 3, 6, 3, 12."*

**Definition** (`Erdos820HTable/Main.lean`, namespace `Erdos820`; no formal-conjectures
rendering exists, so the definition is ours).  `Good n l := ∃ k < l, 2 ≤ k ∧ Nat.Coprime
(k ^ n - 1) (l ^ n - 1)` and `H n := sInf {l | Good n l}`.  As on the page, `k` ranges over
`2 ≤ k < l` (with `k = 1` allowed one would get `gcd(0, l^n − 1) = l^n − 1`, which is `1` only for
`l = 2, n = 1`, giving `H(1) = 2` instead of the page's `3`).

**Statements.**  `H_eq_of_isLeast`, `H_eq_of_good_of_forall_lt` (a least good value is `H n`),
`H_table` and the graded root `erdos_820_table_closed : H 1 = 3 ∧ H 2 = 3 ∧ H 3 = 3 ∧ H 4 = 6 ∧
H 5 = 3 ∧ H 6 = 18 ∧ H 7 = 3 ∧ H 8 = 6 ∧ H 9 = 3 ∧ H 10 = 12`.

**Proof idea.**  For each `n`, a witness `k` shows `Good n m`, and a kernel-checked `decide`
over all `l < m` (with Mathlib's kernel-accelerated `Nat.gcd` and `Nat.pow`) shows no smaller
`l` is good; `IsLeast.csInf_eq` then gives `H n = m`.  All computations are kernel-checked; no
`native_decide` is used.

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos820HTable/Main.lean`, `Erdos820HTable.lean` (library root), `Audit.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `verification.txt`, this README.
